// SPDX-License-Identifier: GPL-2.0
/*
 * False-sharing demo for data-type profiling, told as a TCP connection:
 * the five-tuple identity is fixed for the lifetime of the connection
 * (read-mostly), while the byte/packet counters and the congestion
 * control state change on every packet.  The layout below packs them the
 * way struct sock did before its reorg (see the LPC 2026 struct sock
 * cacheline-groups case study): the read-mostly identity shares its
 * cacheline with the rx fast-path counters, so every incoming packet
 * invalidates the line in the lookup threads' caches.
 *
 * Layout (64-byte lines, cacheline-aligned like datasym's struct):
 *
 *   cacheline 0: identity (saddr/daddr/sport/dport/state, read by the
 *		  lookup threads) + rx counters (bytes_rx/packets_rx/
 *		  rx_queue/last_ack, written per packet) -> the
 *		  false-sharing line;
 *   cacheline 1: tx + congestion control (bytes_tx/packets_tx/cwnd/
 *		  ssthresh/rtt_us/retrans, packet-path private) -> hot
 *		  writes with no contention, the true-sharing control;
 *   cacheline 2: connection config (mss/wscales/keepalive/mark/
 *		  priority, set at setup, read per packet by everybody)
 *		  -> shared reads only, stays in Shared state.
 *
 * Once the per-sample CTF stream carries type/offset/cpu/addr, a
 * 'perf mem record' of this workload lets pahole flag cacheline 0 as
 * FALSE SHARING (confirmed: same instance, distinct CPUs, at least one
 * write) while lines 1 and 2 stay silent -- and suggest grouping the
 * line-0 identity with the line-2 config it is co-accessed with.
 */
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <unistd.h>
#include <linux/compiler.h>
#include "../tests.h"

struct net_conn {
	/* cacheline 0: identity (read-mostly) + rx counters (per packet) */
	uint32_t	saddr;		/*   0 */
	uint32_t	daddr;		/*   4 */
	uint16_t	sport;		/*   8 */
	uint16_t	dport;		/*  10 */
	uint8_t		state;		/*  12: 1 == ESTABLISHED */
	uint8_t		protocol;	/*  13: 6 == TCP */
	uint16_t	__pad0;		/*  14 */
	uint64_t	bytes_rx;	/*  16: every packet */
	uint64_t	packets_rx;	/*  24: every packet */
	uint32_t	rx_queue;	/*  32: backlog depth, fluctuates */
	uint8_t		__pad1[24];	/*  36..59 */
	uint32_t	last_ack;	/*  60: written per ACK */
	/* cacheline 1: tx + congestion control (packet-path private) */
	uint64_t	bytes_tx;	/*  64: every packet */
	uint64_t	packets_tx;	/*  72: every packet */
	uint32_t	cwnd;		/*  80: on every ACK */
	uint32_t	ssthresh;	/*  84: on loss */
	uint32_t	rtt_us;		/*  88: on every ACK */
	uint32_t	retrans;	/*  92: on timeout */
	uint32_t	__pad2[8];	/*  96..127 */
	/* cacheline 2: config, set at setup, read by everybody */
	uint16_t	mss;		/* 128 */
	uint8_t		snd_wscale;	/* 130 */
	uint8_t		rcv_wscale;	/* 131 */
	uint32_t	keepalive_int;	/* 132 */
	uint32_t	mark;		/* 136: firewall mark */
	uint32_t	priority;	/* 140: traffic class */
	uint32_t	__pad3[12];	/* 144..191 */
} __attribute__((aligned(64)));

/* One shared connection, volatile so every loop iteration really loads
 * and stores instead of keeping the fields in registers.
 */
static volatile struct net_conn conn;
/* Keeps the reader checksums alive after the threads join. */
static volatile unsigned long fs_sink;

static volatile sig_atomic_t done;

struct fs_reader {
	pthread_t	thread;
	int		cpu;
	unsigned long	sum;
	char		__pad[64 - sizeof(pthread_t) - sizeof(int) - sizeof(unsigned long)];
} __attribute__((aligned(64)));

static void sighandler(int sig __maybe_unused)
{
	done = 1;
}

static void pin_to_cpu(int cpu)
{
	cpu_set_t set;

	CPU_ZERO(&set);
	CPU_SET(cpu, &set);
	/* Best effort: in a restricted cpuset this fails and the thread
	 * simply runs unpinned, with a weaker cross-CPU signal.
	 */
	pthread_setaffinity_np(pthread_self(), sizeof(set), &set);
}

/* Connection lookup, as a load balancer or 'ss' scrape would do it:
 * hash the five-tuple, then pull the config.  Reads only.
 *
 * The reads go straight to the global rather than through a local pointer:
 * this file is built -O0 (see tests/workloads/Build), so a pointer to the
 * connection would sit in a stack slot and be reloaded in front of every
 * access, a form perf's data type resolver does not track -- the reads
 * would all come out as '(unknown)' and the cross-CPU half of the false
 * sharing would never reach the profile.  A direct access is PC-relative
 * to conn, the same form the writer's stores take, and both sides resolve
 * to (struct net_conn, offset).
 */
static void *reader_fn(void *arg)
{
	struct fs_reader *r = arg;
	unsigned long sum = 0;

	pthread_setname_np(pthread_self(), "fs-reader");
	pin_to_cpu(r->cpu);

	while (!done) {
		sum += conn.saddr + conn.daddr + conn.sport + conn.dport +
		       conn.state + conn.protocol;
		sum += conn.mss + conn.snd_wscale + conn.rcv_wscale +
		       conn.keepalive_int + conn.mark + conn.priority;
	}
	r->sum = sum;
	return NULL;
}

static int false_sharing(int argc, const char **argv)
{
	int sec = 2, nreaders = 0, nr_allowed = 0, err = 1;
	int *allowed = NULL, nallowed = 0, ncpus;
	cpu_set_t set;
	struct fs_reader *readers = NULL;
	int i, writer_cpu;
	unsigned long n = 0;

	pthread_setname_np(pthread_self(), "fs-writer");
	if (argc > 0)
		sec = atoi(argv[0]);
	if (argc > 1)
		nreaders = atoi(argv[1]);

	/* A connection that just got established: identity and config
	 * fixed from here on, counters at zero.
	 */
	conn.saddr = 0x0a000001;	/* 10.0.0.1 */
	conn.daddr = 0x0a000002;	/* 10.0.0.2 */
	conn.sport = 54321;
	conn.dport = 443;
	conn.state = 1;			/* ESTABLISHED */
	conn.protocol = 6;		/* TCP */
	conn.mss = 1448;
	conn.snd_wscale = 7;
	conn.rcv_wscale = 7;
	conn.keepalive_int = 7200;
	conn.cwnd = 10;
	conn.ssthresh = 65535;
	conn.rtt_us = 50;

	/* Pin against the allowed set, not the online set, so restricted
	 * cpusets still spread the threads over distinct CPUs.
	 */
	ncpus = sysconf(_SC_NPROCESSORS_CONF);
	if (sched_getaffinity(0, sizeof(set), &set) == 0) {
		for (i = 0; i < ncpus && i < CPU_SETSIZE; i++) {
			if (!CPU_ISSET(i, &set))
				continue;
			nr_allowed++;
		}
		allowed = malloc(nr_allowed * sizeof(int));
		if (allowed == NULL) {
			fprintf(stderr, "Error: malloc failed for CPU list\n");
			return 1;
		}
		for (i = 0; i < ncpus && i < CPU_SETSIZE; i++) {
			if (CPU_ISSET(i, &set))
				allowed[nallowed++] = i;
		}
	}
	if (nreaders <= 0) {
		/* By default leave one CPU for the packet path, up to 4 readers. */
		nreaders = nallowed > 1 ? nallowed - 1 : 1;
		if (nreaders > 4)
			nreaders = 4;
	}

	signal(SIGINT, sighandler);
	signal(SIGALRM, sighandler);

	readers = calloc(nreaders, sizeof(*readers));
	if (readers == NULL) {
		fprintf(stderr, "Error: calloc failed for %d readers\n", nreaders);
		goto out;
	}
	for (i = 0; i < nreaders; i++) {
		int cpu = nallowed > 1 ? allowed[(i + 1) % nallowed] : -1;

		readers[i].cpu = cpu;
		if (pthread_create(&readers[i].thread, NULL, reader_fn, &readers[i])) {
			fprintf(stderr, "Error: failed to create reader %d\n", i);
			done = 1; // Ensure started threads terminate.
			nreaders = i;
			goto out_join;
		}
	}
	writer_cpu = nallowed > 0 ? allowed[0] : -1;
	if (nallowed == 1)
		fprintf(stderr, "Warning: single CPU allowed, no cross-CPU traffic expected\n");
	if (writer_cpu >= 0)
		pin_to_cpu(writer_cpu);

	/* The packet path: receive, acknowledge, transmit, repeat.  Every
	 * iteration dirties cacheline 0 (rx counters) and cacheline 1
	 * (tx + congestion control); every 64th packet simulates a loss
	 * (ssthresh/retrans), so those members get sampled too.
	 */
	alarm(sec);
	while (!done) {
		conn.bytes_rx += conn.mss;
		conn.packets_rx++;
		conn.rx_queue = (uint32_t)(n & 0x3f);
		conn.last_ack = (uint32_t)n;
		conn.bytes_tx += conn.mss;
		conn.packets_tx++;
		conn.cwnd = 10 + (n & 15);
		conn.rtt_us = 50 + (n & 7);
		if ((n & 63) == 0) {
			conn.ssthresh = conn.cwnd / 2;
			conn.retrans++;
		}
		n++;
	}
	err = 0;
out_join:
	for (i = 0; i < nreaders; i++) {
		if (readers[i].thread) {
			pthread_join(readers[i].thread, /*retval=*/NULL);
			fs_sink += readers[i].sum;
		}
	}
	fs_sink += (unsigned long)(conn.bytes_rx + conn.bytes_tx + n);
	free(readers);
out:
	free(allowed);
	return err;
}

DEFINE_WORKLOAD(false_sharing);
