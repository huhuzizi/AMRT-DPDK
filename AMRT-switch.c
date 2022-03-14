/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright(c) 2010-2016 Intel Corporation
 */
#include <time.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_eal.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>

#define IPH_LEN 20
#define UDPH_LEN 8
#define ETH_LEN 14
#define baseRTT 0.000050
#define trans_t 0.0000012

#define INTERVAL 0.0000012

#define DROP_THRESHOLD 1024
#define ECN_THRESHOLD 24
//#include "l3fwd_linkedQueue.h"

static volatile bool force_quit;

/* MAC updating enabled by default */
static int mac_updating = 1;

double last_time_for_AMRT[16] = {0};
double initial_time;

/* ECN marking enabled by default */
static int mark_pkt = 1;

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define MAX_PKT_BURST 64
//#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 256

/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 1024
#define RTE_TEST_TX_DESC_DEFAULT 64
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;

/* ethernet addresses of ports */
static struct rte_ether_addr l2fwd_ports_eth_addr[RTE_MAX_ETHPORTS];

/* mask of enabled ports */
static uint32_t l2fwd_enabled_port_mask = 0;

/* list of enabled ports */
static uint32_t l2fwd_dst_ports[RTE_MAX_ETHPORTS];

static unsigned int l2fwd_rx_queue_per_lcore = 1;

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16

#define RX_RING_SIZE 1024
#define TX_RING_SIZE 128
#define MAX_PORT 8
#define NUMBER_OF_MULTIQUEUE 1

struct rte_ring *rings_multi[MAX_PORT][NUMBER_OF_MULTIQUEUE];




struct lcore_queue_conf {
	unsigned n_rx_port;
	unsigned rx_port_list[MAX_RX_QUEUE_PER_LCORE];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];

static struct rte_eth_dev_tx_buffer *tx_buffer[RTE_MAX_ETHPORTS];

static struct rte_eth_conf port_conf = {
	.rxmode = {
		.split_hdr_size = 0,
	},
	.txmode = {
		.mq_mode = ETH_MQ_TX_NONE,
	},
};

struct rte_mempool * l2fwd_pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct l2fwd_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
} __rte_cache_aligned;
struct l2fwd_port_statistics port_statistics[RTE_MAX_ETHPORTS];

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 10; /* default period is 10 seconds */

/* Print out statistics on packets dropped */
static void
print_stats(void)
{
	uint64_t total_packets_dropped, total_packets_tx, total_packets_rx;
	unsigned portid;

	total_packets_dropped = 0;
	total_packets_tx = 0;
	total_packets_rx = 0;

	const char clr[] = { 27, '[', '2', 'J', '\0' };
	const char topLeft[] = { 27, '[', '1', ';', '1', 'H','\0' };

		/* Clear screen and move to top left */
	printf("%s%s", clr, topLeft);

	printf("\nPort statistics ====================================");

	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++) {
		/* skip disabled ports */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("\nStatistics for port %u ------------------------------"
			   "\nPackets sent: %24"PRIu64
			   "\nPackets received: %20"PRIu64
			   "\nPackets dropped: %21"PRIu64,
			   portid,
			   port_statistics[portid].tx,
			   port_statistics[portid].rx,
			   port_statistics[portid].dropped);

		total_packets_dropped += port_statistics[portid].dropped;
		total_packets_tx += port_statistics[portid].tx;
		total_packets_rx += port_statistics[portid].rx;
	}
	printf("\nAggregate statistics ==============================="
		   "\nTotal packets sent: %18"PRIu64
		   "\nTotal packets received: %14"PRIu64
		   "\nTotal packets dropped: %15"PRIu64,
		   total_packets_tx,
		   total_packets_rx,
		   total_packets_dropped);
	printf("\n====================================================\n");
}




//mark packet with ECN, successed=0; failed<0
static int mark_packet_with_ecn(struct rte_mbuf *pkt, int type)
{
	struct rte_ipv4_hdr *ipv4_hdr;
	uint16_t cksum;

	//ipv4_hdr=pkt->buf_addr + rte_pktmbuf_headroom(pkt) + ETH_LEN + IPH_LEN;
	ipv4_hdr=rte_pktmbuf_mtod_offset(pkt, struct rte_ipv4_hdr *,
				sizeof(struct rte_ether_hdr));

				
	if (type == 0){
		ipv4_hdr->type_of_service |=0x00;
	}else if(type == 1){
		ipv4_hdr->type_of_service |=0x01;
	}else if(type == 2){
		ipv4_hdr->type_of_service |=0x02;
	}else if(type == 3){ //for AMRT
		ipv4_hdr->type_of_service &=0x11;
	}else if(type == 4){ //for AMRT
		ipv4_hdr->type_of_service &=0x10;
	}
	
	ipv4_hdr->hdr_checksum=0;
	cksum=rte_ipv4_cksum(ipv4_hdr);
	ipv4_hdr->hdr_checksum=cksum;

	return 0;
}

//for machine
/*static int mark_packet_with_ecn(struct rte_mbuf *pkt)
{
	struct rte_ipv4_hdr *ipv4_hdr;
	uint16_t cksum;

	//pkt->packet_type=0, when using vmware
	if(RTE_ETH_IS_IPV4_HDR(pkt->packet_type))
	{
		ipv4_hdr=rte_pktmbuf_mtod_offset(pkt, struct rte_ipv4_hdr *,
				sizeof(struct rte_ether_hdr));
		if((ipv4_hdr->type_of_service & 0x03)!=0){
			ipv4_hdr->type_of_service |=0x3;
			ipv4_hdr->hdr_checksum=0;
			cksum=rte_ipv4_cksum(ipv4_hdr);
			ipv4_hdr->hdr_checksum=cksum;
		}else{
			return -2;
		}
		return 0;
	}else{
		return -1;
	}


}*/


//update the packet MAC addr
static void
l2fwd_mac_updating(struct rte_mbuf *m, unsigned dest_portid)
{
	struct rte_ether_hdr *eth;
	void *tmp;

	eth = rte_pktmbuf_mtod(m, struct rte_ether_hdr *);
	/* dst addr */
	if(dest_portid==0){
			eth->d_addr.addr_bytes[0]=0xB4;
			eth->d_addr.addr_bytes[1]=0x96;
			eth->d_addr.addr_bytes[2]=0x91;
			eth->d_addr.addr_bytes[3]=0x0F;
			eth->d_addr.addr_bytes[4]=0x82;
			eth->d_addr.addr_bytes[5]=0x50;
	}
	if(dest_portid==1){//B4:96:91:0F:80:18 // 1A
			eth->d_addr.addr_bytes[0]=0xB4;
			eth->d_addr.addr_bytes[1]=0x96;
			eth->d_addr.addr_bytes[2]=0x91;
			eth->d_addr.addr_bytes[3]=0x0F;
			eth->d_addr.addr_bytes[4]=0x80;
			eth->d_addr.addr_bytes[5]=0x18;
	}
	if(dest_portid==2){
			eth->d_addr.addr_bytes[0]=0xB4;
			eth->d_addr.addr_bytes[1]=0x96;
			eth->d_addr.addr_bytes[2]=0x91;
			eth->d_addr.addr_bytes[3]=0x0F;
			eth->d_addr.addr_bytes[4]=0x7C;
			eth->d_addr.addr_bytes[5]=0x80;
	}
	if(dest_portid==3){
			eth->d_addr.addr_bytes[0]=0xB4;
			eth->d_addr.addr_bytes[1]=0x96;
			eth->d_addr.addr_bytes[2]=0x91;
			eth->d_addr.addr_bytes[3]=0x0F;
			eth->d_addr.addr_bytes[4]=0x7C;
			eth->d_addr.addr_bytes[5]=0x9C;
	}
	if(dest_portid==4){//B4:96:91:0F:81:10 //81:12
			eth->d_addr.addr_bytes[0]=0xB4;
			eth->d_addr.addr_bytes[1]=0x96;
			eth->d_addr.addr_bytes[2]=0x91;
			eth->d_addr.addr_bytes[3]=0x0F;
			eth->d_addr.addr_bytes[4]=0x81;
			eth->d_addr.addr_bytes[5]=0x10;
	}



	/* src addr */
	rte_ether_addr_copy(&l2fwd_ports_eth_addr[dest_portid], &eth->s_addr);
}

/*get flow infomation*/
struct ipv4_5tuple {
	uint32_t ip_dst;
	uint32_t ip_src;
	uint16_t port_dst;
	uint16_t port_src;
	uint8_t  proto;
} __attribute__((__packed__));

union ipv4_5tuple_host {
	struct {
		uint8_t  pad0;
		uint8_t  proto;
		uint16_t pad1;
		uint32_t ip_src;
		uint32_t ip_dst;
		uint16_t port_src;
		uint16_t port_dst;
	};
	xmm_t xmm;
};

static rte_xmm_t mask00;
#define ALL_32_BITS 0xffffffff
#define BIT_8_TO_15 0x0000ff00

#if defined(__SSE2__)
static inline xmm_t
em_mask_key(void *key, xmm_t mask)
{
	__m128i data = _mm_loadu_si128((__m128i *)(key));

	return _mm_and_si128(data, mask);
}
#elif defined(__NEON__)
static inline xmm_t
em_mask_key(void *key, xmm_t mask)
{
	int32x4_t data = vld1q_s32((int32_t *)key);

	return vandq_s32(data, mask);
}
#elif defined(__ALTIVEC__)
static inline xmm_t
em_mask_key(void *key, xmm_t mask)
{
	xmm_t data = vec_ld(0, (xmm_t *)(key));

	return vec_and(data, mask);
}
#else
#error No vector engine (SSE, NEON, ALTIVEC) available, check your toolchain
#endif

static inline uint16_t
get_ipv4_dst_port(struct rte_mbuf *pkt, uint16_t portid)
{
	//printf("pkt->packet_type %d port %d\n",pkt->packet_type, portid);
	uint16_t dest_port=100;
	struct rte_ipv4_hdr *ipv4_hdr;
	uint32_t tcp_or_udp;
	union ipv4_5tuple_host key;
	mask00 = (rte_xmm_t){.u32 = {BIT_8_TO_15, ALL_32_BITS,
				ALL_32_BITS, ALL_32_BITS} };

	ipv4_hdr = (uint8_t *)ipv4_hdr +
		offsetof(struct rte_ipv4_hdr, time_to_live);
	
	tcp_or_udp = pkt->packet_type & (RTE_PTYPE_L4_TCP | RTE_PTYPE_L4_UDP);
	
//	if (tcp_or_udp) {

		/* Handle IPv4 headers.*/
		ipv4_hdr = rte_pktmbuf_mtod_offset(pkt, struct rte_ipv4_hdr *,
				sizeof(struct rte_ether_hdr));

		ipv4_hdr = (uint8_t *)ipv4_hdr +
			offsetof(struct rte_ipv4_hdr, time_to_live);

		/*
		 * Get 5 tuple: dst port, src port, dst IP address,
		 * src IP address and protocol.
		 */
		key.xmm = em_mask_key(ipv4_hdr, mask00.x);

		//printf("key.ip_src %d  key.ip_dst %d proto: %d port_src:%d port_dst:%d\n",key.ip_src, key.ip_dst,key.proto,key.port_src,key.port_dst);

		/*add route rule, find destination port*/

		if(key.ip_dst==RTE_IPV4(5,2,168,192)) dest_port=0;
		if(key.ip_dst==RTE_IPV4(1,2,168,192)) dest_port=1;
		if(key.ip_dst==RTE_IPV4(2,2,168,192)) dest_port=2;
		if(key.ip_dst==RTE_IPV4(8,2,168,192)) dest_port=3;
		if(key.ip_dst==RTE_IPV4(7,2,168,192)) dest_port=4;
		
		
		if(dest_port < 5){
			//printf("key.ip_src %u  key.ip_dst %u proto: %u. port %u to %u\n",key.ip_src, key.ip_dst,key.proto,portid,dest_port);
		}
		//if(key.ip_dst==RTE_IPV4(3,0,0,3)) dest_port=4;
		//if(key.ip_dst==RTE_IPV4(4,0,0,4)) dest_port=5;

		return dest_port;
}

int seq = 0;



static void
enqueue_multi_queue(int port, void** bufs,int number){
	int i,retval,queue_length,queue_size;
	unsigned dst_port = 0;
	
	//printf("number: %d\n",number);
	for (i = 0; i < number; i++){
		retval = -1;	
		//printf("enqueue dst_port: %u\n",dst_port);

		
		dst_port = get_ipv4_dst_port(bufs[i], port);
		if(dst_port==100) {rte_pktmbuf_free(bufs[i]);continue;}
		l2fwd_mac_updating(bufs[i], dst_port);
		int queue_length = rte_ring_count(rings_multi[dst_port][0]);
		//printf("port_tx %d buffer %d\n",dst_port,queue_length);
		if(queue_length <= DROP_THRESHOLD){
			if(queue_length > 1 && dst_port ==0){ //for AMRT
				mark_packet_with_ecn(bufs[i], 4);
			}
			if(queue_length >= ECN_THRESHOLD){
				//printf("port_tx %d buffer %d\n",dst_port,queue_length);
				//mark_packet_with_ecn(bufs[i], 1);
				;
			}
			retval = rte_ring_mp_enqueue(rings_multi[dst_port][0], bufs[i]);
		}else{
			printf("port_tx %d buffer overflow\n",dst_port);
		}
		
		if (retval != 0)
			//printf("enqueue error at port %d to %d\n",port,dst_port);
			rte_pktmbuf_free(bufs[i]);
		}
}
static void
dequeue_multi_queue(int port, int lcore_id){
	//polling all queue in this port
	//each fetch one packet

	int sent;
	int mark_rte;
	int i,nb_1,nb_2,queue_length=0;
	double hz = rte_get_timer_hz();
	double now = rte_rdtsc()/ (double)hz;
	struct rte_mbuf *bufs[16];
	
	for (i = 0; i < NUMBER_OF_MULTIQUEUE; i++){		
	    nb_1 = rte_ring_sc_dequeue_burst(rings_multi[port][i], (void**)bufs, 4, NULL);

	    //cur_time = rte_rdtsc();	    
		nb_2 = 0;
		
		if (nb_1 > 0 && port == 0){
			if (now - last_time_for_AMRT[lcore_id] > INTERVAL){
				mark_packet_with_ecn(bufs[0], 3);
			}else{
				mark_packet_with_ecn(bufs[0], 4);
			}
		}

		int nb=nb_1;
		while (nb_1 > 0){
			nb_2 += rte_eth_tx_burst(port, 0, &bufs[nb_2], nb_1);
			nb_1 = nb - nb_2;
			last_time_for_AMRT[lcore_id] = rte_rdtsc()/ (double)hz;
			if(nb_1 > 0){
				//printf("nb_1:%d\n",nb_1);
			}

		}
		
		while (nb_2 < nb_1){
			nb_2 = rte_eth_tx_burst(port, 0, bufs, nb_1);
		}
		
		if (nb_2){
			port_statistics[port].tx += nb_2;
			}

       

	}
}


/* main processing loop */
static void
l2fwd_main_loop(void)
{
	
	int sent;
	unsigned lcore_id;
	unsigned i, j, portid, nb_rx;
	struct lcore_queue_conf *qconf;

	//struct rte_eth_dev_tx_buffer *buffer;

	lcore_id = rte_lcore_id();
	//printf("mainloop_lcore_id %d\n",lcore_id);
	qconf = &lcore_queue_conf[lcore_id];

	/*
	if (qconf->n_rx_port == 0) {
		//RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
		return;
	}
	*/
	//RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
	portid = qconf->rx_port_list[qconf->n_rx_port-1];
	if(lcore_id % 2 ==0){
		printf("start enqueue at port %d\n",portid);
		while (!force_quit) {

			/*
			 * Read packet from RX queues
			 */
			nb_rx = rte_eth_rx_burst(portid, 0, pkts_burst, MAX_PKT_BURST);
			port_statistics[portid].rx += nb_rx;
			if(nb_rx != 0){
				enqueue_multi_queue(portid,(void **)pkts_burst,nb_rx);
					//printf("recv\n");
			}
		}
	}else{
		printf("start dequeue at port %d\n",portid);
		while (!force_quit) {	
			dequeue_multi_queue(portid, lcore_id);
		}
	}

}

static int
l2fwd_launch_one_lcore(__attribute__((unused)) void *dummy)
{
	l2fwd_main_loop();
	return 0;
}

/* display usage */
static void
l2fwd_usage(const char *prgname)
{
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
	       "  -p PORTMASK: hexadecimal bitmask of ports to configure\n"
	       "  -q NQ: number of queue (=ports) per lcore (default is 1)\n"
		   "  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 default, 86400 maximum)\n"
		   "  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by default)\n"
		   "      When enabled:\n"
		   "       - The source MAC address is replaced by the TX port MAC address\n"
		   "       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID\n",
	       prgname);
}

static int
l2fwd_parse_portmask(const char *portmask)
{
	char *end = NULL;
	unsigned long pm;

	/* parse hexadecimal string */
	pm = strtoul(portmask, &end, 16);
	if ((portmask[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;

	if (pm == 0)
		return -1;

	return pm;
}

static unsigned int
l2fwd_parse_nqueue(const char *q_arg)
{
	char *end = NULL;
	unsigned long n;

	/* parse hexadecimal string */
	n = strtoul(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return 0;
	if (n == 0)
		return 0;
	if (n >= MAX_RX_QUEUE_PER_LCORE)
		return 0;

	return n;
}

static int
l2fwd_parse_timer_period(const char *q_arg)
{
	char *end = NULL;
	int n;

	/* parse number string */
	n = strtol(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;
	if (n >= MAX_TIMER_PERIOD)
		return -1;

	return n;
}

static const char short_options[] =
	"p:"  /* portmask */
	"q:"  /* number of queues */
	"T:"  /* timer period */
	;

#define CMD_LINE_OPT_MAC_UPDATING "mac-updating"
#define CMD_LINE_OPT_NO_MAC_UPDATING "no-mac-updating"

enum {
	/* long options mapped to a short option */

	/* first long only option value must be >= 256, so that we won't
	 * conflict with short options */
	CMD_LINE_OPT_MIN_NUM = 256,
};

static const struct option lgopts[] = {
	{ CMD_LINE_OPT_MAC_UPDATING, no_argument, &mac_updating, 1},
	{ CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, &mac_updating, 0},
	{NULL, 0, 0, 0}
};

/* Parse the argument given in the command line of the application */
static int
l2fwd_parse_args(int argc, char **argv)
{
	int opt, ret, timer_secs;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;

	while ((opt = getopt_long(argc, argvopt, short_options,
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			l2fwd_enabled_port_mask = l2fwd_parse_portmask(optarg);
			if (l2fwd_enabled_port_mask == 0) {
				printf("invalid portmask\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* nqueue */
		case 'q':
			l2fwd_rx_queue_per_lcore = l2fwd_parse_nqueue(optarg);
			if (l2fwd_rx_queue_per_lcore == 0) {
				printf("invalid queue number\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* timer period */
		case 'T':
			timer_secs = l2fwd_parse_timer_period(optarg);
			if (timer_secs < 0) {
				printf("invalid timer period\n");
				l2fwd_usage(prgname);
				return -1;
			}
			timer_period = timer_secs;
			break;

		/* long options */
		case 0:
			break;

		default:
			l2fwd_usage(prgname);
			return -1;
		}
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 1; /* reset getopt lib */
	return ret;
}

/* Check the link status of all ports in up to 9s, and print them finally */
static void
check_all_ports_link_status(uint32_t port_mask)
{
#define CHECK_INTERVAL 100 /* 100ms */
#define MAX_CHECK_TIME 90 /* 9s (90 * 100ms) in total */
	uint16_t portid;
	uint8_t count, all_ports_up, print_flag = 0;
	struct rte_eth_link link;

	printf("\nChecking link status");
	fflush(stdout);
	for (count = 0; count <= MAX_CHECK_TIME; count++) {
		if (force_quit)
			return;
		all_ports_up = 1;
		RTE_ETH_FOREACH_DEV(portid) {
			if (force_quit)
				return;
			if ((port_mask & (1 << portid)) == 0)
				continue;
			memset(&link, 0, sizeof(link));
			rte_eth_link_get_nowait(portid, &link);
			/* print link status if flag set */
			if (print_flag == 1) {
				if (link.link_status)
					printf(
					"Port%d Link Up. Speed %u Mbps - %s\n",
						portid, link.link_speed,
				(link.link_duplex == ETH_LINK_FULL_DUPLEX) ?
					("full-duplex") : ("half-duplex\n"));
				else
					printf("Port %d Link Down\n", portid);
				continue;
			}
			/* clear all_ports_up flag if any link down */
			if (link.link_status == ETH_LINK_DOWN) {
				all_ports_up = 0;
				break;
			}
		}
		/* after finally printing all link status, get out */
		if (print_flag == 1)
			break;

		if (all_ports_up == 0) {
			printf(".");
			fflush(stdout);
			rte_delay_ms(CHECK_INTERVAL);
		}

		/* set the print_flag if all ports up or timeout */
		if (all_ports_up == 1 || count == (MAX_CHECK_TIME - 1)) {
			print_flag = 1;
			printf("done\n");
		}
	}
}

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}

int
main(int argc, char **argv)
{
	struct lcore_queue_conf *qconf;
	int ret;
	uint16_t nb_ports;
	uint16_t nb_ports_available = 0;
	uint16_t portid, last_port;
	unsigned lcore_id, rx_lcore_id;
	unsigned nb_ports_in_mask = 0;
	unsigned int nb_lcores = 0;
	unsigned int nb_mbufs;
	initial_time = rte_rdtsc();
	//int fd =fopen("./log_file","w");
	//rte_openlog_stream(fd);


	/* init EAL */
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid EAL arguments\n");
	argc -= ret;
	argv += ret;

	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);

	/* parse application arguments (after the EAL ones) */
	ret = l2fwd_parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");

	printf("MAC updating %s\n", mac_updating ? "enabled" : "disabled");

	/* convert to number of cycles */
	timer_period *= rte_get_timer_hz();

	nb_ports = rte_eth_dev_count_avail();
	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No Ethernet ports - bye\n");

	/* check port mask to possible port mask */
	if (l2fwd_enabled_port_mask & ~((1 << nb_ports) - 1))
		rte_exit(EXIT_FAILURE, "Invalid portmask; possible (0x%x)\n",
			(1 << nb_ports) - 1);

	/* reset l2fwd_dst_ports */
	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++)
		l2fwd_dst_ports[portid] = 0;
	last_port = 0;

	/*
	 * Each logical core is assigned a dedicated TX queue on each port.
	 */
	RTE_ETH_FOREACH_DEV(portid) {
		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		if (nb_ports_in_mask % 2) {
			l2fwd_dst_ports[portid] = last_port;
			l2fwd_dst_ports[last_port] = portid;
		}
		else
			last_port = portid;

		nb_ports_in_mask++;
	}
	if (nb_ports_in_mask % 2) {
		printf("Notice: odd number of ports in portmask.\n");
		l2fwd_dst_ports[last_port] = last_port;
	}

	rx_lcore_id = 0;
	qconf = NULL;
	//printf("yes\n");
	/* Initialize the port/queue configuration of each logical core */
	RTE_ETH_FOREACH_DEV(portid) {
		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		/* get the lcore_id for this port */
		//printf("n_rx_port %u l2fwd_rx_queue_per_lcore %u\n",lcore_queue_conf[rx_lcore_id].n_rx_port,l2fwd_rx_queue_per_lcore);
		int k=0;
		for (k=0; k<2; k++){
			while (rte_lcore_is_enabled(rx_lcore_id) == 0 ||
			       lcore_queue_conf[rx_lcore_id].n_rx_port ==
			       l2fwd_rx_queue_per_lcore) {
				rx_lcore_id++;
				if (rx_lcore_id >= RTE_MAX_LCORE)
					rte_exit(EXIT_FAILURE, "Not enough cores\n");
			}

			if (qconf != &lcore_queue_conf[rx_lcore_id]) {
				/* Assigned a new logical core in the loop above. */
				qconf = &lcore_queue_conf[rx_lcore_id];
				nb_lcores++;
			}

			qconf->rx_port_list[qconf->n_rx_port] = portid;
			//qconf->rx_port_list[qconf->n_rx_port+1] = portid;
			qconf->n_rx_port++;
			printf("Lcore %u: RX port %u\n", rx_lcore_id, portid);
		}

	}

	nb_mbufs = RTE_MAX(nb_ports * (nb_rxd + nb_txd + MAX_PKT_BURST +
		nb_lcores * MEMPOOL_CACHE_SIZE), 8192U);

	/* create the mbuf pool */
	l2fwd_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", nb_mbufs,
		MEMPOOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE,
		rte_socket_id());
	if (l2fwd_pktmbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	/* Initialise each port */
	RTE_ETH_FOREACH_DEV(portid) {
		struct rte_eth_rxconf rxq_conf;
		struct rte_eth_txconf txq_conf;
		struct rte_eth_conf local_port_conf = port_conf;
		struct rte_eth_dev_info dev_info;

		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0) {
			printf("Skipping disabled port %u\n", portid);
			continue;
		}
		nb_ports_available++;

		/* init port */
		printf("Initializing port %u... ", portid);
		fflush(stdout);
		rte_eth_dev_info_get(portid, &dev_info);
		if (dev_info.tx_offload_capa & DEV_TX_OFFLOAD_MBUF_FAST_FREE)
			local_port_conf.txmode.offloads |=
				DEV_TX_OFFLOAD_MBUF_FAST_FREE;
		ret = rte_eth_dev_configure(portid, 1, 1, &local_port_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
				  ret, portid);

		ret = rte_eth_dev_adjust_nb_rx_tx_desc(portid, &nb_rxd,
						       &nb_txd);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
				 "Cannot adjust number of descriptors: err=%d, port=%u\n",
				 ret, portid);

		rte_eth_macaddr_get(portid,&l2fwd_ports_eth_addr[portid]);

		/* init one RX queue */
		fflush(stdout);
		rxq_conf = dev_info.default_rxconf;
		rxq_conf.offloads = local_port_conf.rxmode.offloads;
		ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
					     rte_eth_dev_socket_id(portid),
					     &rxq_conf,
					     l2fwd_pktmbuf_pool);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup:err=%d, port=%u\n",
				  ret, portid);

		/* init one TX queue on each port */
		fflush(stdout);
		txq_conf = dev_info.default_txconf;
		txq_conf.offloads = local_port_conf.txmode.offloads;
		ret = rte_eth_tx_queue_setup(portid, 0, nb_txd,
				rte_eth_dev_socket_id(portid),
				&txq_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n",
				ret, portid);
		int q;
		for (q = 0; q < NUMBER_OF_MULTIQUEUE; q++){
			char name[32];
			snprintf(name, sizeof(name), "port_%u_%u-th_queue", q, portid);
			//printf("port_%u_%u-th_queue\n", q, portid);
			rings_multi[portid][q] = rte_ring_create(name, RX_RING_SIZE, rte_socket_id(),
					RING_F_SC_DEQ | RING_F_MP_RTS_ENQ);
					// RING_F_SP_ENQ 0x0001 
					// RING_F_SC_DEQ 0x0002 
					// RING_F_EXACT_SZ 0x0004
					// RTE_RING_SZ_MASK  (0x7fffffffU) 
					// RING_F_MP_RTS_ENQ 0x0008 
					// RING_F_MC_RTS_DEQ 0x0010 
					// RING_F_MP_HTS_ENQ 0x0020 
					// RING_F_MC_HTS_DEQ 0x0040 
			if (rings_multi[portid][q] == NULL)
				rte_panic("Cannot create the %u-th queue in port %u", q, portid);
		}

		/* Initialize TX buffers */
/*
		tx_buffer[portid] = rte_zmalloc_socket("tx_buffer",
				RTE_ETH_TX_BUFFER_SIZE(MAX_PKT_BURST), 0,
				rte_eth_dev_socket_id(portid));
		if (tx_buffer[portid] == NULL)
			rte_exit(EXIT_FAILURE, "Cannot allocate buffer for tx on port %u\n",
					portid);

		rte_eth_tx_buffer_init(tx_buffer[portid], MAX_PKT_BURST);

		ret = rte_eth_tx_buffer_set_err_callback(tx_buffer[portid],
				rte_eth_tx_buffer_count_callback,
				&port_statistics[portid].dropped);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
			"Cannot set error callback for tx buffer on port %u\n",
				 portid);

*/
		/* Start device */
		ret = rte_eth_dev_start(portid);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n",
				  ret, portid);

		printf("done: \n");

		rte_eth_promiscuous_enable(portid);

		printf("Port %u, MAC address: %02X:%02X:%02X:%02X:%02X:%02X\n\n",
				portid,
				l2fwd_ports_eth_addr[portid].addr_bytes[0],
				l2fwd_ports_eth_addr[portid].addr_bytes[1],
				l2fwd_ports_eth_addr[portid].addr_bytes[2],
				l2fwd_ports_eth_addr[portid].addr_bytes[3],
				l2fwd_ports_eth_addr[portid].addr_bytes[4],
				l2fwd_ports_eth_addr[portid].addr_bytes[5]);

		/* initialize port stats */
		memset(&port_statistics, 0, sizeof(port_statistics));
	}

	if (!nb_ports_available) {
		rte_exit(EXIT_FAILURE,
			"All available ports are disabled. Please set portmask.\n");
	}

	check_all_ports_link_status(l2fwd_enabled_port_mask);

	ret = 0;
	/* launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(l2fwd_launch_one_lcore, NULL, CALL_MASTER);
	RTE_LCORE_FOREACH_SLAVE(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	RTE_ETH_FOREACH_DEV(portid) {
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("Closing port %d...", portid);
		rte_eth_dev_stop(portid);
		rte_eth_dev_close(portid);
		printf(" Done\n");
	}
	printf("Bye...\n");

	return ret;
}
