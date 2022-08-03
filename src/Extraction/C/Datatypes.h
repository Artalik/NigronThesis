#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "vector.c"
#include "option.h"
#include "pair.h"

typedef struct Span {
    uint8_t *pos;
    uint64_t length;
} span;

typedef struct Pair {
    void* left;
    void* right;
} pair;

typedef struct List {
    void* value;
    void* next;
} list;

typedef struct Ipv4 {
    uint8_t o1;
    uint8_t o2;
    uint8_t o3;
    uint8_t o4;
} ipv4;


typedef struct Ipv6 {
    uint16_t o1;
    uint16_t o2;
    uint16_t o3;
    uint16_t o4;
    uint16_t o5;
    uint16_t o6;
    uint16_t o7;
    uint16_t o8;
} ipv6;

typedef struct RadiusAttribute {
    int key;
    union Attribute {
        struct { span v; } UserName;
        struct { span v; } UserPassword;
        struct { uint8_t n; span v; } ChapPassword;
        struct { ipv4 ip; } NasIPAddress;
        struct { uint32_t v; } NasPort;
        struct { uint32_t v; } Protocol;
        struct { ipv4 ip; } FramedIPAddress;
        struct { ipv4 ip; } FramedIPNetmask;
        struct { uint32_t v; } Routing;
        struct { span s; } FilterId;
        struct { uint32_t v; } FramedMTU;
        struct { uint32_t v; } Compression;
        struct { uint32_t v; span s; } VendorSpecific;
        struct { span s; } CalledStationId;
        struct { span s; } CallingStationId;
        struct { uint8_t n; span s; } Unknown;
        struct { uint32_t v; } Service;
    } attribute;
} radius_attribute;

DEFINE_VECTOR(radius_attribute);
DEFINE_OPTION(Vector_radius_attribute);

DEFINE_VECTOR(uint8_t);

typedef struct RadiusData {
    uint8_t code;
    uint8_t identifier;
    uint16_t length;
    span authentificator;
    option_Vector_radius_attribute attributes;
} radius_data;

typedef struct SSHBanner {
    span protover;
    span swver;
} SSHBanner;

typedef struct SSHRecordHeader {
    uint32_t pkt_len;
    uint8_t padding_len;
    uint8_t msg_code;
} SSHRecordHeader;

typedef struct SSHPacketKeyExchange {
    span cookie;
    span kex_algs;
    span server_host_key_algs;
    span encr_algs_client_to_server;
    span encr_algs_server_to_client;
    span max_algs_client_to_server;
    span max_algs_server_to_client;
    span comp_algs_client_to_server;
    span comp_algs_server_to_client;
    span langs_client_to_server;
    span langs_server_to_client;
    uint8_t first_kex_packet_follows;
    uint32_t reserved;
} SSHPacketKeyExchange;

void create_SSHBanner (span protover, span swver, SSHBanner* res){
    res->protover = protover;
    res->swver = swver;
}

void create_SSHRecordHeader (uint32_t pkt_len, uint8_t padding_len, uint8_t msg_code, SSHRecordHeader* res){
    res->pkt_len = pkt_len;
    res->padding_len = padding_len;
    res->msg_code = msg_code;
}

void create_SSHPacketKeyExchange (span cookie, span kex_algs, span shka,
                                  span eacs, span easc, span macs, span masc, span cacs,
                                  span casc, span lcs, span lsc, uint8_t fkpf,
                                  uint32_t reserved, SSHPacketKeyExchange* res){
    res->cookie = cookie;
    res->kex_algs = kex_algs;
    res->server_host_key_algs = shka;
    res->encr_algs_client_to_server = eacs;
    res->encr_algs_server_to_client = easc;
    res->max_algs_client_to_server = macs;
    res->max_algs_server_to_client = masc;
    res->comp_algs_client_to_server = cacs;
    res->comp_algs_server_to_client = casc;
    res->langs_client_to_server = lcs;
    res->langs_server_to_client = lsc;
    res->first_kex_packet_follows = fkpf;
    res->reserved= reserved;
}


void create_RadiusData (uint8_t code, uint8_t identifier, uint16_t length, span authentificator, option_Vector_radius_attribute attributes, radius_data* res){
    res->code = code;
    res->identifier = identifier;
    res->length = length;
    res->authentificator = authentificator;
    res->attributes = attributes;
}

void create_UserName(span s, radius_attribute* res) {
    res->key = 0;
    res->attribute.UserName.v = s;
}

void create_UserPassword(span s, radius_attribute* res) {
    res->key = 1;
    res->attribute.UserPassword.v = s;
}

void create_ChapPassword(uint8_t n, span s, radius_attribute* res) {
    res->key = 2;
    res->attribute.ChapPassword.n = n;
    res->attribute.ChapPassword.v = s;
}

void create_NasIPAddress(ipv4 ip, radius_attribute* res) {
    res->key = 3;
    res->attribute.NasIPAddress.ip = ip;
}

void create_NasPort(uint32_t v, radius_attribute* res) {
    res->key = 4;
    res->attribute.NasPort.v = v;
}

void create_Protocol(uint32_t v, radius_attribute* res) {
    res->key = 5;
    res->attribute.Protocol.v = v;
}

void create_FramedIPAddress(ipv4 ip, radius_attribute* res) {
    res->key = 6;
    res->attribute.FramedIPAddress.ip = ip;
}

void create_FramedIPNetmask(ipv4 ip, radius_attribute* res) {
    res->key = 7;
    res->attribute.FramedIPNetmask.ip = ip;
}


void create_Routing(uint32_t v, radius_attribute* res) {
    res->key = 8;
    res->attribute.Routing.v = v;
}

void create_FilterId(span s, radius_attribute* res) {
    res->key = 9;
    res->attribute.FilterId.s = s;
}

void create_FramedMTU(uint32_t v, radius_attribute* res) {
    res->key = 10;
    res->attribute.FramedMTU.v = v;
}

void create_Compression(uint32_t v, radius_attribute* res) {
    res->key = 11;
    res->attribute.Compression.v = v;
}

void create_VendorSpecific(uint32_t v, span s, radius_attribute* res) {
    res->key = 12;
    res->attribute.Compression.v = v;
    res->attribute.VendorSpecific.s = s;
}

void create_CalledStationId(span s, radius_attribute* res) {
    res->key = 13;
    res->attribute.CalledStationId.s = s;
}

void create_CallingStationId(span s, radius_attribute* res) {
    res->key = 14;
    res->attribute.CallingStationId.s = s;
}

void create_Unknown(uint8_t n, span s, radius_attribute* res) {
    res->key = 15;
    res->attribute.Unknown.n = n;
    res->attribute.Unknown.s = s;
}

void create_Service(uint32_t n, radius_attribute* res) {
    res->key = 16;
    res->attribute.Service.v = n;
}


void create_ipv4(uint8_t o1, uint8_t o2, uint8_t o3, uint8_t o4, ipv4* res){
    res->o1 = o1;
    res->o2 = o2;
    res->o3 = o3;
    res->o4 = o4;
}

void create_ipv6(uint16_t o1, uint16_t o2, uint16_t o3, uint16_t o4,
                 uint16_t o5, uint16_t o6, uint16_t o7, uint16_t o8, ipv6* res){
    res->o1 = o1;
    res->o2 = o2;
    res->o3 = o3;
    res->o4 = o4;
    res->o5 = o5;
    res->o6 = o6;
    res->o7 = o7;
    res->o8 = o8;
}


list* cons (void* head, list* tail) {
    list* l = malloc (sizeof(list));
    l->value = head;
    l->next = tail;
    return l;
}

void create_pair (void* left, void* right, pair* res){
    res->left = left;
    res->right = right;
}

void proj1 (pair p, void** v){
    *v = p.left;
}

void proj2 (pair p, void **v){
    *v = p.right;
}

void print_array (uint8_t *tab, uint64_t length) {
    int i;
    printf("{ ");
    for(i = 0; i < length; i++){
        printf("%d; ",*(tab+i));
    };
    printf("};");
}

void pos_span(span s, uint8_t** res) {
    *res = s.pos;
}

void length_span (span s, uint64_t* res) {
    *res = s.length;
}

void set_span (span *s, uint8_t* pos, uint64_t length) {
    s->pos = pos;
    s->length = length;
}

void create_span (uint8_t* pos, uint64_t length, span* pres) {
    span res;
    res.pos = pos;
    res.length = length;
    *pres = res;
}

void take (span* bin, uint64_t size, span* pres) {
    span res;
    res.pos = bin->pos;
    res.length = size;
    set_span (bin, bin->pos + size, bin->length - size);
    *pres = res;
}

void deref (span range, Vector_uint8_t* vec) {
    Vector_uint8_t_make(range.length,vec);
    for (uint64_t i = 0; i < range.length; i++){
        Vector_uint8_t_add(vec, range.pos[i]);
    }
}

void print_span (span s){
    uint64_t length;
    length_span(s,&length);
    printf("Span :\n");
    printf("length : %ld\n",length);
    uint64_t i;
    for (i = 0; i < length; i = i + 8){
        uint64_t j;
        for (j = 0; j < 8; j++){
            printf("%d ",s.pos[i+j]);
        }
        printf("\n");
    }
}

void print_SSHPacketKeyExchange (SSHPacketKeyExchange pke) {
    printf("SSHPacketKeyExchange :\n");
    print_span(pke.cookie);
    print_span (pke.kex_algs);
    print_span (pke.server_host_key_algs);
    print_span (pke.encr_algs_client_to_server);
    print_span (pke.encr_algs_server_to_client);
    print_span (pke.max_algs_client_to_server);
    print_span (pke.max_algs_server_to_client);
    print_span (pke.comp_algs_client_to_server);
    print_span (pke.comp_algs_server_to_client);
    print_span (pke.langs_client_to_server);
    print_span (pke.langs_server_to_client);
    printf ("fkpf : %u\n", pke.first_kex_packet_follows);
    printf ("reserved : %u\n", pke.reserved);
}

void print_SSHPacketKeyExchange_string (SSHPacketKeyExchange pke) {
    printf("SSHPacketKeyExchange :\n");
    printf("%s\n",pke.cookie.pos);
    printf ("%s\n",pke.kex_algs.pos);
    printf ("%s\n",pke.server_host_key_algs.pos);
    printf ("%s\n",pke.encr_algs_client_to_server.pos);
    printf ("%s\n",pke.encr_algs_server_to_client.pos);
    printf ("%s\n",pke.max_algs_client_to_server.pos);
    printf ("%s\n",pke.max_algs_server_to_client.pos);
    printf ("%s\n",pke.comp_algs_client_to_server.pos);
    printf ("%s\n",pke.comp_algs_server_to_client.pos);
    printf ("%s\n",pke.langs_client_to_server.pos);
    printf ("%s\n",pke.langs_server_to_client.pos);
    printf ("fkpf : %u\n", pke.first_kex_packet_follows);
    printf ("reserved : %u\n", pke.reserved);
}

void get (span *s, span* res){
    res->pos = s->pos;
    res->length = s->length;
}


void set (span *s, span save){
    s->pos = save.pos;
    s->length = save.length;
}


void print_ipv4(ipv4 ip){
    printf("%d.%d.%d.%d",ip.o1,ip.o2,ip.o3,ip.o4);
}

void print_radius_attribute(radius_attribute attr) {
    switch (attr.key){
    case 0 :
        printf ("UserName :\n span :");
        print_span(attr.attribute.UserName.v);
        break;
    case 1 :
        printf ("UserPassword :\n span :");
        print_span(attr.attribute.UserPassword.v);
        break;
    case 2 :
        printf ("ChapPassword :\n n : %d\nspan :",attr.attribute.ChapPassword.n);
        print_span(attr.attribute.ChapPassword.v);
        break;
    case 3 :
        printf ("ChapPassword :\n ipv4 :");
        print_ipv4(attr.attribute.NasIPAddress.ip);
        break;
    case 4 :
        printf ("NasPort :\n uint32 :%d\n",attr.attribute.NasPort.v);
        break;
    case 5 :
        printf ("Protocol :\n uint32 :%d\n",attr.attribute.Protocol.v);
        break;
    case 6 :
        printf ("FramedIPAddress :\n ip :");
        print_ipv4(attr.attribute.FramedIPAddress.ip);
        break;
    case 7 :
        printf ("FramedIPNetmask :\n ip :");
        print_ipv4(attr.attribute.FramedIPNetmask.ip);
        break;
    case 8 :
        printf ("Routing :\n uint32 :%d\n",attr.attribute.Routing.v);
        break;
    case 9 :
        printf ("FilterId :\n span :");
        print_span(attr.attribute.FilterId.s);
        break;
    case 10 :
        printf ("FramedMTU :\n uint32 :%d\n",attr.attribute.FramedMTU.v);
        break;
    case 11 :
        printf ("Compression :\n uint32 :%d\n",attr.attribute.Compression.v);
        break;
    case 12 :
        printf ("VendorSpecific :\n uint32 :%d\nspan :",attr.attribute.VendorSpecific.v);
        print_span(attr.attribute.VendorSpecific.s);
        break;
    case 13 :
        printf ("CalledStationId :\n span :");
        print_span(attr.attribute.CalledStationId.s);
        break;
    case 14 :
        printf ("CallingStationId :\n span :");
        print_span(attr.attribute.CallingStationId.s);
        break;
    case 15 :
        printf ("Unknown :\n uint32 :%d\nspan :",attr.attribute.Unknown.n);
        print_span(attr.attribute.Unknown.s);
        break;
    case 16 :
        printf ("Compression :\n uint32 :%d\n",attr.attribute.Service.v);
        break;
    default :
        printf ("Résultat normalement impossible\n");
    }
}
