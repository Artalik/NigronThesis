#include "../Datatypes.h"

DEFINE_OPTION(span);

typedef struct SSHVersion {
    span proto;
    span software;
    option_span comments;
} SSHVersion;

void create_SSHVersion (span proto, span software, option_span comments, SSHVersion* res){
    res->proto = proto;
    res->software = software;
    res->comments = comments;
}

typedef struct SSHPacketDisconnect {
    uint32_t reason_code;
    span description;
    span lang;
} SSHPacketDisconnect;


typedef struct SSHPacketKeyExchange {
    span cookie;
    span kex_algs;
    span server_host_key_algs;
    span encr_algs_client_to_server;
    span encr_algs_server_to_client;
    span mac_algs_client_to_server;
    span mac_algs_server_to_client;
    span comp_algs_client_to_server;
    span comp_algs_server_to_client;
    span langs_client_to_server;
    span langs_server_to_client;
    bool first_kex_packet_follows;
} SSHPacketKeyExchange;


void create_SSHPacketKeyExchange (span cookie, span kex_algs, span shka,
                         span eacs, span easc, span macs, span masc, span cacs,
                         span casc, span lcs, span lsc, bool fkpf,
                         SSHPacketKeyExchange* res){
    res->cookie = cookie;
    res->kex_algs = kex_algs;
    res->server_host_key_algs = shka;
    res->encr_algs_client_to_server = eacs;
    res->encr_algs_server_to_client = easc;
    res->mac_algs_client_to_server = macs;
    res->mac_algs_server_to_client = masc;
    res->comp_algs_client_to_server = cacs;
    res->comp_algs_server_to_client = casc;
    res->langs_client_to_server = lcs;
    res->langs_server_to_client = lsc;
    res->first_kex_packet_follows = fkpf;
}

void print_SSHPacketKeyExchange (SSHPacketKeyExchange pke) {
    printf("SSHPacketKeyExchange :\n");
    print_span(pke.cookie);
    print_span (pke.kex_algs);
    print_span (pke.server_host_key_algs);
    print_span (pke.encr_algs_client_to_server);
    print_span (pke.encr_algs_server_to_client);
    print_span (pke.mac_algs_client_to_server);
    print_span (pke.mac_algs_server_to_client);
    print_span (pke.comp_algs_client_to_server);
    print_span (pke.comp_algs_server_to_client);
    print_span (pke.langs_client_to_server);
    print_span (pke.langs_server_to_client);
    printf ("fkpf : %u\n", pke.first_kex_packet_follows);
}

typedef struct SSHPacketDebug {
    bool always_display;
    span message;
    span debug_lang;
} SSHPacketDebug;

typedef struct SSHPacketDhReply {
    span pubkey_and_cert;
    span f;
    span signature;
} SSHPacketDhReply;

void create_SSHPacketDhReply (span pubkey_and_cert, span f,
                              span signature, SSHPacketDhReply* res){
    res->pubkey_and_cert = pubkey_and_cert;
    res->f = f;
    res->signature = signature;
}

typedef struct SSHPacket {
    uint8_t key;
    union SSHPacketU {
        SSHPacketDisconnect disconnect; // 1
        span ignore; // 2
        uint32_t unimplemented; // 3
        SSHPacketDebug debug; // 4
        span servicerequest; // 5
        span serviceaccept; // 6
        SSHPacketKeyExchange keyexchange; // 20
        span dhinit; // 30
        SSHPacketDhReply dhreply; // 31
    } content;
} SSHPacket;

void create_SSHPacketDisconnect (uint32_t reason_code, span description,
                                 span lang, SSHPacketDisconnect* res){
    res->reason_code = reason_code;
    res->description = description;
    res->lang = lang;
}

void create_Disconnect (uint32_t reason_code, span description,
                        span lang, SSHPacket* res){
    res->key = 1;
    res->content.disconnect.reason_code = reason_code;
    res->content.disconnect.description = description;
    res->content.disconnect.lang = lang;
}

void create_Disconnect2 (SSHPacketDisconnect d, SSHPacket* res){
    res->key = 1;
    res->content.disconnect = d;
}

void create_Ignore (span d, SSHPacket* res){
    res->key = 2;
    res->content.ignore = d;
}

void create_Unimplemented (uint32_t d, SSHPacket* res){
    res->key = 3;
    res->content.unimplemented = d;
}

void create_SSHPacketDebug (bool always_display, span message,
                            span debug_lang, SSHPacketDebug* res){
    res->always_display = always_display;
    res->message = message;
    res->debug_lang = debug_lang;
}

void create_Debug (bool always_display, span message,
                   span debug_lang, SSHPacket* res){
    res->key = 4;
    res->content.debug.always_display = always_display;
    res->content.debug.message = message;
    res->content.debug.debug_lang = debug_lang;
}

void create_Debug2 (SSHPacketDebug d, SSHPacket* res){
    res->key = 4;
    res->content.debug = d;
}

void create_ServiceRequest (span d, SSHPacket* res){
    res->key = 5;
    res->content.servicerequest = d;
}

void create_ServiceAccept (span d, SSHPacket* res){
    res->key = 6;
    res->content.serviceaccept = d;
}

void create_KeyExchange (span cookie, span kex_algs, span shka,
                                  span eacs, span easc, span macs, span masc, span cacs,
                                  span casc, span lcs, span lsc, bool fkpf,
                                  SSHPacket* res){
    res->key = 20;
    res->content.keyexchange.cookie = cookie;
    res->content.keyexchange.kex_algs = kex_algs;
    res->content.keyexchange.server_host_key_algs = shka;
    res->content.keyexchange.encr_algs_client_to_server = eacs;
    res->content.keyexchange.encr_algs_server_to_client = easc;
    res->content.keyexchange.mac_algs_client_to_server = macs;
    res->content.keyexchange.mac_algs_server_to_client = masc;
    res->content.keyexchange.comp_algs_client_to_server = cacs;
    res->content.keyexchange.comp_algs_server_to_client = casc;
    res->content.keyexchange.langs_client_to_server = lcs;
    res->content.keyexchange.langs_server_to_client = lsc;
    res->content.keyexchange.first_kex_packet_follows = fkpf;
}

void create_KeyExchange2 (SSHPacketKeyExchange d, SSHPacket* res){
    res->key = 20;
    res->content.keyexchange = d;
}

void create_NewKeys (SSHPacket* res){
    res->key = 21;
}

void create_DiffieHellmanInit (span dhinit, SSHPacket* res){
    res->key = 30;
    res->content.dhinit = dhinit;
}

void create_DiffieHellmanReply (span pubkey_and_cert, span f, span signature, SSHPacket* res){
    res->key = 31;
    res->content.dhreply.pubkey_and_cert = pubkey_and_cert;
    res->content.dhreply.f = f;
    res->content.dhreply.signature = signature;
}
