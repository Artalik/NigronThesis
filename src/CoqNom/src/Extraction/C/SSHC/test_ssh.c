#include "parser_ssh.c"

#include <sys/mman.h>
#include <time.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>

int main (void){

    pair_09SSHPacket04span rdata;

    int CLIENT_KEY_EXCHANGE = open("assets/client_init.raw", O_RDONLY);
    if(CLIENT_KEY_EXCHANGE < 0){
        printf("\n\"%s \" could not open\n","assets/client_init.raw");
        exit(1);
    }

    int CLIENT_DH_INIT = open("assets/dh_init.raw", O_RDONLY);
    if(CLIENT_DH_INIT < 0){
        printf("\n\"%s \" could not open\n","assets/dh_init.raw");
        exit(1);
    }

    int SERVER_DH_REPLY = open("assets/dh_reply.raw", O_RDONLY);
    if(SERVER_DH_REPLY < 0){
        printf("\n\"%s \" could not open\n","assets/dh_reply.raw");
        exit(1);
    }

    int SERVER_NEW_KEYS = open("assets/new_keys.raw", O_RDONLY);
    if(SERVER_NEW_KEYS < 0){
        printf("\n\"%s \" could not open\n","assets/new_keys.raw");
        exit(1);
    }

    int SERVER_COMPAT = open("assets/server_compat.raw", O_RDONLY);
    if(SERVER_COMPAT < 0){
        printf("\n\"%s \" could not open\n","assets/server_compat.raw");
        exit(1);
    }

    struct stat statbuf_KEY_EXCHANGE;
    int err_KEY_EXCHANGE = fstat(CLIENT_KEY_EXCHANGE, &statbuf_KEY_EXCHANGE);

    if(err_KEY_EXCHANGE < 0){
        printf("\n\"%s \" could not open\n","assets/client_init.raw");
        exit(2);
    }

    struct stat statbuf_DH_INIT;
    int err_DH_INIT = fstat(CLIENT_DH_INIT, &statbuf_DH_INIT);


    if(err_DH_INIT < 0){
        printf("\n\"%s \" could not open\n","assets/dh_init.raw");
        exit(2);
    }

    struct stat statbuf_DH_REPLY;
    int err_DH_REPLY = fstat(SERVER_DH_REPLY, &statbuf_DH_REPLY);

    if(err_DH_REPLY < 0){
        printf("\n\"%s \" could not open\n","assets/dh_reply.raw");
        exit(2);
    }

    struct stat statbuf_NEW_KEYS;
    int err_NEW_KEYS = fstat(SERVER_NEW_KEYS, &statbuf_NEW_KEYS);

    if(err_NEW_KEYS < 0){
        printf("\n\"%s \" could not open\n","assets/new_keys.raw");
        exit(2);
    }

    struct stat statbuf_COMPAT;
    int err_COMPAT = fstat(SERVER_COMPAT, &statbuf_COMPAT);

    if(err_COMPAT < 0){
        printf("\n\"%s \" could not open\n","assets/server_compat.raw");
        exit(2);
    }


    uint8_t *ptr_KEY_EXCHANGE = mmap(NULL, statbuf_KEY_EXCHANGE.st_size, PROT_READ, MAP_SHARED, CLIENT_KEY_EXCHANGE, 0);
    if(ptr_KEY_EXCHANGE == MAP_FAILED){
        printf("Mapping Failed KEY_EXCHANGE\n");
        return 1;
    }
    close(CLIENT_KEY_EXCHANGE);

    span bin;
    create_span(ptr_KEY_EXCHANGE + 21, statbuf_KEY_EXCHANGE.st_size - 21, &bin);
    if(!parse_ssh_packet(&bin, &rdata)){
        printf("Parsing Failed\n");
        return 1;
    }
    uint8_t cookie[16] = {0xca, 0x98, 0x42, 0x14, 0xd6, 0xa5, 0xa7, 0xfd,
                          0x6c, 0xe8, 0xd4, 0x7c, 0x0b, 0xc0, 0x96, 0xcc};

    assert(rdata.snd.length == 11);
    for(int i = 0; i < 11; i++){
        assert (rdata.snd.pos[i] == 0);
    }
    assert(rdata.fst.key == 20);
    assert(rdata.fst.content.keyexchange.cookie.length == 16);
    for(int i = 0; i < 16; i++){
        assert (rdata.fst.content.keyexchange.cookie.pos[i] == cookie[i]);
    }
    assert(rdata.fst.content.keyexchange.langs_client_to_server.length == 0);
    assert(rdata.fst.content.keyexchange.langs_server_to_client.length == 0);
    assert(bin.length == 0);

    err_KEY_EXCHANGE = munmap(ptr_KEY_EXCHANGE, statbuf_KEY_EXCHANGE.st_size);

    if(err_KEY_EXCHANGE != 0){
        printf("UnMapping Failed\n");
        return 1;
    }

    printf("TEST 1 : SUCCESS\n");

    uint8_t *ptr_DH_INIT = mmap(NULL, statbuf_DH_INIT.st_size, PROT_READ, MAP_SHARED, CLIENT_DH_INIT, 0);
    if(ptr_DH_INIT == MAP_FAILED){
        printf("Mapping Failed DH_INIT\n");
        return 1;
    }
    close(CLIENT_DH_INIT);

    create_span(ptr_DH_INIT, statbuf_DH_INIT.st_size, &bin);
    if(!parse_ssh_packet(&bin, &rdata)){
        printf("Parsing Failed\n");
        return 1;
    }
    uint8_t dh[65] =
        {0x04, 0xe7, 0x59, 0x2a, 0xe1, 0xb9, 0xb6, 0xbe,
         0x7c, 0x81, 0x5f, 0xc8, 0x3d, 0x55, 0x7b, 0x8f,
         0xc7, 0x09, 0x1d, 0x71, 0x6c, 0xed, 0x68, 0x45,
         0x6c, 0x31, 0xc7, 0xf3, 0x65, 0x98, 0xa5, 0x44,
         0x7d, 0xa4, 0x28, 0xdd, 0xe7, 0x3a, 0xd9, 0xa1,
         0x0e, 0x4b, 0x75, 0x3a, 0xde, 0x33, 0x99, 0x6e,
         0x41, 0x7d, 0xea, 0x88, 0xe9, 0x90, 0xe3, 0x5a,
         0x27, 0xf8, 0x38, 0x09, 0x01, 0x66, 0x46, 0xd4,
         0xdc,
    };
    assert(rdata.snd.length == 5);
    for(int i = 0; i < 5; i++){
        assert (rdata.snd.pos[i] == 0);
    }
    assert (rdata.fst.key == 30);
    assert (rdata.fst.content.dhinit.length == 65);
    for(int i = 0; i < 65; i++){
        assert (rdata.fst.content.dhinit.pos[i] == dh[i]);
    }
    assert(bin.length == 0);

    err_DH_INIT = munmap(ptr_DH_INIT, statbuf_DH_INIT.st_size);

    if(err_DH_INIT != 0){
        printf("UnMapping Failed\n");
        return 1;
    }

    printf("TEST 2 : SUCCESS\n");

    uint8_t *ptr_DH_REPLY = mmap(NULL, statbuf_DH_REPLY.st_size, PROT_READ, MAP_SHARED, SERVER_DH_REPLY, 0);
    if(ptr_DH_REPLY == MAP_FAILED){
        printf("Mapping Failed DH_REPLY\n");
        return 1;
    }
    close(SERVER_DH_REPLY);

    create_span(ptr_DH_REPLY, statbuf_DH_REPLY.st_size, &bin);
    if(!parse_ssh_packet(&bin, &rdata)){
        printf("Parsing Failed\n");
        return 1;
    }
    uint8_t pubkey[104] =
        {0x00, 0x00, 0x00, 0x13, 0x65, 0x63, 0x64, 0x73,
         0x61, 0x2d, 0x73, 0x68, 0x61, 0x32, 0x2d, 0x6e,
         0x69, 0x73, 0x74, 0x70, 0x32, 0x35, 0x36, 0x00,
         0x00, 0x00, 0x08, 0x6e, 0x69, 0x73, 0x74, 0x70,
         0x32, 0x35, 0x36, 0x00, 0x00, 0x00, 0x41, 0x04,
         0x55, 0xa1, 0xb5, 0x65, 0xde, 0xf5, 0x6a, 0xac,
         0xcb, 0xa9, 0x60, 0xd1, 0x49, 0xf8, 0x8c, 0x46,
         0x42, 0x1c, 0xe2, 0x92, 0x59, 0xe4, 0x5d, 0x85,
         0xdf, 0xb9, 0x27, 0x84, 0xa2, 0x6a, 0x28, 0x83,
         0xe8, 0x49, 0xf6, 0x23, 0x78, 0xc9, 0x60, 0x71,
         0x73, 0xc7, 0x78, 0xf5, 0x83, 0x85, 0xdd, 0xcf,
         0x74, 0x63, 0x0e, 0xbd, 0xcf, 0x78, 0x33, 0xeb,
         0x5e, 0xfa, 0xfe, 0x2f, 0xd8, 0x1c, 0x65, 0xbc
    };

    uint8_t f[65] =
        { 0x04, 0x99, 0x2c, 0x48, 0xfd, 0xeb, 0x2d, 0x58,
          0xdf, 0x37, 0xfd, 0x74, 0xf0, 0x60, 0xe9, 0x9c,
          0x73, 0x40, 0x42, 0x8f, 0x73, 0x28, 0x3f, 0x05,
          0x1a, 0x44, 0x6b, 0xdb, 0xb1, 0x87, 0x4c, 0xe8,
          0xe8, 0x96, 0x4a, 0x36, 0x98, 0x6e, 0x5e, 0x91,
          0x87, 0xd3, 0x04, 0x86, 0x43, 0x83, 0x5f, 0x04,
          0xdd, 0x6e, 0x27, 0x22, 0x2b, 0x3f, 0xb8, 0x00,
          0x82, 0x3f, 0x76, 0x0d, 0xbd, 0x40, 0xc1, 0xd6,
          0x2a };

    uint8_t signature[99] =
        { 0x00, 0x00, 0x00, 0x13, 0x65, 0x63, 0x64, 0x73,
          0x61, 0x2d, 0x73, 0x68, 0x61, 0x32, 0x2d, 0x6e,
          0x69, 0x73, 0x74, 0x70, 0x32, 0x35, 0x36, 0x00,
          0x00, 0x00, 0x48, 0x00, 0x00, 0x00, 0x20, 0x0b,
          0xca, 0x56, 0x33, 0xaf, 0xe5, 0xd6, 0x72, 0xaf,
          0x3f, 0x8c, 0x1a, 0x8c, 0x28, 0x50, 0x6d, 0x3f,
          0x5a, 0xa4, 0x55, 0xba, 0x80, 0x4d, 0x98, 0x16,
          0x56, 0x9b, 0x6b, 0x1f, 0x79, 0x21, 0xc8, 0x00,
          0x00, 0x00, 0x20, 0x0c, 0xa5, 0x7a, 0xce, 0x69,
          0xcf, 0x38, 0x28, 0xb4, 0xb4, 0xf8, 0xf0, 0x4e,
          0xa9, 0x67, 0x8f, 0xd2, 0x62, 0x3c, 0x94, 0x63,
          0x6f, 0x5d, 0x08, 0x25, 0xad, 0xfc, 0x2d, 0x95,
          0x25, 0x73, 0xbc, };

    assert(rdata.snd.length == 10);
    for(int i = 0; i < 10; i++){
        assert (rdata.snd.pos[i] == 0);
    }
    assert (rdata.fst.key == 31);
    assert (rdata.fst.content.dhreply.pubkey_and_cert.length == 104);
    for(int i = 0; i < 104; i++){
        assert (rdata.fst.content.dhreply.pubkey_and_cert.pos[i] == pubkey[i]);
    }
    assert (rdata.fst.content.dhreply.f.length == 65);
    for(int i = 0; i < 65; i++){
        assert (rdata.fst.content.dhreply.f.pos[i] == f[i]);
    }
    assert (rdata.fst.content.dhreply.signature.length == 99);
    for(int i = 0; i < 99; i++){
        assert (rdata.fst.content.dhreply.signature.pos[i] == signature[i]);
    }
    assert(bin.length == 0);

    err_DH_REPLY = munmap(ptr_DH_REPLY, statbuf_DH_REPLY.st_size);

    if(err_DH_INIT != 0){
        printf("UnMapping Failed\n");
        return 1;
    }

    printf("TEST 3 : SUCCESS\n");


    uint8_t *ptr_NEW_KEYS = mmap(NULL, statbuf_NEW_KEYS.st_size, PROT_READ, MAP_SHARED, SERVER_NEW_KEYS, 0);
    if(ptr_NEW_KEYS == MAP_FAILED){
        printf("Mapping Failed NEW_KEYS\n");
        return 1;
    }
    close(SERVER_NEW_KEYS);

    create_span(ptr_NEW_KEYS, statbuf_NEW_KEYS.st_size, &bin);
    if(!parse_ssh_packet(&bin, &rdata)){
        printf("Parsing Failed\n");
        return 1;
    }
    assert(rdata.snd.length == 10);
    for(int i = 0; i < 10; i++){
        assert (rdata.snd.pos[i] == 0);
    }
    assert (rdata.fst.key == 21);
    assert(bin.length == 0);

    err_NEW_KEYS = munmap(ptr_NEW_KEYS, statbuf_NEW_KEYS.st_size);

    if(err_NEW_KEYS != 0){
        printf("UnMapping Failed\n");
        return 1;
    }

    printf("TEST 4 : SUCCESS\n");

    uint8_t ptr_INVALID[8] = "\x00\x00\x00\x00\x00\x00\x00\x00";

    create_span(ptr_INVALID, 8, &bin);
    if(!parse_ssh_packet(&bin, &rdata)){
        printf("TEST 5 : SUCCESS\n");
        return 1;
    }
    printf("TEST 5 : FAILED\n");
    return 0;
}
