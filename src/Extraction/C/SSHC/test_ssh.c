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
    assert(rdata.snd.pos[0] == 0);
    assert(rdata.snd.pos[1] == 0);
    assert(rdata.snd.pos[2] == 0);
    assert(rdata.snd.pos[3] == 0);
    assert(rdata.snd.pos[4] == 0);
    assert(rdata.snd.pos[5] == 0);
    assert(rdata.snd.pos[6] == 0);
    assert(rdata.snd.pos[7] == 0);
    assert(rdata.snd.pos[8] == 0);
    assert(rdata.snd.pos[9] == 0);
    assert(rdata.snd.pos[10] == 0);
    assert(rdata.snd.pos[11] == 0);
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
    printf("SUCCESS\n");
    return 0;
}
