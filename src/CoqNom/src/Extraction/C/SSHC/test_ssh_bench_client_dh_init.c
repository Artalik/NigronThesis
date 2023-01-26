#include "parser_ssh.c"

#include <sys/mman.h>
#include <time.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>

int main (void){

    pair_09SSHPacket04span rdata;

    int CLIENT_DH_INIT = open("assets/dh_init.raw", O_RDONLY);
    if(CLIENT_DH_INIT < 0){
        printf("\n\"%s \" could not open\n","assets/dh_init.raw");
        exit(1);
    }

    struct stat statbuf_DH_INIT;
    int err_DH_INIT = fstat(CLIENT_DH_INIT, &statbuf_DH_INIT);

    if(err_DH_INIT < 0){
        printf("\n\"%s \" could not open\n","assets/dh_init.raw");
        exit(2);
    }

    uint8_t *ptr_DH_INIT = mmap(NULL, statbuf_DH_INIT.st_size, PROT_READ, MAP_SHARED, CLIENT_DH_INIT, 0);
    if(ptr_DH_INIT == MAP_FAILED){
        printf("Mapping Failed DH_INIT\n");
        return 1;
    }
    close(CLIENT_DH_INIT);
    span bin;
    create_span(ptr_DH_INIT, statbuf_DH_INIT.st_size, &bin);
    span save = bin;

    for(int i = 0; i < 100000; i++){
        parse_ssh_packet(&bin, &rdata);
        bin = save;
    }
    long all = 0;
    int ite = 10;
    clock_t start,end,diff;
    for(int j = 0; j < ite; j++){
        start = clock();
        for(int i = 0; i < 100000000; i++){
            parse_ssh_packet(&bin, &rdata);
            bin = save;
        }
        end = clock ();
        diff = end - start;
        printf("Cas %d : %ld ms\n", j, diff/1000);
        all = all + diff;
    }
    printf("Millisecond moyen : %ld\n", all / (ite * 1000));
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
    return 0;
}
