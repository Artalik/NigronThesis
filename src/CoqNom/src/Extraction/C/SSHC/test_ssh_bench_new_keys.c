#include "parser_ssh.c"

#include <sys/mman.h>
#include <time.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>

int main (void){

    pair_09SSHPacket04span rdata;

    int CLIENT_DH_INIT = open("assets/new_keys.raw", O_RDONLY);
    if(CLIENT_DH_INIT < 0){
        printf("\n\"%s \" could not open\n","assets/new_keys.raw");
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
    printf("Test de performance sur SSH - New Keys :\n");
    long all = 0;
    int ite = 10;
    clock_t start,diff,end;
    for(int j = 0; j < ite; j++){
        start = clock();
        for(int i = 0; i < 100000000; i++){
            parse_ssh_packet(&bin, &rdata);
            bin = save;
        }
        end = clock();
        diff = end - start;
        printf(" Cas %d : %ld ms\n", j, diff/1000);
        all = all + diff;
    }
    printf("SSH - New Keys : %ld ms\n", all / (ite * 1000));
    assert(rdata.snd.length == 10);
    for(int i = 0; i < 10; i++){
        assert (rdata.snd.pos[i] == 0);
    }
    assert (rdata.fst.key == 21);
    return 0;
}
