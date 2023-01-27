#include "parser_Radius.c"
#include <sys/mman.h>
#include <time.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>

int main (void){

    radius_data rdata;

    int fd = open("radius_access-request.bin", O_RDONLY);
    if(fd < 0){
        printf("\n\"%s \" could not open\n","radius_access-request.bin");
        exit(1);
    }

    struct stat statbuf;
    int err = fstat(fd, &statbuf);

    if(err < 0){
        printf("\n\"%s \" could not open\n","radius_access-request.bin");
        exit(2);
    }
    uint8_t *ptr = mmap(NULL, statbuf.st_size, PROT_READ,MAP_SHARED, fd, 0);
    if(ptr == MAP_FAILED){
        printf("Mapping Failed\n");
        return 1;
    }
    close(fd);
    span bin;
    create_span(ptr, statbuf.st_size, &bin);
    span save = bin;
    for(int i = 0; i < 100000; i++){
        parse_radius(&bin, &rdata);
        free(rdata.attributes.val.data);
        bin = save;
    }
    printf("Test de performance sur Radius :\n");
    long all = 0;
    int ite = 10;
    clock_t start,end,diff;
    for(int j = 0; j < ite; j++){
        start = clock();
        for(int i = 0; i < 100000000; i++){
            parse_radius(&bin, &rdata);
            free(rdata.attributes.val.data);
            bin = save;
        }
        end = clock ();
        diff = end - start;
        printf(" Cas %d : %ld ms\n", j, diff/1000);
        all = all + diff;
    }
    printf("Millisecond moyen : %ld\n", all / (ite * 1000));

    if(err != 0){
        printf("UnMapping Failed\n");
        return 1;
    }
    assert(rdata.code == 1);
    assert(rdata.identifier == 103);
    assert(rdata.length == 87);
    return 0;
}
