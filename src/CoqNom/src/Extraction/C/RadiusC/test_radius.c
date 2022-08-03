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
    if(!parse_radius(&bin, &rdata)){
        printf("Parsing Failed\n");
        return 1;
    }
    assert(rdata.code == 1);
    assert(rdata.identifier == 103);
    assert(rdata.length == 87);
    assert(rdata.authentificator.length == 16);
    assert(rdata.attributes.ok);
    assert(rdata.attributes.val.size == 6);
    assert(rdata.attributes.val.data[0].key == 0);
    assert(rdata.attributes.val.data[1].key == 1);
    assert(rdata.attributes.val.data[2].key == 3);
    assert(rdata.attributes.val.data[3].key == 4);
    assert(rdata.attributes.val.data[4].key == 15);
    assert(rdata.attributes.val.data[5].key == 15);
    assert(bin.length == 0);
    err = munmap(ptr, statbuf.st_size);

    if(err != 0){
        printf("UnMapping Failed\n");
        return 1;
    }
    printf("SUCCESS\n");
    return 0;
}
