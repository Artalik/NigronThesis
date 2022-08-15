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
