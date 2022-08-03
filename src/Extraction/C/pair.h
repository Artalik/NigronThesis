#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#define DEFINE_PAIR_TYPE(_name,_type1,_type2)                     \
    typedef struct _name {                                        \
        _type1 fst;                                               \
        _type2 snd;                                               \
    } _name;

#define DEFINE_PAIR(_n1, _type1, _n2, _type2)  \
    DEFINE_PAIR_TYPE(pair_##_n1##_type1##_n2##_type2, _type1, _type2);
