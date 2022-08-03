#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#define DEFINE_OPTION_TYPE(_name,_type)                           \
    typedef struct _name {                                        \
        bool ok;                                                  \
        _type val;                                                \
    } _name;

#define DEFINE_OPTION(_type)                    \
    DEFINE_OPTION_TYPE(option_##_type,_type);
