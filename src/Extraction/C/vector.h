#include <stdlib.h>
#include <stdint.h>

#define DEFINE_VECTOR_TYPE(_name,_type)                           \
    typedef struct _name {                                        \
        uint64_t capacity;                                        \
        uint64_t size;                                            \
        _type* data;                                              \
    } _name;                                                      \
                                                                  \
    void _name##_make(uint64_t initial_capacity, _name* vec);     \
    void _name##_add(_name* vec, _type data);                     \
    _type* _name##_shallow_free(_name* vec);                      \
    void _name##_deep_free(_name* vec);
