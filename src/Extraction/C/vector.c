#include "vector.h"

#define DEFINE_VECTOR_IMPLEM(_name,_type)                               \
                                                                        \
    void _name##_make(uint64_t initial_capacity, _name* vec){           \
        vec->size = 0;                                                  \
        vec->capacity = initial_capacity;                               \
        vec->data = calloc(initial_capacity, sizeof(*vec->data));       \
    }                                                                   \
                                                                        \
    void _name##_add(_name* vec, _type data){                           \
        if(vec->size >= vec-> capacity) {                               \
            vec->capacity = vec->capacity + (vec->capacity >> 1);       \
            vec->data = realloc(vec->data, vec->capacity * sizeof *vec->data); \
        }                                                               \
        vec->data[vec->size++] = data;                                  \
    }                                                                   \
                                                                        \
    _type* _name##_shallow_free(_name* vec){                            \
        _type* data = vec->data;                                        \
        free(vec);                                                      \
        return data;                                                    \
    }                                                                   \
                                                                        \
    void _name##_deep_free(_name* vec){                                 \
        free(vec->data);                                                \
        free(vec);                                                      \
    }                                                                   \

#define DEFINE_VECTOR(_type)                            \
    DEFINE_VECTOR_TYPE(Vector_##_type,_type);           \
    DEFINE_VECTOR_IMPLEM(Vector_##_type,_type);
