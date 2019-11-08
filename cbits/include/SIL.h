#ifndef SIL_GUARD
#define SIL_GUARD
/**
 * @file SIL.h
 * @author Mateusz Kłoczko
 * @date 27 Apr 2018
 * @brief Stand-in-language C representation.
 */

#ifdef __cplusplus
extern "C" {
#endif

// Tags for SIL grammar
#define SIL_ZERO    (0)
#define SIL_PAIR    (1)
#define SIL_ENV     (2)
#define SIL_SETENV  (3)
#define SIL_DEFER   (4)
#define SIL_ABORT   (5)
#define SIL_GATE    (6)
#define SIL_PLEFT   (7)
#define SIL_PRIGHT  (8)
#define SIL_TRACE   (9)

typedef unsigned char sil_type;

//Representation for dynamic construction

/* Note [C AST and SIL_Root]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~
 * 
 * The C AST representation is designed to be somewhat memory efficient.
 * Each expression is a struct, which contains the type and pointer
 * to next expressions.
 *
 * That's why we needed to have SIL_Root - initial entry point,
 * pointing to the top-most node.
 */

/**
 * @brief Stores the top-most expression. Does not exist in grammar.
 */
typedef struct SIL_Root{
    sil_type type;
    void * value;
} SIL_Root;

typedef struct SIL_Zero{} SIL_Zero;
typedef struct SIL_Pair{
    sil_type left_type;
    sil_type right_type;
    void * left_value;
    void * right_value; 
} SIL_Pair;
typedef struct SIL_Env{} SIL_Env;
typedef struct SIL_SetEnv{
    sil_type type;
    void * value; 
} SIL_SetEnv;
typedef struct SIL_Defer{
    sil_type type;
    void * value; 
} SIL_Defer;
typedef struct SIL_Abort{
    sil_type type;
    void * value; 
} SIL_Abort;
typedef struct SIL_Gate{} SIL_Gate;
typedef struct SIL_PLeft{
    sil_type type;
    void * value; 
} SIL_PLeft;
typedef struct SIL_PRight{
    sil_type type;
    void * value; 
} SIL_PRight;
typedef struct SIL_Trace{
    sil_type type;
    void * value; 
} SIL_Trace;

/**
 * @brief SIL_Stack nodes.
 *
 * Used in sil_traverse, sil_serialize and sil_deserialize
 */
typedef struct SIL_Stack{
    struct SIL_Stack * next;
    sil_type  type;
    void * value;
} SIL_Stack;

SIL_Stack* sil_stack_new(sil_type type, void * val);
void sil_stack_add(SIL_Stack ** stack, sil_type type, void * val);
void sil_stack_pop(SIL_Stack ** stack);

/**
 * @brief Traverse each node and perform a computation based on the node type. Does not change the AST.
 */
void sil_traverse(SIL_Root * root, void (*fn)(sil_type, void*), void * state);

/**
 * @brief Checks for equality between two ASTs.
 */
unsigned char sil_equal(SIL_Root * root1, SIL_Root *root2);

/**
 * @brief Count the number of nodes in AST.
 */
unsigned long sil_count(SIL_Root * root);

/**
 * @brief Delete the memory under SIL AST
 */
void sil_free(SIL_Root * root);

/**
 * @brief Serialized representation of SIL.
 * 
 * The representation is somewhat static - it's not possible to
 * add new nodes.
 */
typedef struct SIL_Serialized{
    unsigned long      size;
    sil_type      storage[];
} SIL_Serialized;


/**
 * @brief Serializer state, modified through sil_traverse. Used by sil_serialize.
 */
typedef struct SIL_Serializer_State{
    unsigned long count;
    SIL_Serialized * serialized;
} SIL_Serializer_State;

SIL_Serialized * sil_serialize(SIL_Root * root);

/**
 * @brief Deserialize into SIL AST.
 * 
 * Assumes correct input. Undefined behaviour otherwise.
 */
SIL_Root * sil_deserialize(SIL_Serialized * serialized);


/**
 * @brief Count the number of nodes in AST.
 */
unsigned long sil_count_old(SIL_Root * root);

#ifdef __cplusplus
}
#endif

#endif
