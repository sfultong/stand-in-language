#ifndef Telomare_GUARD
#define Telomare_GUARD
/**
 * @file Telomare.h
 * @author Mateusz Kłoczko
 * @date 27 Apr 2018
 * @brief Stand-in-language C representation.
 */

#ifdef __cplusplus
extern "C" {
#endif

// Tags for Telomare grammar
#define Telomare_ZERO    (0)
#define Telomare_PAIR    (1)
#define Telomare_ENV     (2)
#define Telomare_SETENV  (3)
#define Telomare_DEFER   (4)
#define Telomare_GATE    (5)
#define Telomare_PLEFT   (6)
#define Telomare_PRIGHT  (7)
#define Telomare_TRACE   (8)

typedef unsigned char telomare_type;

//Representation for dynamic construction

/* Note [C AST and Telomare_Root]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~
 * 
 * The C AST representation is designed to be somewhat memory efficient.
 * Each expression is a struct, which contains the type and pointer
 * to next expressions.
 *
 * That's why we needed to have Telomare_Root - initial entry point,
 * pointing to the top-most node.
 */

/**
 * @brief Stores the top-most expression. Does not exist in grammar.
 */
typedef struct Telomare_Root{
    telomare_type type;
    void * value;
} Telomare_Root;

typedef struct Telomare_Zero{} Telomare_Zero;
typedef struct Telomare_Pair{
    telomare_type left_type;
    telomare_type right_type;
    void * left_value;
    void * right_value; 
} Telomare_Pair;
typedef struct Telomare_Env{} Telomare_Env;
typedef struct Telomare_SetEnv{
    telomare_type type;
    void * value; 
} Telomare_SetEnv;
typedef struct Telomare_Defer{
    telomare_type type;
    void * value; 
} Telomare_Defer;
typedef struct Telomare_Gate{
  telomare_type left_type;
  telomare_type right_type;
  void * left_value;
  void * right_value;
} Telomare_Gate;
typedef struct Telomare_PLeft{
    telomare_type type;
    void * value; 
} Telomare_PLeft;
typedef struct Telomare_PRight{
    telomare_type type;
    void * value; 
} Telomare_PRight;
typedef struct Telomare_Trace{} Telomare_Trace;

/**
 * @brief Telomare_Stack nodes.
 *
 * Used in telomare_traverse, telomare_serialize and telomare_deserialize
 */
typedef struct Telomare_Stack{
    struct Telomare_Stack * next;
    telomare_type  type;
    void * value;
} Telomare_Stack;

Telomare_Stack* telomare_stack_new(telomare_type type, void * val);
void telomare_stack_add(Telomare_Stack ** stack, telomare_type type, void * val);
void telomare_stack_pop(Telomare_Stack ** stack);

/**
 * @brief Traverse each node and perform a computation based on the node type. Does not change the AST.
 */
void telomare_traverse(Telomare_Root * root, void (*fn)(telomare_type, void*), void * state);

/**
 * @brief Checks for equality between two ASTs.
 */
unsigned char telomare_equal(Telomare_Root * root1, Telomare_Root *root2);

/**
 * @brief Count the number of nodes in AST.
 */
unsigned long telomare_count(Telomare_Root * root);

/**
 * @brief Delete the memory under Telomare AST
 */
void telomare_free(Telomare_Root * root);

/**
 * @brief Serialized representation of Telomare.
 * 
 * The representation is somewhat static - it's not possible to
 * add new nodes.
 */
typedef struct Telomare_Serialized{
    unsigned long      size;
    telomare_type      storage[];
} Telomare_Serialized;


/**
 * @brief Serializer state, modified through telomare_traverse. Used by telomare_serialize.
 */
typedef struct Telomare_Serializer_State{
    unsigned long count;
    Telomare_Serialized * serialized;
} Telomare_Serializer_State;

Telomare_Serialized * telomare_serialize(Telomare_Root * root);

/**
 * @brief Deserialize into Telomare AST.
 * 
 * Assumes correct input. Undefined behaviour otherwise.
 */
Telomare_Root * telomare_deserialize(Telomare_Serialized * serialized);


/**
 * @brief Count the number of nodes in AST.
 */
unsigned long telomare_count_old(Telomare_Root * root);

#ifdef __cplusplus
}
#endif

#endif
