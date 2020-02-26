/**
 * @file SIL.c
 * @author Mateusz Kłoczko
 * @date 27 Apr 2018
 * @brief Stand-in-language C representation.
 */

#include "SIL.h"

#include <stdio.h>
#include <stdlib.h>


SIL_Stack* sil_stack_new(sil_type type, void * val){
    SIL_Stack * ret = (SIL_Stack*)malloc(sizeof(SIL_Stack));
    ret->next  = 0;
    ret->type  = type;
    ret->value = val;
    return ret;
}

void sil_stack_add(SIL_Stack ** stack, sil_type type, void * val){
    SIL_Stack * tmp = sil_stack_new(type, val); 
    tmp->next = (*stack);
    (*stack) = tmp;
}

void sil_stack_pop(SIL_Stack ** stack){
    SIL_Stack * tmp = (*stack);
    (*stack) = (*stack)->next;
    free(tmp);
}

/**
 * @brief Traverse each node and perform a computation based on the node type. Does not change the AST.
 */
void sil_traverse(SIL_Root * root, void (*fn)(sil_type, void*), void * state){
    SIL_Stack * stack = sil_stack_new(root->type, root->value);

    sil_type type = 0;
    void* value   = 0;

    while(stack != 0){
        type  = stack->type;
        value = stack->value;
        sil_stack_pop(&stack);
        while(1){
            fn(type,state);
            switch(type){
                case SIL_ZERO:
                    value = 0;    
                    goto TraverseBranchStop;
                    break;
                case SIL_PAIR:;
                    //Assuming there are no null pointers
                    SIL_Pair * pair = value;
                    type  = pair->left_type;
                    value = pair->left_value; 
                    sil_stack_add(&stack, pair->right_type, pair->right_value);
                    break;
                case SIL_ENV:
                    value = 0;
                    goto TraverseBranchStop;
                    break;
                case SIL_SETENV:;
                    SIL_SetEnv * setenv = value;
                    type  = setenv->type;
                    value = setenv->value; 
                    break;
                case SIL_DEFER:;
                    SIL_Defer * defer = value;
                    type  = defer->type;
                    value = defer->value; 
                    break;
                case SIL_ABORT:
                    value = 0;
                    goto TraverseBranchStop;
                    break;
                case SIL_GATE:;
                    SIL_Gate *gate = value;
                    type  = gate->left_type;
                    value = gate->left_value;
                    sil_stack_add(&stack, gate->right_type, gate->right_value);
                    break;
                case SIL_PLEFT:;
                    SIL_PLeft *pleft = value;
                    type  = pleft->type;
                    value = pleft->value; 
                    break;
                case SIL_PRIGHT:;
                    SIL_PRight *pright = value;
                    type  = pright->type;
                    value = pright->value; 
                    break;
                case SIL_TRACE:
                    value = 0;
                    goto TraverseBranchStop;
                    break; 
                default:
                    fprintf( stderr, "sil_traverse: Received unsupported type %d. Debug me through call stack.\n", type);
                    goto TraverseBranchStop;
                    break;
            }
        }
TraverseBranchStop:;
    }
}

/**
 * @brief Checks for equality between two ASTs.
 */
unsigned char sil_equal(SIL_Root * root1, SIL_Root *root2){
    SIL_Stack * stack1 = sil_stack_new(root1->type, root1->value);
    SIL_Stack * stack2 = sil_stack_new(root2->type, root2->value);

    sil_type type1 = 0;
    void*   value1 = 0;

    sil_type type2 = 0;
    void*   value2 = 0;

    while(stack1 != 0 && stack2 != 0){
        type1  = stack1->type;
        value1 = stack1->value;
        type2  = stack2->type;
        value2 = stack2->value;
        sil_stack_pop(&stack1);
        sil_stack_pop(&stack2);
        //Special case for Zero and Env
        if(type1 != type2){
            return 0;
        }
        while(1){
            //Types not equal:
            if(type1 != type2){
                return 0;
            }
            switch(type1){
                case SIL_ZERO:
                    value1 = 0;    
                    value2 = 0;    
                    goto EqualBranchStop;
                    break;
                case SIL_PAIR:;
                    SIL_Pair * pair1 = value1;
                    type1  = pair1->left_type;
                    value1 = pair1->left_value; 
                    sil_stack_add(&stack1, pair1->right_type, pair1->right_value);

                    SIL_Pair * pair2 = value2;
                    type2  = pair2->left_type;
                    value2 = pair2->left_value; 
                    sil_stack_add(&stack2, pair2->right_type, pair2->right_value);
                    break;
                case SIL_ENV:
                    value1 = 0;
                    value2 = 0;
                    goto EqualBranchStop;
                    break;
                case SIL_SETENV:;
                    SIL_SetEnv * setenv1 = value1;
                    type1  = setenv1->type;
                    value1 = setenv1->value; 

                    SIL_SetEnv * setenv2 = value2;
                    type2  = setenv2->type;
                    value2 = setenv2->value; 
                    break;
                case SIL_DEFER:;
                    SIL_Defer * defer1 = value1;
                    type1  = defer1->type;
                    value1 = defer1->value; 

                    SIL_Defer * defer2 = value2;
                    type2  = defer2->type;
                    value2 = defer2->value; 
                    break;
                case SIL_ABORT:;
                    value1 = 0;
                    value2 = 0;
                    goto EqualBranchStop;
                    break;
                case SIL_GATE:;
                    SIL_Gate *gate1 = value1;
                    type1  = gate1->left_type;
                    value1 = gate1->left_value; 
                    sil_stack_add(&stack1, gate1->right_type, gate1->right_value);

                    SIL_Gate *gate2 = value2;
                    type2  = gate2->left_type;
                    value2 = gate2->left_value; 
                    sil_stack_add(&stack2, gate2->right_type, gate2->right_value);
                    break;
                case SIL_PLEFT:;
                    SIL_PLeft *pleft1 = value1;
                    type1  = pleft1->type;
                    value1 = pleft1->value; 

                    SIL_PLeft *pleft2 = value2;
                    type2  = pleft2->type;
                    value2 = pleft2->value; 
                    break;
                case SIL_PRIGHT:;
                    SIL_PRight *pright1 = value1;
                    type1  = pright1->type;
                    value1 = pright1->value; 

                    SIL_PRight *pright2 = value2;
                    type2  = pright2->type;
                    value2 = pright2->value; 
                    break;
                case SIL_TRACE:
                    value1 = 0;
                    value2 = 0;
                    goto EqualBranchStop;
                    break; 
            }
        }
EqualBranchStop:;
    }
    //Both stacks should be 0.
    
    return stack1 == stack2;
}

static void sil_count_counter(sil_type type, void * state){
    unsigned long * counter = state;
    (*counter) += 1;
}

unsigned long sil_count(SIL_Root * root){
    unsigned long counter = 0;
    sil_traverse(root, sil_count_counter, &counter);
    return counter;
}

/**
 * @brief Free the memory under SIL AST
 */
void sil_free(SIL_Root * root){
    SIL_Stack * stack = sil_stack_new(root->type, root->value);

    sil_type type = 0;
    void* value   = 0;

    while(stack != 0){
        type  = stack->type;
        value = stack->value;
        sil_stack_pop(&stack);
        while(1){
            switch(type){
                case SIL_ZERO:
                    if(value != 0){
                        free(value);
                    }
                    value = 0;    
                    goto FreeBranchStop;
                    break;
                case SIL_PAIR:;
                    //Assuming there are no null pointers
                    SIL_Pair * pair = value;
                    type  = pair->left_type;
                    value = pair->left_value; 
                    sil_stack_add(&stack, pair->right_type, pair->right_value);
                    free(pair);
                    break;
                case SIL_ENV:
                    if(value != 0){
                        free(value);
                    }
                    value = 0;
                    goto FreeBranchStop;
                    break;
                case SIL_SETENV:;
                    SIL_SetEnv * setenv = value;
                    type  = setenv->type;
                    value = setenv->value; 
                    free(setenv);
                    break;
                case SIL_DEFER:;
                    SIL_Defer * defer = value;
                    type  = defer->type;
                    value = defer->value; 
                    free(defer);
                    break;
                case SIL_ABORT:
                    if(value != 0){
                      free(value);
                    }
                    value = 0;
                    goto FreeBranchStop;
                    break;
                case SIL_GATE:;
                    SIL_Gate *gate = value;
                    type  = gate->left_type;
                    value = gate->left_value; 
                    sil_stack_add(&stack, gate->right_type, gate->right_value);
                    free(gate);
                    break;
                case SIL_PLEFT:;
                    SIL_PLeft *pleft = value;
                    type  = pleft->type;
                    value = pleft->value; 
                    free(pleft);
                    break;
                case SIL_PRIGHT:;
                    SIL_PRight *pright = value;
                    type  = pright->type;
                    value = pright->value; 
                    free(pright);
                    break;
                case SIL_TRACE:;
                    if(value != 0){
                      free(value);
                    }
                    value = 0;
                    goto FreeBranchStop;
                    break; 
                default:
                    fprintf( stderr, "free: Received unsupported type %d. Debug me through call stack.\n", type);
                    goto FreeBranchStop;
                    break;
            }
        }
FreeBranchStop:;
    }
}



static void sil_serializer(sil_type type, void* void_state){
    SIL_Serializer_State * state = void_state;
    state->serialized->storage[state->count] = type;
    state->count += 1;
}

SIL_Serialized * sil_serialize(SIL_Root * root){
    SIL_Serialized * ret;
    unsigned long size = sil_count(root);
    ret = (SIL_Serialized*)malloc(sizeof(SIL_Serialized) + size * sizeof(sil_type));
    ret->size = size;

    SIL_Serializer_State state;
    state.count = 0;
    state.serialized = ret;

    sil_traverse(root, sil_serializer, &state);

    return ret;
}

/**
 * @brief Stack for deserialization
 */

typedef struct SIL_Deserialize_Stack{
    struct SIL_Deserialize_Stack * next;
    sil_type * type_ptr;
    void    ** value_ptr;
}SIL_Deserialize_Stack;


SIL_Deserialize_Stack* sil_deserialize_stack_new(sil_type * type, void ** val){
    SIL_Deserialize_Stack * ret = (SIL_Deserialize_Stack*)malloc(sizeof(SIL_Deserialize_Stack));
    ret->next  = 0;
    ret->type_ptr  = type;
    ret->value_ptr = val;
    return ret;
}

void sil_deserialize_stack_add(SIL_Deserialize_Stack ** stack, sil_type * type, void ** val){
    SIL_Deserialize_Stack * tmp = sil_deserialize_stack_new(type, val); 
    tmp->next = (*stack);
    (*stack) = tmp;
}

void sil_deserialize_stack_pop(SIL_Deserialize_Stack ** stack){
    SIL_Deserialize_Stack * tmp = (*stack);
    (*stack) = (*stack)->next;
    free(tmp);
}

/**
 * @brief Deserialize into SIL AST.
 * 
 * Assumes correct input. Undefined behaviour otherwise.
 */
SIL_Root * sil_deserialize(SIL_Serialized * serialized){
    SIL_Root * ret = (SIL_Root*)malloc(sizeof(SIL_Root));
    ret->value = 0;

    if(serialized->size == 0){
        return ret;
    }
   // ret.type = serialized->storage[0];
    SIL_Deserialize_Stack * stack = sil_deserialize_stack_new(&ret->type, &ret->value);
    sil_type  * type  = 0;
    void     ** value = 0;
    unsigned long i = 0;
    while(stack != 0 && i < serialized->size){
        type  = stack->type_ptr; 
        value = stack->value_ptr; 
        sil_deserialize_stack_pop(&stack);
        while(type != 0 && i < serialized->size){
            sil_type current_type = serialized->storage[i];
            switch(current_type){
                case SIL_ZERO:;
                    (*type)  = current_type;
                    (*value) = 0; 
                    type  = 0;
                    value = 0;
                    break;
                case SIL_PAIR:;
                    SIL_Pair * pair = (SIL_Pair*)malloc(sizeof(SIL_Pair));
                    (*type)  = current_type;
                    (*value) = pair;
                    type  = &(pair->left_type);
                    value = &(pair->left_value);
                    pair->right_type = 100;
                    sil_deserialize_stack_add(&stack, &pair->right_type, &pair->right_value);
                    break;
                case SIL_ENV:;
                    (*type)  = current_type;
                    (*value) = 0; 
                    type  = 0;
                    value = 0;
                    break;
                case SIL_SETENV:;
                    SIL_SetEnv * setenv = (SIL_SetEnv*)malloc(sizeof(SIL_SetEnv));
                    (*type)  = current_type;
                    (*value) = setenv;
                    type  = &(setenv->type);
                    value = &(setenv->value);
                    break;
                case SIL_DEFER:;
                    SIL_Defer * defer = (SIL_Defer*)malloc(sizeof(SIL_Defer));
                    (*type)  = current_type;
                    (*value) = defer;
                    type  = &(defer->type);
                    value = &(defer->value);
                    break;
                case SIL_ABORT:;
                    (*type)  = current_type;
                    (*value) = 0; 
                    type  = 0;
                    value = 0;
                    break;
                case SIL_GATE:;
                    SIL_Gate * gate = (SIL_Gate*)malloc(sizeof(SIL_Gate));
                    (*type)  = current_type;
                    (*value) = gate;
                    type  = &(gate->left_type);
                    value = &(gate->left_value);
                    gate->right_type = 100;
                    sil_deserialize_stack_add(&stack, &gate->right_type, &gate->right_value);
                    break;
                case SIL_PLEFT:;
                    SIL_PLeft * pleft = (SIL_PLeft*)malloc(sizeof(SIL_PLeft));
                    (*type)  = current_type;
                    (*value) = pleft;
                    type  = &(pleft->type);
                    value = &(pleft->value);
                    break;
                case SIL_PRIGHT:;
                    SIL_PRight * pright = (SIL_PRight*)malloc(sizeof(SIL_PRight));
                    (*type)  = current_type;
                    (*value) = pright;
                    type  = &(pright->type);
                    value = &(pright->value);
                    break;
                case SIL_TRACE:;
                    (*type)  = current_type;
                    (*value) = 0; 
                    type  = 0;
                    value = 0;
                    break;
            }
            i++;
        }
    }
    
    return ret;
}


/**
 * @brief Count the number of nodes in AST.
 */
unsigned long sil_count_old(SIL_Root * root){
    unsigned long counter = 0;

    SIL_Stack * stack = sil_stack_new(root->type, root->value);

    sil_type type = 0;
    void* value   = 0;

    while(stack != 0){
        type  = stack->type;
        value = stack->value;
        sil_stack_pop(&stack);
        while(1){
            counter += 1; 
            switch(type){
                case SIL_ZERO:
                    value = 0;
                    goto CountBranchStop;
                    break;
                case SIL_PAIR:;
                    //Assuming there are no null pointers
                    SIL_Pair * pair = value;
                    type  = pair->left_type;
                    value = pair->left_value; 
                    sil_stack_add(&stack, pair->right_type, pair->right_value);
                    break;
                case SIL_ENV:
                    value = 0;
                    goto CountBranchStop;
                    break;
                case SIL_SETENV:;
                    SIL_SetEnv * setenv = value;
                    type  = setenv->type;
                    value = setenv->value; 
                    break;
                case SIL_DEFER:;
                    SIL_Defer * defer = value;
                    type  = defer->type;
                    value = defer->value; 
                    break;
                case SIL_ABORT:;
                    value = 0;
                    goto CountBranchStop;
                    break;
                case SIL_GATE:;
                    SIL_Gate *gate = value;
                    type  = gate->left_type;
                    value = gate->left_value; 
                    sil_stack_add(&stack, gate->right_type, gate->right_value);
                    break;
                case SIL_PLEFT:;
                    SIL_PLeft *pleft = value;
                    type  = pleft->type;
                    value = pleft->value; 
                    break;
                case SIL_PRIGHT:;
                    SIL_PRight *pright = value;
                    type  = pright->type;
                    value = pright->value; 
                    break;
                case SIL_TRACE:;
                    value = 0;
                    goto CountBranchStop;
                    break; 
            }
        }
CountBranchStop:;
    }
    return counter;
}



// SIL_Serialized SIL_serialize(SIL_Root * root, unsigned long count){
//     
// };
