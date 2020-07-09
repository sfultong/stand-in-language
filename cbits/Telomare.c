/**
 * @file Telomare.c
 * @author Mateusz Kłoczko
 * @date 27 Apr 2018
 * @brief Stand-in-language C representation.
 */

#include "Telomare.h"

#include <stdio.h>
#include <stdlib.h>


Telomare_Stack* telomare_stack_new(telomare_type type, void * val){
    Telomare_Stack * ret = (Telomare_Stack*)malloc(sizeof(Telomare_Stack));
    ret->next  = 0;
    ret->type  = type;
    ret->value = val;
    return ret;
}

void telomare_stack_add(Telomare_Stack ** stack, telomare_type type, void * val){
    Telomare_Stack * tmp = telomare_stack_new(type, val); 
    tmp->next = (*stack);
    (*stack) = tmp;
}

void telomare_stack_pop(Telomare_Stack ** stack){
    Telomare_Stack * tmp = (*stack);
    (*stack) = (*stack)->next;
    free(tmp);
}

/**
 * @brief Traverse each node and perform a computation based on the node type. Does not change the AST.
 */
void telomare_traverse(Telomare_Root * root, void (*fn)(telomare_type, void*), void * state){
    Telomare_Stack * stack = telomare_stack_new(root->type, root->value);

    telomare_type type = 0;
    void* value   = 0;

    while(stack != 0){
        type  = stack->type;
        value = stack->value;
        telomare_stack_pop(&stack);
        while(1){
            fn(type,state);
            switch(type){
                case Telomare_ZERO:
                    value = 0;    
                    goto TraverseBranchStop;
                    break;
                case Telomare_PAIR:;
                    //Assuming there are no null pointers
                    Telomare_Pair * pair = value;
                    type  = pair->left_type;
                    value = pair->left_value; 
                    telomare_stack_add(&stack, pair->right_type, pair->right_value);
                    break;
                case Telomare_ENV:
                    value = 0;
                    goto TraverseBranchStop;
                    break;
                case Telomare_SETENV:;
                    Telomare_SetEnv * setenv = value;
                    type  = setenv->type;
                    value = setenv->value; 
                    break;
                case Telomare_DEFER:;
                    Telomare_Defer * defer = value;
                    type  = defer->type;
                    value = defer->value; 
                    break;
                case Telomare_ABORT:
                    value = 0;
                    goto TraverseBranchStop;
                    break;
                case Telomare_GATE:;
                    Telomare_Gate *gate = value;
                    type  = gate->left_type;
                    value = gate->left_value;
                    telomare_stack_add(&stack, gate->right_type, gate->right_value);
                    break;
                case Telomare_PLEFT:;
                    Telomare_PLeft *pleft = value;
                    type  = pleft->type;
                    value = pleft->value; 
                    break;
                case Telomare_PRIGHT:;
                    Telomare_PRight *pright = value;
                    type  = pright->type;
                    value = pright->value; 
                    break;
                case Telomare_TRACE:
                    value = 0;
                    goto TraverseBranchStop;
                    break; 
                default:
                    fprintf( stderr, "telomare_traverse: Received unsupported type %d. Debug me through call stack.\n", type);
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
unsigned char telomare_equal(Telomare_Root * root1, Telomare_Root *root2){
    Telomare_Stack * stack1 = telomare_stack_new(root1->type, root1->value);
    Telomare_Stack * stack2 = telomare_stack_new(root2->type, root2->value);

    telomare_type type1 = 0;
    void*   value1 = 0;

    telomare_type type2 = 0;
    void*   value2 = 0;

    while(stack1 != 0 && stack2 != 0){
        type1  = stack1->type;
        value1 = stack1->value;
        type2  = stack2->type;
        value2 = stack2->value;
        telomare_stack_pop(&stack1);
        telomare_stack_pop(&stack2);
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
                case Telomare_ZERO:
                    value1 = 0;    
                    value2 = 0;    
                    goto EqualBranchStop;
                    break;
                case Telomare_PAIR:;
                    Telomare_Pair * pair1 = value1;
                    type1  = pair1->left_type;
                    value1 = pair1->left_value; 
                    telomare_stack_add(&stack1, pair1->right_type, pair1->right_value);

                    Telomare_Pair * pair2 = value2;
                    type2  = pair2->left_type;
                    value2 = pair2->left_value; 
                    telomare_stack_add(&stack2, pair2->right_type, pair2->right_value);
                    break;
                case Telomare_ENV:
                    value1 = 0;
                    value2 = 0;
                    goto EqualBranchStop;
                    break;
                case Telomare_SETENV:;
                    Telomare_SetEnv * setenv1 = value1;
                    type1  = setenv1->type;
                    value1 = setenv1->value; 

                    Telomare_SetEnv * setenv2 = value2;
                    type2  = setenv2->type;
                    value2 = setenv2->value; 
                    break;
                case Telomare_DEFER:;
                    Telomare_Defer * defer1 = value1;
                    type1  = defer1->type;
                    value1 = defer1->value; 

                    Telomare_Defer * defer2 = value2;
                    type2  = defer2->type;
                    value2 = defer2->value; 
                    break;
                case Telomare_ABORT:;
                    value1 = 0;
                    value2 = 0;
                    goto EqualBranchStop;
                    break;
                case Telomare_GATE:;
                    Telomare_Gate *gate1 = value1;
                    type1  = gate1->left_type;
                    value1 = gate1->left_value; 
                    telomare_stack_add(&stack1, gate1->right_type, gate1->right_value);

                    Telomare_Gate *gate2 = value2;
                    type2  = gate2->left_type;
                    value2 = gate2->left_value; 
                    telomare_stack_add(&stack2, gate2->right_type, gate2->right_value);
                    break;
                case Telomare_PLEFT:;
                    Telomare_PLeft *pleft1 = value1;
                    type1  = pleft1->type;
                    value1 = pleft1->value; 

                    Telomare_PLeft *pleft2 = value2;
                    type2  = pleft2->type;
                    value2 = pleft2->value; 
                    break;
                case Telomare_PRIGHT:;
                    Telomare_PRight *pright1 = value1;
                    type1  = pright1->type;
                    value1 = pright1->value; 

                    Telomare_PRight *pright2 = value2;
                    type2  = pright2->type;
                    value2 = pright2->value; 
                    break;
                case Telomare_TRACE:
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

static void telomare_count_counter(telomare_type type, void * state){
    unsigned long * counter = state;
    (*counter) += 1;
}

unsigned long telomare_count(Telomare_Root * root){
    unsigned long counter = 0;
    telomare_traverse(root, telomare_count_counter, &counter);
    return counter;
}

/**
 * @brief Free the memory under Telomare AST
 */
void telomare_free(Telomare_Root * root){
    Telomare_Stack * stack = telomare_stack_new(root->type, root->value);

    telomare_type type = 0;
    void* value   = 0;

    while(stack != 0){
        type  = stack->type;
        value = stack->value;
        telomare_stack_pop(&stack);
        while(1){
            switch(type){
                case Telomare_ZERO:
                    if(value != 0){
                        free(value);
                    }
                    value = 0;    
                    goto FreeBranchStop;
                    break;
                case Telomare_PAIR:;
                    //Assuming there are no null pointers
                    Telomare_Pair * pair = value;
                    type  = pair->left_type;
                    value = pair->left_value; 
                    telomare_stack_add(&stack, pair->right_type, pair->right_value);
                    free(pair);
                    break;
                case Telomare_ENV:
                    if(value != 0){
                        free(value);
                    }
                    value = 0;
                    goto FreeBranchStop;
                    break;
                case Telomare_SETENV:;
                    Telomare_SetEnv * setenv = value;
                    type  = setenv->type;
                    value = setenv->value; 
                    free(setenv);
                    break;
                case Telomare_DEFER:;
                    Telomare_Defer * defer = value;
                    type  = defer->type;
                    value = defer->value; 
                    free(defer);
                    break;
                case Telomare_ABORT:
                    if(value != 0){
                      free(value);
                    }
                    value = 0;
                    goto FreeBranchStop;
                    break;
                case Telomare_GATE:;
                    Telomare_Gate *gate = value;
                    type  = gate->left_type;
                    value = gate->left_value; 
                    telomare_stack_add(&stack, gate->right_type, gate->right_value);
                    free(gate);
                    break;
                case Telomare_PLEFT:;
                    Telomare_PLeft *pleft = value;
                    type  = pleft->type;
                    value = pleft->value; 
                    free(pleft);
                    break;
                case Telomare_PRIGHT:;
                    Telomare_PRight *pright = value;
                    type  = pright->type;
                    value = pright->value; 
                    free(pright);
                    break;
                case Telomare_TRACE:;
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



static void telomare_serializer(telomare_type type, void* void_state){
    Telomare_Serializer_State * state = void_state;
    state->serialized->storage[state->count] = type;
    state->count += 1;
}

Telomare_Serialized * telomare_serialize(Telomare_Root * root){
    Telomare_Serialized * ret;
    unsigned long size = telomare_count(root);
    ret = (Telomare_Serialized*)malloc(sizeof(Telomare_Serialized) + size * sizeof(telomare_type));
    ret->size = size;

    Telomare_Serializer_State state;
    state.count = 0;
    state.serialized = ret;

    telomare_traverse(root, telomare_serializer, &state);

    return ret;
}

/**
 * @brief Stack for deserialization
 */

typedef struct Telomare_Deserialize_Stack{
    struct Telomare_Deserialize_Stack * next;
    telomare_type * type_ptr;
    void    ** value_ptr;
}Telomare_Deserialize_Stack;


Telomare_Deserialize_Stack* telomare_deserialize_stack_new(telomare_type * type, void ** val){
    Telomare_Deserialize_Stack * ret = (Telomare_Deserialize_Stack*)malloc(sizeof(Telomare_Deserialize_Stack));
    ret->next  = 0;
    ret->type_ptr  = type;
    ret->value_ptr = val;
    return ret;
}

void telomare_deserialize_stack_add(Telomare_Deserialize_Stack ** stack, telomare_type * type, void ** val){
    Telomare_Deserialize_Stack * tmp = telomare_deserialize_stack_new(type, val); 
    tmp->next = (*stack);
    (*stack) = tmp;
}

void telomare_deserialize_stack_pop(Telomare_Deserialize_Stack ** stack){
    Telomare_Deserialize_Stack * tmp = (*stack);
    (*stack) = (*stack)->next;
    free(tmp);
}

/**
 * @brief Deserialize into Telomare AST.
 * 
 * Assumes correct input. Undefined behaviour otherwise.
 */
Telomare_Root * telomare_deserialize(Telomare_Serialized * serialized){
    Telomare_Root * ret = (Telomare_Root*)malloc(sizeof(Telomare_Root));
    ret->value = 0;

    if(serialized->size == 0){
        return ret;
    }
   // ret.type = serialized->storage[0];
    Telomare_Deserialize_Stack * stack = telomare_deserialize_stack_new(&ret->type, &ret->value);
    telomare_type  * type  = 0;
    void     ** value = 0;
    unsigned long i = 0;
    while(stack != 0 && i < serialized->size){
        type  = stack->type_ptr; 
        value = stack->value_ptr; 
        telomare_deserialize_stack_pop(&stack);
        while(type != 0 && i < serialized->size){
            telomare_type current_type = serialized->storage[i];
            switch(current_type){
                case Telomare_ZERO:;
                    (*type)  = current_type;
                    (*value) = 0; 
                    type  = 0;
                    value = 0;
                    break;
                case Telomare_PAIR:;
                    Telomare_Pair * pair = (Telomare_Pair*)malloc(sizeof(Telomare_Pair));
                    (*type)  = current_type;
                    (*value) = pair;
                    type  = &(pair->left_type);
                    value = &(pair->left_value);
                    pair->right_type = 100;
                    telomare_deserialize_stack_add(&stack, &pair->right_type, &pair->right_value);
                    break;
                case Telomare_ENV:;
                    (*type)  = current_type;
                    (*value) = 0; 
                    type  = 0;
                    value = 0;
                    break;
                case Telomare_SETENV:;
                    Telomare_SetEnv * setenv = (Telomare_SetEnv*)malloc(sizeof(Telomare_SetEnv));
                    (*type)  = current_type;
                    (*value) = setenv;
                    type  = &(setenv->type);
                    value = &(setenv->value);
                    break;
                case Telomare_DEFER:;
                    Telomare_Defer * defer = (Telomare_Defer*)malloc(sizeof(Telomare_Defer));
                    (*type)  = current_type;
                    (*value) = defer;
                    type  = &(defer->type);
                    value = &(defer->value);
                    break;
                case Telomare_ABORT:;
                    (*type)  = current_type;
                    (*value) = 0; 
                    type  = 0;
                    value = 0;
                    break;
                case Telomare_GATE:;
                    Telomare_Gate * gate = (Telomare_Gate*)malloc(sizeof(Telomare_Gate));
                    (*type)  = current_type;
                    (*value) = gate;
                    type  = &(gate->left_type);
                    value = &(gate->left_value);
                    gate->right_type = 100;
                    telomare_deserialize_stack_add(&stack, &gate->right_type, &gate->right_value);
                    break;
                case Telomare_PLEFT:;
                    Telomare_PLeft * pleft = (Telomare_PLeft*)malloc(sizeof(Telomare_PLeft));
                    (*type)  = current_type;
                    (*value) = pleft;
                    type  = &(pleft->type);
                    value = &(pleft->value);
                    break;
                case Telomare_PRIGHT:;
                    Telomare_PRight * pright = (Telomare_PRight*)malloc(sizeof(Telomare_PRight));
                    (*type)  = current_type;
                    (*value) = pright;
                    type  = &(pright->type);
                    value = &(pright->value);
                    break;
                case Telomare_TRACE:;
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
unsigned long telomare_count_old(Telomare_Root * root){
    unsigned long counter = 0;

    Telomare_Stack * stack = telomare_stack_new(root->type, root->value);

    telomare_type type = 0;
    void* value   = 0;

    while(stack != 0){
        type  = stack->type;
        value = stack->value;
        telomare_stack_pop(&stack);
        while(1){
            counter += 1; 
            switch(type){
                case Telomare_ZERO:
                    value = 0;
                    goto CountBranchStop;
                    break;
                case Telomare_PAIR:;
                    //Assuming there are no null pointers
                    Telomare_Pair * pair = value;
                    type  = pair->left_type;
                    value = pair->left_value; 
                    telomare_stack_add(&stack, pair->right_type, pair->right_value);
                    break;
                case Telomare_ENV:
                    value = 0;
                    goto CountBranchStop;
                    break;
                case Telomare_SETENV:;
                    Telomare_SetEnv * setenv = value;
                    type  = setenv->type;
                    value = setenv->value; 
                    break;
                case Telomare_DEFER:;
                    Telomare_Defer * defer = value;
                    type  = defer->type;
                    value = defer->value; 
                    break;
                case Telomare_ABORT:;
                    value = 0;
                    goto CountBranchStop;
                    break;
                case Telomare_GATE:;
                    Telomare_Gate *gate = value;
                    type  = gate->left_type;
                    value = gate->left_value; 
                    telomare_stack_add(&stack, gate->right_type, gate->right_value);
                    break;
                case Telomare_PLEFT:;
                    Telomare_PLeft *pleft = value;
                    type  = pleft->type;
                    value = pleft->value; 
                    break;
                case Telomare_PRIGHT:;
                    Telomare_PRight *pright = value;
                    type  = pright->type;
                    value = pright->value; 
                    break;
                case Telomare_TRACE:;
                    value = 0;
                    goto CountBranchStop;
                    break; 
            }
        }
CountBranchStop:;
    }
    return counter;
}



// Telomare_Serialized Telomare_serialize(Telomare_Root * root, unsigned long count){
//     
// };
