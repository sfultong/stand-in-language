#include <rapidcheck.h>
#include <iostream>
#include <vector>
#include <tuple>
#include <functional>

#include "Telomare.h"

using namespace std;


bool unit_tests(){
   Telomare_Root root;
   Telomare_Pair pair;
   Telomare_Zero zero;
   Telomare_SetEnv setenv;
   Telomare_Env  env;

   root.type = Telomare_PAIR;
   root.value = &pair;

   pair.left_type   = Telomare_SETENV;
   pair.left_value  = &setenv;
   pair.right_type  = Telomare_ZERO;
   pair.right_value = &zero;

   setenv.type  = Telomare_ENV;
   setenv.value = 0;

   unsigned long no_nodes  = telomare_count(&root);
   unsigned long no_nodes2 = telomare_count_old(&root);
   printf("%d %d\n",no_nodes, no_nodes2);

   unsigned char eq = telomare_equal(&root,&root);
   printf("equality: %d\n", eq);

   Telomare_Serialized * serialized = telomare_serialize(&root);
   for(int i = 0; i < serialized->size; i++){
        printf("%d ",serialized->storage[i]);
   }
   printf("\n");
   serialized->storage[1] = Telomare_ZERO;
   serialized->size =2;
   //serialized.storage[2] = Telomare_ZERO;
   //serialized.storage[3] = Telomare_ENV;
   Telomare_Root * deserialized = telomare_deserialize(serialized);

   printf("Is serialized and deserialized tree okay: %d\n", telomare_equal(&root,deserialized));
   Telomare_Serialized * serialized2 = telomare_serialize(deserialized);
   for(int i = 0; i < serialized2->size; i++){
        printf("%d ",serialized2->storage[i]);
   }
   printf("\n");

}



int main(){
    //@TODO Learn how to build generators.
    using NodeGenFn = function<void(telomare_type&, void*&, unsigned long)>;
    NodeGenFn huh = [&](telomare_type &type, void *& value, unsigned long nodes_left){
        const vector<telomare_type> leafs = {Telomare_ZERO, Telomare_ENV}; 
        const vector<telomare_type> nodes = {Telomare_PAIR, Telomare_SETENV,Telomare_DEFER, Telomare_TWIDDLE, Telomare_ABORT
                                       ,Telomare_GATE, Telomare_PLEFT, Telomare_PRIGHT, Telomare_TRACE}; 
        const vector<telomare_type> non_pair = {Telomare_SETENV,Telomare_DEFER, Telomare_TWIDDLE, Telomare_ABORT
                                          ,Telomare_GATE, Telomare_PLEFT, Telomare_PRIGHT, Telomare_TRACE}; 
        //No more nodes create.
        if(nodes_left == 0){
            return;
        //Only the leaf to create
        } else if(nodes_left == 1){
            type  = *rc::gen::elementOf(leafs);
            value = nullptr;
            return; 
        } else if(nodes_left == 2){
            type = *rc::gen::elementOf(non_pair);
        } else {
            type = *rc::gen::elementOf(nodes);
        }
        nodes_left--;
        switch(type){
            case Telomare_PAIR:{
                unsigned long nodes_right = *rc::gen::inRange((unsigned long)1,nodes_left);
                Telomare_Pair * node = new Telomare_Pair();
                value = node;
                huh(node->left_type, node->left_value, nodes_left-nodes_right);
                huh(node->right_type, node->right_value, nodes_right);
                } break;
            case Telomare_SETENV:{
                Telomare_SetEnv * node = new Telomare_SetEnv();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case Telomare_DEFER:{
                Telomare_Defer * node = new Telomare_Defer();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case Telomare_TWIDDLE:{
                Telomare_Twiddle * node = new Telomare_Twiddle();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case Telomare_ABORT:{
                Telomare_Abort * node = new Telomare_Abort();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case Telomare_GATE:{
                Telomare_Gate * node = new Telomare_Gate();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case Telomare_PLEFT:{
                Telomare_PLeft * node = new Telomare_PLeft();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case Telomare_PRIGHT:{
                Telomare_PRight * node = new Telomare_PRight();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case Telomare_TRACE:{
                Telomare_Trace * node = new Telomare_Trace();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
        }
    };

    //Generates AST.
    auto genAST = [&](unsigned long size){
        Telomare_Root ret;
        huh(ret.type, ret.value, size);
        return ret;
    };

    rc::check("can generate tree of specified size",
        [&]() {
            unsigned long size = *rc::gen::inRange(1,1000);
            Telomare_Root root = genAST(size);
            unsigned long ast_size = telomare_count(&root);
            bool ok = ast_size == size;
            if(!ok){
                cerr << ast_size << " vs " << size << endl;
                cerr << (int)root.type << " and " << root.value << endl;
                Telomare_Serialized * serialized = telomare_serialize(&root);
                for(unsigned int i = 0; i < serialized->size; i++){
                    cerr << (int)serialized->storage[i] << " ";
                }
                cerr << endl;
            }
            return ok;
        });
    
    rc::check("the tree is equal to itself",
        [&]() {
            unsigned long size = *rc::gen::inRange(1,1000);
            Telomare_Root root = genAST(size);
            bool ok = telomare_equal(&root, &root);
            if(!ok){
                Telomare_Serialized * serialized = telomare_serialize(&root);
                for(unsigned int i = 0; i < serialized->size; i++){
                    cerr << (int)serialized->storage[i] << " ";
                }
                cerr << endl;
            }
            return ok;
        });
    rc::check("the tree is not equal to any tree of other size",
        [&]() {
            unsigned long size1 = *rc::gen::inRange(1,1000);
            unsigned long size2 = *rc::gen::suchThat(rc::gen::inRange(1,1000),[&](unsigned long x){
                            return x != size1;});
            Telomare_Root root1 = genAST(size1);
            Telomare_Root root2 = genAST(size2);
            bool ok = !telomare_equal(&root1, &root2);
            if(!ok){
                Telomare_Serialized * serialized1 = telomare_serialize(&root1);
                Telomare_Serialized * serialized2 = telomare_serialize(&root2);
                for(unsigned int i = 0; i < serialized1->size; i++){
                    cerr << (int)serialized1->storage[i] << " ";
                }
                cerr << endl;
                for(unsigned int i = 0; i < serialized2->size; i++){
                    cerr << (int)serialized2->storage[i] << " ";
                }
                cerr << endl;
            }
            return ok;
        });
    rc::check("(serializing -> deserializing) => equal pre-serialized and deserialized versions",
        [&]() {
            unsigned long        size = *rc::gen::inRange(1,1000);
            Telomare_Root             root = genAST(size);
            Telomare_Serialized * serialized = telomare_serialize(&root);
            Telomare_Root    *deserialized = telomare_deserialize(serialized);
            bool ok = telomare_equal(&root, deserialized);
            if(!ok){
                cerr << "Size: " << size << endl;
                for(unsigned int i = 0; i < serialized->size; i++){
                    cerr << (int)serialized->storage[i] << " ";
                }
                cerr << endl;
            }
            return ok;
        });
    rc::check("(serializing -> deserializing -> serializing) => equal serializations",
        [&]() {
            unsigned long        size = *rc::gen::inRange(1,1000);
            Telomare_Root             root = genAST(size);
            Telomare_Serialized * serialized = telomare_serialize(&root);
            Telomare_Root    *deserialized = telomare_deserialize(serialized);
            Telomare_Serialized * serialized2 = telomare_serialize(deserialized);

            bool ok = serialized->size == serialized2->size;
            for(unsigned long i = 0; i < serialized->size && ok; i++){
               ok = serialized->storage[i] == serialized2->storage[i]; 
            }
            if(!ok){
                cerr << "Size: " << size << endl;
                for(unsigned int i = 0; i < serialized->size; i++){
                    cerr << (int)serialized->storage[i] << " ";
                }
                cerr << " vs ";
                for(unsigned int i = 0; i < serialized2->size; i++){
                    cerr << (int)serialized2->storage[i] << " ";
                }
                cerr << endl;
            }
            return ok;
        });
}
