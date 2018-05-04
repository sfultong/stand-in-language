#include <rapidcheck.h>
#include <iostream>
#include <vector>
#include <tuple>
#include <functional>

#include "SIL.h"

using namespace std;


bool unit_tests(){
   SIL_Root root;
   SIL_Pair pair;
   SIL_Zero zero;
   SIL_SetEnv setenv;
   SIL_Env  env;

   root.type = SIL_PAIR;
   root.value = &pair;

   pair.left_type   = SIL_SETENV;
   pair.left_value  = &setenv;
   pair.right_type  = SIL_ZERO;
   pair.right_value = &zero;

   setenv.type  = SIL_ENV;
   setenv.value = 0;

   unsigned long no_nodes  = sil_count(&root);
   unsigned long no_nodes2 = sil_count_old(&root);
   printf("%d %d\n",no_nodes, no_nodes2);

   unsigned char eq = sil_equal(&root,&root);
   printf("equality: %d\n", eq);

   SIL_Serialized * serialized = sil_serialize(&root);
   for(int i = 0; i < serialized->size; i++){
        printf("%d ",serialized->storage[i]);
   }
   printf("\n");
   serialized->storage[1] = SIL_ZERO;
   serialized->size =2;
   //serialized.storage[2] = SIL_ZERO;
   //serialized.storage[3] = SIL_ENV;
   SIL_Root * deserialized = sil_deserialize(serialized);

   printf("Is serialized and deserialized tree okay: %d\n", sil_equal(&root,deserialized));
   SIL_Serialized * serialized2 = sil_serialize(deserialized);
   for(int i = 0; i < serialized2->size; i++){
        printf("%d ",serialized2->storage[i]);
   }
   printf("\n");

}



int main(){
    //@TODO Learn how to build generators.
    using NodeGenFn = function<void(sil_type&, void*&, unsigned long)>;
    NodeGenFn huh = [&](sil_type &type, void *& value, unsigned long nodes_left){
        const vector<sil_type> leafs = {SIL_ZERO, SIL_ENV}; 
        const vector<sil_type> nodes = {SIL_PAIR, SIL_SETENV,SIL_DEFER, SIL_TWIDDLE, SIL_ABORT
                                       ,SIL_GATE, SIL_PLEFT, SIL_PRIGHT, SIL_TRACE}; 
        const vector<sil_type> non_pair = {SIL_SETENV,SIL_DEFER, SIL_TWIDDLE, SIL_ABORT
                                          ,SIL_GATE, SIL_PLEFT, SIL_PRIGHT, SIL_TRACE}; 
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
            case SIL_PAIR:{
                unsigned long nodes_right = *rc::gen::inRange((unsigned long)1,nodes_left);
                SIL_Pair * node = new SIL_Pair();
                value = node;
                huh(node->left_type, node->left_value, nodes_left-nodes_right);
                huh(node->right_type, node->right_value, nodes_right);
                } break;
            case SIL_SETENV:{
                SIL_SetEnv * node = new SIL_SetEnv();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case SIL_DEFER:{
                SIL_Defer * node = new SIL_Defer();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case SIL_TWIDDLE:{
                SIL_Twiddle * node = new SIL_Twiddle();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case SIL_ABORT:{
                SIL_Abort * node = new SIL_Abort();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case SIL_GATE:{
                SIL_Gate * node = new SIL_Gate();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case SIL_PLEFT:{
                SIL_PLeft * node = new SIL_PLeft();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case SIL_PRIGHT:{
                SIL_PRight * node = new SIL_PRight();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
            case SIL_TRACE:{
                SIL_Trace * node = new SIL_Trace();
                value = node;
                huh(node->type, node->value, nodes_left);
                }break;
        }
    };

    //Generates AST.
    auto genAST = [&](unsigned long size){
        SIL_Root ret;
        huh(ret.type, ret.value, size);
        return ret;
    };

    rc::check("can generate tree of specified size",
        [&]() {
            unsigned long size = *rc::gen::inRange(1,1000);
            SIL_Root root = genAST(size);
            unsigned long ast_size = sil_count(&root);
            bool ok = ast_size == size;
            if(!ok){
                cerr << ast_size << " vs " << size << endl;
                cerr << (int)root.type << " and " << root.value << endl;
                SIL_Serialized * serialized = sil_serialize(&root);
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
            SIL_Root root = genAST(size);
            bool ok = sil_equal(&root, &root);
            if(!ok){
                SIL_Serialized * serialized = sil_serialize(&root);
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
            SIL_Root root1 = genAST(size1);
            SIL_Root root2 = genAST(size2);
            bool ok = !sil_equal(&root1, &root2);
            if(!ok){
                SIL_Serialized * serialized1 = sil_serialize(&root1);
                SIL_Serialized * serialized2 = sil_serialize(&root2);
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
            SIL_Root             root = genAST(size);
            SIL_Serialized * serialized = sil_serialize(&root);
            SIL_Root    *deserialized = sil_deserialize(serialized);
            bool ok = sil_equal(&root, deserialized);
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
            SIL_Root             root = genAST(size);
            SIL_Serialized * serialized = sil_serialize(&root);
            SIL_Root    *deserialized = sil_deserialize(serialized);
            SIL_Serialized * serialized2 = sil_serialize(deserialized);

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
