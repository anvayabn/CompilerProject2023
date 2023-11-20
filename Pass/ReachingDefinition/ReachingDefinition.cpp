#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <string>
#include <fstream>
#include <unordered_map>
#include <set>
#include <queue>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "ReachingDefinition"

void print_set(std::set<int>& st, std::string type){
  errs() << type << ": ";
  for (auto &i : st){
    errs() << i << " ";
  }
  errs() << "\n";
}

void print_instruction_blocks_with_index(std::map<int , llvm::Instruction*>& all_ins, Function& F)
{
    for (auto &basic_block : F)
    {
      errs() << "-----" << basic_block.getName() << "-----" << "\n";

      for (auto &i : all_ins){
        llvm::Instruction* inst = i.second;
        int ind = i.first;
        
        /* Print instructions belonging to this block */
        if (inst->getParent() == &basic_block){
          errs() << ind << ":" << *inst << "\n";
        } 
      }
    }
}

set<int> union_of_pred(BasicBlock *bb, map<BasicBlock* , set<int>>& OUT)
{
  std::set<int> result;

  /* get the predecessors */
  for (auto PI = pred_begin(bb), E = pred_end(bb); PI != E; ++PI)
  {
    BasicBlock *pred = *PI; 
    set<int> out = OUT[pred]; 
    std::set_union(result.begin(), result.end(), out.begin(), out.end(), std::inserter(result, result.begin()));

  }

  return result; 
}

set<int> getOutSet(const std::set<int>& gen, const std::set<int>& in, const std::set<int>& kill)
{
  std::set<int> resultset; 
  std::set<int> temp; 

  std::set_difference(in.begin(), in.end(), kill.begin() , kill.end(), std::inserter(temp, temp.begin()));
  std::set_union(gen.begin(), gen.end(), temp.begin(), temp.end(), std::inserter(resultset, resultset.begin()));

  return resultset;
  
}

namespace
{

struct ReachingDefinition : public FunctionPass
{
  static char ID;
  ReachingDefinition() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override
  {
    errs() << "ReachingDefinition: By Anvaya and Arnav : Compiler Construction Phase-II: ";
    errs() << F.getName() << "\n";

    /* Retrive Information of the instruction from the IR */

    /* Data Structures to hold the data 
      all_ins - map of index to instruction 
      def_of_var - map between varname 
                  (string) and vector of all the indexes var is defined 
      latest_defs_in_block - map of Block to (map <string to index>)                   
    */
    std::map<int, llvm::Instruction*> all_ins; 
    // std::map<llvm::BasicBlock*, map<std::string, std::set<int>>> def_of_var_block;
    std::map<llvm::BasicBlock*, std::map<std::string, int>> latest_def_in_block;

    /* Index */
    int i = 0 ; 

    for (auto &basic_block : F)
    { 

      std::map<std::string, int> l_def; 
      std:: map<std::string, std::set<int>> def_of_var;
      for (auto &inst : basic_block)
      {
        /* add each instruction to all_ins */
        all_ins[ i ] = &inst;

        /* If instruction is store operation */
        if (inst.getOpcode() == Instruction::Store){

          StoreInst *store_instruction = dyn_cast<StoreInst>(&inst); 
          if (store_instruction){
              
              /* add to def_of_var */
              if (store_instruction->getPointerOperand() -> hasName()){
                std::string var_name = store_instruction->getPointerOperand() ->getName().str();

                // if (def_of_var.find(var_name) != def_of_var.end()){
                //   std::set<int> temp; 
                //   def_of_var[var_name] = temp;
                // }
                // def_of_var[var_name].insert(i);

                // def_of_var_block[ &basic_block ] =  def_of_var; 

                /* add the latest definitions in the block */
                l_def [var_name] = i ;

              }
          }
        }
        i++;
      }

      /* add to global latest def */
      latest_def_in_block [&basic_block] = l_def; 

    }

    /* Print the instrctions with its index and  */
    //DEBUG Print 
    // print_instruction_blocks_with_index(all_ins, F);

    /* Global GEN, KILL , IN, OUT sets*/
    std::map<llvm::BasicBlock*, set<int>> IN; 
    std::map<llvm::BasicBlock*, set<int>> OUT; 
    std::map<llvm::BasicBlock*, set<int>> GEN; 
    std::map<llvm::BasicBlock*, set<int>> KILL; 

    /* reinitialise the index */
    i = 0 ; 
    for (auto &basic_block : F)
    {
      /* kill gen set for each block */
      std::set<int> gen; 
      std::set<int> kill; 
      std::set<int> in;
      std::set<int> out;
      
      std::map<std::string, int> temp_ldef = latest_def_in_block [ &basic_block ]; 

      /* Gen Set : definitions within Basic Block (B) that reach the end of B 

      */
      for (auto &inst : basic_block)
      {

        /* create Gen Set for store operations */
        if (inst.getOpcode() == Instruction::Store){

          StoreInst *store_instruction = dyn_cast<StoreInst>(&inst); 
          if (store_instruction){
            if (store_instruction->getPointerOperand() -> hasName()){
                std::string var_name = store_instruction->getPointerOperand() ->getName().str();
                
                /* Only add definitions that reach */
                if(temp_ldef.find(var_name) != temp_ldef.end()){
                  gen.insert(temp_ldef[var_name]); 

                  /* if the index of the varname is different add to kill set */
                  if (i != temp_ldef[var_name]){
                    kill.insert(i); 
                  }
                } 

                /* Other additions to Kill Set */
                /* what are all the defintions found in the predecessors */
                for (auto PI = pred_begin(&basic_block), E = pred_end(&basic_block); PI != E; ++PI) {
                    BasicBlock *Pred = *PI;
                    std::map<std::string, int> temp_prev_ldef =  latest_def_in_block [ Pred ]; 

                    if ((temp_prev_ldef.find(var_name) != temp_prev_ldef.end()) &&
                         (gen.find(temp_ldef[var_name]) != gen.end())){

                          kill.insert(temp_prev_ldef[var_name]); 
                    }
                }
            }    

          }

        }
        i++; 
      }
      /* add to global set */
      GEN [ &basic_block ] = gen; 
      KILL [ &basic_block ] = kill;
    }    

    /* compute and print Reaching definition sets */
    /* reinitialise the index */
    i = 0 ; 
    for (auto &basic_block : F){

      /* if entry block IN[B] = null */
      if (basic_block.getName() == "entry"){
        std::set<int> nullset; 
        IN [ &basic_block ] = nullset; 
      }else{
        IN [ &basic_block ] = union_of_pred(&basic_block, OUT); 
      }

      OUT[ &basic_block ] = getOutSet(GEN [&basic_block], IN[ &basic_block ], KILL[ &basic_block]); 

      /* Print to Console or whatever */
      errs() << "-----" << basic_block.getName() << "-----" << "\n";

      print_set(GEN[&basic_block], "GEN");
      print_set(KILL[&basic_block], "KILL");
      print_set(IN[&basic_block], "IN");
      print_set(OUT[ &basic_block], "OUT");

    }

    return true;
  }
}; // end of struct ReachingDefinition
}// end of anonymous namespace

char ReachingDefinition::ID = 0;
static RegisterPass<ReachingDefinition> X("ReachingDefinition", "Reaching Definition Pass",
                                      false /* Only looks at CFG */,
                                      true /* Analysis Pass */);
