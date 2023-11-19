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

void printset(const std::set<int> &input)
{
  for (auto &inp : input){
    errs() << inp << " ";
  }
}

set<int> getOutSet(const std::set<int>& gen, const std::set<int>& in, const std::set<int>& kill)
{
  std::set<int> resultset; 
  std::set<int> temp; 

  std::set_difference(in.begin(), in.end(), kill.begin() , kill.end(), std::inserter(temp, temp.begin()));
  std::set_union(gen.begin(), gen.end(), temp.begin(), temp.end(), std::inserter(resultset, resultset.begin()));

  return resultset;
  
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
map<Value*, int> get_latest_definition(BasicBlock *bb, map<BasicBlock* ,  map<Value*, int>>& L_DEF)
{
  map<Value*, int> result ; 
  
}


namespace
{

struct ReachingDefinition : public FunctionPass
{
  static char ID;
  ReachingDefinition() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override
  {
    errs() << "ReachingDefinition: ";
    errs() << F.getName() << "\n";

    /* Global GEN and KILL set */
    map<BasicBlock* , set<int>> GEN, KILL, IN, OUT;  

    /* Maintain a map of values of their latest definition */ 
    map<BasicBlock* ,  map<Value*, int>> L_DEF; 
    /* index */
    int i = 0; 

    /* for each basic block find the variables that enter and exit the basic block */
    for (auto &basic_block : F)
    {
            
      /* display the name of each basic block */
      errs() << "-----" << basic_block.getName() << "-----" << "\n";

      /* Sets for Reaching definition, should be processed for each block  */
      std::set<int> gen ; 
      std::set<int> kill;
      std::set<int> in; 
      std::set<int> out; 
      map<Value*, int> latest_definition;

      if (basic_block.getName() != "entry")
      {
        in = union_of_pred(&basic_block, OUT);
        /* get the latest definition */
        latest_definition = get_latest_definition(&basic_block, L_DEF);
      }

      for (auto &inst : basic_block)
      {
        /* read instructions */
        errs() << i << ":"<< inst << "\n";
        if (inst.getOpcode() == Instruction::Store){

          /* check the what the operand is ??*/
          StoreInst *store_instruction = dyn_cast<StoreInst>(&inst);
          if (store_instruction)
          {
            Value *var = store_instruction->getPointerOperand();
            
            /* if we find a definition */
            if ((latest_definition.find(var) != latest_definition.end()) || (in.find(latest_definition[var]) != in.end()))
            {
              kill.insert(latest_definition[var]);
              gen.erase(latest_definition[var]);
            } 
            latest_definition[var] = i ; 
            gen.insert(latest_definition[var]);
          }

          /* add to kill set if previous definition is killed */
          
        }
        i++;
      }

      errs() << "IN:" << "\n";
      printset(in);
      errs() << "GEN:" << "\n";
      printset(gen);
      errs() << "KILL:" << "\n";
      printset(kill);

      L_DEF[&basic_block] = latest_definition; 
      IN[&basic_block] = in;
    
      /* add the basic blocks GEN set and KILL set */
      GEN[&basic_block] = gen; 
      KILL[&basic_block] = kill; 

      /* OUT[B] = GEN[B] U (IN[B] - KILL[B])*/
      OUT[&basic_block] = getOutSet(GEN[&basic_block], IN[&basic_block], KILL[&basic_block]);
      errs() << "OUT:" << "\n";
      printset(OUT[&basic_block]);

    }

    return true;
  }
}; // end of struct ReachingDefinition
} // end of anonymous namespace

char ReachingDefinition::ID = 0;
static RegisterPass<ReachingDefinition> X("ReachingDefinition", "Reaching Definition Pass",
                                      false /* Only looks at CFG */,
                                      true /* Analysis Pass */);
