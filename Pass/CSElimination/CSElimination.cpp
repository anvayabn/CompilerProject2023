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

#define DEBUG_TYPE "CSElimination"



namespace
{

std::map<llvm::BasicBlock*,map<int, llvm::Instruction*>> global_inst_map;
std::map<llvm::BasicBlock*,map<int, llvm::Instruction*>> global_inst_op_map;
std::map<llvm::BasicBlock*,map<int, llvm::Instruction*>> global_inst_stor_map;
std::map<llvm::BasicBlock*,map<int, llvm::Instruction*>> global_inst_load_map;
std::map<llvm::Value*, std::string> valueToStringMap;

std::vector<llvm::BasicBlock*> get_pred_blocks(llvm::BasicBlock *block) {
    std::vector<llvm::BasicBlock*> predecessors;

    if (block == nullptr) {
        return predecessors; 
    }

    for (auto it = llvm::pred_begin(block), et = llvm::pred_end(block); it != et; ++it) {
        llvm::BasicBlock *predBlock = *it;
        predecessors.push_back(predBlock);
    }

    return predecessors;
}

bool available_at_entry(llvm::BasicBlock* bb, int index){

  /* get the instructions and operands */
  std::map<int, llvm::Instruction*> temp1 = global_inst_op_map[ bb ];
  llvm::Instruction* temp_inst = temp1[ index ];
  

  bool toggle = true;

  if (llvm::isa<llvm::BinaryOperator>(temp_inst)){
    llvm::Value* operand1 = temp_inst->getOperand(0);

    // errs() << "operand1" << operand1 << "\n";
    llvm::Value*  operand2 = temp_inst->getOperand(1); 
    // errs() << "operand2" << operand2 << "\n";

    /* check if previous block has any computation of the same instruction */
    std::vector<llvm::BasicBlock*> prevblocks = get_pred_blocks(bb);
    /* for each instruction in previous blocks 
       check if the instrcutions has the same operands and operator */
    
    if (prevblocks.size() != 0 ){
      /* for each prev block check if there is the same computation say B op C*/
      for ( int i = 0 ; i < prevblocks.size(); i++){

        std::map<int, llvm::Instruction*> temp2 = global_inst_op_map[ prevblocks[i] ];
        bool match_found_in_this_block = false;

        /* each operation instruction */
        for ( const auto &pair : temp2 ){
          int key = pair.first;

          llvm::Instruction* prev_temp_inst = pair.second;

          if (prev_temp_inst->isSameOperationAs(temp_inst)){
            llvm::Value* prev_op1 = prev_temp_inst->getOperand(0);
            llvm::Value* prev_op2 = prev_temp_inst->getOperand(1);

            if ((operand1 == prev_op1 && operand2 == prev_op2) ||
              (operand1 == prev_op2 && operand2 == prev_op1)){
              match_found_in_this_block = true ;
            }
          }
        }
        if (!match_found_in_this_block){
          toggle = false;
        }
      }
      
    }
  }
  return toggle;

}

bool not_redefined_bef_S(llvm::BasicBlock* bb, int index){
  /* get the instructions and operands */
  std::map<int, llvm::Instruction*> temp1 = global_inst_op_map[ bb ];
  llvm::Instruction* temp_inst = temp1[ index ];
  if (llvm::isa<llvm::BinaryOperator>(temp_inst)){
    /* check if any of the operand is redefined before our instruction */
    auto operand1 = dyn_cast<User>(temp_inst)->getOperand(0); 
    llvm::Value* operand2 = temp_inst->getOperand(1); 
    
    
    /* check if any of the operands are redefined bfore S */
    /* get all store instructions in our basic block */
    std::map<int, llvm::Instruction*> temp2 = global_inst_stor_map[ bb ];

    for ( auto &pair : temp2 ){
      int key = pair.first;
      if (key < index){
        llvm::Instruction* temp_inst_load = pair.second;
        StoreInst *store_instruction = dyn_cast<StoreInst>(temp_inst_load); 
        llvm::Value* definition = store_instruction->getPointerOperand();

        if (definition == operand1 || definition == operand2){
          return false; 
        }    
      }
    }

  }else{
    return false; 
  }

  return true; 

}
std::vector<int> defs_that_reach_s(llvm::BasicBlock* bb, int index){

  vector<int> result;
  std::map<int, llvm::Instruction*> temp1 = global_inst_op_map[ bb ];
  llvm::Instruction* temp_inst = temp1[ index ];

  if (llvm::isa<llvm::BinaryOperator>(temp_inst)){
    /* check if any of the operand is redefined before our instruction */
   llvm::Value*  operand1 = temp_inst->getOperand(0); 
   llvm::Value*  operand2 = temp_inst->getOperand(1); 


    std::vector<llvm::BasicBlock*> prevblocks = get_pred_blocks(bb);
    if (prevblocks.size() != 0 ){
      for ( int i = 0 ; i < prevblocks.size(); i++){
        std::map<int, llvm::Instruction*> temp2 = global_inst_op_map[ prevblocks[i] ];
        for ( const auto &pair : temp2 ){
          int key = pair.first;

          llvm::Instruction* prev_temp_inst = pair.second;

          if (prev_temp_inst->isSameOperationAs(temp_inst)){
            llvm::Value*  prev_op1 = prev_temp_inst->getOperand(0);
            llvm::Value*  prev_op2 = prev_temp_inst->getOperand(1);

            if ((operand1 == prev_op1 && operand2 == prev_op2) ||
              (operand1 == prev_op2 && operand2 == prev_op1)){
                result.push_back(key); 
            }
          }
        }        
      }  
    }
  }
  return result;
}

void replace_each_statement(std::vector<int>& def, std::string& t, llvm::BasicBlock* bb) {
    for (int index : def) {
        llvm::Instruction* inst = global_inst_op_map[bb][index];
        // Create a new temporary variable
        IRBuilder<> Builder(bb);
        AllocaInst* tempVar = Builder.CreateAlloca(inst->getType(), nullptr, t);

        /* Replace the instruction with a store to the temporary variable */
        StoreInst* storeInst = new StoreInst(inst, tempVar, false, inst);
        ReplaceInstWithInst(inst, storeInst);

        // Replace all uses of the original instruction with the temporary variable
        for (auto& U : inst->uses()) {
            User* user = U.getUser();
            user->setOperand(U.getOperandNo(), tempVar);
        }
    }
} 

void printGlobalMap(const std::map<llvm::BasicBlock*, std::map<int, llvm::Instruction*>>& globalMap) {
    for (const auto& blockMapPair : globalMap) {
        const llvm::BasicBlock* block = blockMapPair.first;
        const std::map<int, llvm::Instruction*>& instMap = blockMapPair.second;

        std::string blockName = (block->hasName()) ? block->getName().str() : "unnamed";
        llvm::errs() << "Basic Block: " << blockName << "\n";

        for (const auto& instPair : instMap) {
            int index = instPair.first;
            llvm::Instruction* inst = instPair.second;

            std::string instStr;
            llvm::raw_string_ostream rso(instStr);
            inst->print(rso);

            llvm::errs() << "  Index: " << index << ", Instruction: " << instStr << "\n";
        }
        llvm::errs() << "\n";
    }
}



struct CSElimination : public FunctionPass
{
  static char ID;
  CSElimination() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override
  {
    errs() << "CSE Elimination: By Anvaya and Arnav : Compiler Construction Phase-III: ";
    errs() << F.getName() << "\n";

    /* just collect all the information here */
    int i = 0 ;
    for (auto &basic_block : F){

      /* map <index, inst> */
      std::map<int, llvm::Instruction*> inst_map;
      std::map<int, llvm::Instruction*> inst_op_map;
      std::map<int, llvm::Instruction*> inst_stor_map;
      std::map<int, llvm::Instruction*> inst_load_map;

      for (auto &inst : basic_block){
        /* insert all instructions to this map */
        inst_map[ i ] = &inst;

        /* if instruction is a operation store in */
        if (llvm::isa<llvm::BinaryOperator>(inst)){

          /* add to inst op map*/
          inst_op_map[ i ] = &inst; 
        
        }else if (llvm::isa<llvm::StoreInst>(inst)){

          /* add to store map*/
          inst_stor_map[ i ] = &inst; 
        
        }else if (llvm::isa<llvm::LoadInst>(inst)){
          /* add to load map*/
          inst_load_map[ i ] = &inst;
        }
        
        i++;
      }

      /* insert the inst_map to global basic block instruction map */
      global_inst_map[ &basic_block ] = inst_map; 
      global_inst_op_map[ &basic_block ] = inst_op_map;
      global_inst_stor_map[ &basic_block ] = inst_stor_map;
      global_inst_load_map[ &basic_block ] = inst_load_map;
    }
    
    // F.print(errs());

    /* CS Elimination algorithm */

    /* index */
    i = 0 ; 
    /* for each block */
    for (auto &basic_block : F){


      for (auto &inst : basic_block){
        /* if the statement is a operation such as S:A = (B OP C )*/
        if (llvm::isa<llvm::BinaryOperator>(inst)){
          /* if BOP is available at entry of this BB */
          bool avai = available_at_entry(&basic_block, i); 
          /* get the operands' name and the operation */
          bool nr = not_redefined_bef_S(&basic_block, i); 

          if (avai && nr ){
            std::vector<int> def = defs_that_reach_s(&basic_block, i);

            /* create a temporary var */
            std::string t = "t";

            /* replace each statement D = B OP C */
            replace_each_statement(def, t, &basic_block); 

            /* replace the right hand */
            // replace_right_hand_side(t); 

          }
          
        }
        i++; 
      }
    }    
    F.print(errs());
    return true; // Indicate this is a Transform pass
  }
}; // end of struct CSElimination
} // end of anonymous namespace

char CSElimination::ID = 0;
static RegisterPass<CSElimination> X("CSElimination", "CSElimination Pass",
                                      false /* Only looks at CFG */,
                                      true /* Tranform Pass */);
