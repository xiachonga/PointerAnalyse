/************************************************************************
 *
 * @file Dataflow.h
 *
 * General dataflow framework
 *
 ***********************************************************************/

#ifndef _DATAFLOW_H_
#define _DATAFLOW_H_

#include <llvm/Support/raw_ostream.h>
#include <map>
#include <set>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Function.h>

using namespace llvm;

//#define DEBUG
///Base dataflow visitor class, defines the dataflow function

template <class T>
class DataflowVisitor {
public:
    virtual ~DataflowVisitor() { }

    /// Dataflow Function invoked for each basic block 
    /// 
    /// @block the Basic Block
    /// @dfval the input dataflow value
    /// @isforward true to compute dfval forward, otherwise backward
    virtual void compDFVal(BasicBlock *block, T *dfval, bool isforward) {
        if (isforward == true) {
           for (BasicBlock::iterator ii=block->begin(), ie=block->end(); ii!=ie; ++ii) {
                Instruction * inst = &*ii;
                compDFVal(inst, dfval);
           }
        } else {
           for (BasicBlock::reverse_iterator ii=block->rbegin(), ie=block->rend(); ii != ie; ++ii) {
                Instruction * inst = &*ii;
                compDFVal(inst, dfval);
           }
        }
    }

    ///
    /// Dataflow Function invoked for each instruction
    ///
    /// @inst the Instruction
    /// @dfval the input dataflow value
    /// @return true if dfval changed
    virtual void compDFVal(Instruction *inst, T *dfval ) = 0;

    ///
    /// Merge of two dfvals, dest will be ther merged result
    /// @return true if dest changed
    ///
    virtual void merge( T *dest, const T &src ) = 0;
};

///
/// Dummy class to provide a typedef for the detailed result set
/// For each basicblock, we compute its input dataflow val and its output dataflow val
///
template<class T>
struct DataflowResult {
    typedef typename std::map<BasicBlock *, std::pair<T, T> > Type;
};

/// 
/// Compute a forward iterated fixedpoint dataflow function, using a user-supplied
/// visitor function. Note that the caller must ensure that the function is
/// in fact a monotone function, as otherwise the fixedpoint may not terminate.
/// 
/// @param fn The function
/// @param visitor A function to compute dataflow vals
/// @param result The results of the dataflow 
/// @initval the Initial dataflow value
template<class T>
void compForwardDataflow(Function *fn,
    DataflowVisitor<T> *visitor,
    typename DataflowResult<T>::Type *result,
    const T & initval) {
    T initNull;
    std::set<BasicBlock *> workList;
    for(Function::iterator bi = fn->begin(); bi != fn->end(); ++bi) {
        BasicBlock* bb = &*bi;
        result->insert(std::make_pair(bb, std::make_pair(initNull, initNull)));
        workList.insert(bb);
        for (BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
            if (Instruction* instruction = dyn_cast<Instruction>(inst)) {
                std::set<Value*> nullSet = {};
                (*result)[bb].first.PointToSet.insert(std::make_pair(instruction, nullSet));   
            }
        }
    }
    result->insert(std::make_pair(&*fn->begin(), std::make_pair(initval, initNull)));    
    while(!workList.empty()) {
        BasicBlock *bb = *workList.begin();
        workList.erase(workList.begin());
        // Merge all incoming value
        T bbEnterVal = (*result)[bb].first;
        for (auto si = pred_begin(bb), se = pred_end(bb); si != se; si++) {
            BasicBlock *pred = *si;
            visitor->merge(&bbEnterVal, (*result)[pred].second); //result[bb].first意思是基本块bb的入口，result[bb].second意思是基本块bb的出口
        }

        (*result)[bb].first = bbEnterVal;
        visitor->compDFVal(bb, &bbEnterVal, true); //compDFVal计算当前基本块对数据流集合的影响

        // If outgoing value changed, propagate it along the CFG
        if (bbEnterVal == (*result)[bb].second) continue; 
        (*result)[bb].second = bbEnterVal;

        for (succ_iterator pi = succ_begin(bb), pe = succ_end(bb); pi != pe; pi++) {  //把他的每个后继基本块合加入worklist重新计算
            workList.insert(*pi);
        }

    }

    return;
}
/// 
/// Compute a backward iterated fixedpoint dataflow function, using a user-supplied
/// visitor function. Note that the caller must ensure that the function is
/// in fact a monotone function, as otherwise the fixedpoint may not terminate.
/// 
/// @param fn The function
/// @param visitor A function to compute dataflow vals
/// @param result The results of the dataflow 
/// @initval The initial dataflow value
template<class T>
void compBackwardDataflow(Function *fn,
    DataflowVisitor<T> *visitor,
    typename DataflowResult<T>::Type *result,
    const T &initval) {

    std::set<BasicBlock *> worklist;

    // Initialize the worklist with all exit blocks
    for (Function::iterator bi = fn->begin(); bi != fn->end(); ++bi) {
        BasicBlock * bb = &*bi;
        result->insert(std::make_pair(bb, std::make_pair(initval, initval)));
        worklist.insert(bb);
        printf("=======================\n");
        bb->dump();
        printf("=======================\n");
    }

    // Iteratively compute the dataflow result
    while (!worklist.empty()) {
        BasicBlock *bb = *worklist.begin();
        worklist.erase(worklist.begin());

        // Merge all incoming value
        T bbexitval = (*result)[bb].second;
        for (auto si = succ_begin(bb), se = succ_end(bb); si != se; si++) {
            BasicBlock *succ = *si;
            visitor->merge(&bbexitval, (*result)[succ].first); //result[bb].first意思是基本块bb的入口，result[bb].second意思是基本块bb的出口
        }

        (*result)[bb].second = bbexitval;
        visitor->compDFVal(bb, &bbexitval, false); //compDFVal计算当前基本块对数据流集合的影响

        // If outgoing value changed, propagate it along the CFG
        if (bbexitval == (*result)[bb].first) continue; //
        (*result)[bb].first = bbexitval;

        for (pred_iterator pi = pred_begin(bb), pe = pred_end(bb); pi != pe; pi++) {  //把他的每个前驱基本快合加入worklist重新计算
            worklist.insert(*pi);
        }
    }
}

template<class T>
void printDataflowResult(raw_ostream &out,
                         const typename DataflowResult<T>::Type &dfresult) {
    for ( typename DataflowResult<T>::Type::const_iterator it = dfresult.begin();
            it != dfresult.end(); ++it ) {
        if (it->first == NULL) out << "*";
        else it->first->dump();
        out << "\n\tin : "
            << it->second.first 
            << "\n\tout :  "
            << it->second.second
            << "\n";
    }
}







#endif /* !_DATAFLOW_H_ */
