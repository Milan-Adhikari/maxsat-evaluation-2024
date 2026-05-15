#include "Solver.h"
#define myFalse 0
#define myTrue 1
#define myNone -1

bool Solver::checkClauses(vec<CRef>& cs) {
  vec<int> myValue;
  myValue.growTo(nVars());

  for(int i=0; i<nVars(); i++)
    if (value(i)==l_True)
      myValue[i]=myTrue;
    else if (value(i)==l_False)
      myValue[i]=myFalse;
    else   myValue[i]=myNone;

  myValue[216399]=myTrue;
  myValue[188037]=myTrue;
  myValue[90431]=myTrue;
  myValue[76210]=myTrue;
  myValue[178269]=myTrue;
  myValue[202808]=myTrue;
  myValue[113833]=myTrue;
  myValue[135397]=myTrue;
               
  bool toRepeat=false;
  do {
    toRepeat=false;
    for(int i=0; i<cs.size(); i++) {
      Clause& c=ca[cs[i]];
      if (c.mark()==1)
        continue;
      Lit p=lit_Undef;
      bool sat=false;
      bool unit=true;
      for(int j=0; j<c.size(); j++) {
        if (myValue[var(c[j])] == myNone) {
          if (p==lit_Undef)
            p=c[j];
          else {
            unit=false;
            break;
          }
        }
        else if (myValue[var(c[j])]^sign(c[j])==myTrue) {
          sat=true;
          break;
        }
      }
      if (!sat) {
        if (p == lit_Undef)
          return false;
        else if (unit) {
          toRepeat=true;
          myValue[var(p)] = !sign(p);
        }
      }
    }
  } while(toRepeat);
  return true;
}

bool Solver::checkHardenheapOrder(int i)
{
  Heap<VarOrderWeightDec>& myHeap=hardenHeap;
  if (2*i+1 < myHeap.size() && (weights[myHeap[i]] < weights[myHeap[2*i+1]] || !checkHardenheapOrder(2*i+1)))
    return false;
  if (2*i+2 < myHeap.size() && (weights[myHeap[i]] < weights[myHeap[2*i+2]] || !checkHardenheapOrder(2*i+2)))
    return false;
  return true;
}     
