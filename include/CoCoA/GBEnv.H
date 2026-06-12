#ifndef CoCoA_GBEnv_H
#define CoCoA_GBEnv_H

//   Copyright (c)  2010  Anna Bigatti, Massimo Caboara

//   This file is part of the source of CoCoALib, the CoCoA Library.
//
//   CoCoALib is free software: you can redistribute it and/or modify
//   it under the terms of the GNU General Public License as published by
//   the Free Software Foundation, either version 3 of the License, or
//   (at your option) any later version.
//
//   CoCoALib is distributed in the hope that it will be useful,
//   but WITHOUT ANY WARRANTY; without even the implied warranty of
//   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//   GNU General Public License for more details.
//
//   You should have received a copy of the GNU General Public License
//   along with CoCoALib.  If not, see <http://www.gnu.org/licenses/>.

#include "CoCoA/CpuTimeLimit.H"
#include "CoCoA/DivMask.H"
#include "CoCoA/FreeModule.H"
#include "CoCoA/RingHom.H"
#include "CoCoA/SparsePolyRing.H"
#include "CoCoA/SugarDegree.H"
#include "CoCoA/TmpGTypes.H"

//#include<list>
// using std::list; // for GPolyList; GPolyPtrList;
//#include<vector>
// using std::vector; // for GPolyPtrVector;

namespace CoCoA
{

  namespace CoeffEncoding
  {
    enum type {Field, FrFldOfGCDDomain};
  }


//-- class GRingInfo --------------------------------------------------*/


// Add fields for GradingIndex,ModulevarIndex.

// long ModuleVarIndex(const SparsePolyRing&); // now private member fn

enum ComputationInputAndGradingType
{HOMOG, NOGRADING, NONHOMOG_GRADING, SaturatingAlg, SaturatingAlgNoDRL};


class GRingInfo
{

public:
  GRingInfo(const SparsePolyRing& theNewSPR,
            const bool HomogeneousInput,
            const bool SaturatingAlgorithm,
            const DivMaskRule&);       // when you have polynomials only ie GB

  GRingInfo(const SparsePolyRing& theNewSPR,
            const SparsePolyRing& theOldSPR,
            const FreeModule& theFM,
            const FreeModule& theOutputFM,
            const bool HomogeneousInput,
            const bool SaturatingAlgorithm,
            const DivMaskRule&);       // when you have modules from theFM

  GRingInfo(const SparsePolyRing& theNewSPR,
            const SparsePolyRing& theOldSPR,
            const FreeModule& theOutputFM,
            const bool HomogeneousInput,
            const bool SaturatingAlgorithm,
            const DivMaskRule&);      // when you have module op on polynomials result vectorlist

  GRingInfo(const SparsePolyRing& theNewSPR,
            const SparsePolyRing& theOldSPR,
            const bool HomogeneousInput,
            const bool SaturatingAlgorithm,
            const DivMaskRule&);      // when you have module op on polynomials result polylist
  ~GRingInfo(){};
  void myCtorAux(const SparsePolyRing& theNewSPR,
                 const bool HomogeneousInput,
                 const bool SaturatingAlgorithm); ///< some assignments in common to all kind of GRingInfo

  //--general----
  const SparsePolyRing& myP_work() const {return myPworkValue;}

  //--for embed/deembed----
  const SparsePolyRing& myP_orig() const {return myPorigValue;}
  const FreeModule& myFreeModule()  const {return myFreeModuleValue;}
  const FreeModule& myOutputFreeModule() const {return myOutputFreeModuleValue;}
  const RingHom& myWorkToOrigHom() const {return myWorkToOrigHomValue;}
  const RingHom& myOrigToWorkHom() const {return myOrigToWorkHomValue;}

  //--for internal computation----
  const DivMaskRule& myDivMaskRule() const {return myDivMaskRuleValue;}
  const PPMonoid& myPPM() const {return myPPMValue;}
  CoeffEncoding::type myCoeffRingType() const { return myCoeffRingTypeValue; }
  void mySetCoeffRingType(CoeffEncoding::type CT); ///< Field or FrFldOfGCDDomain

  //--for embed/deembed----
  long myCompt_OrigToWork(long i) const; //Complement to myMaxComponentIndex
  long myCompt_orig(ConstRefPPMonoidElem T) const;///< the component in orig module

  //--general----
  long myCompt_work(ConstRefPPMonoidElem T)const;///< the component in work ring
  //  bool operator==(const GRingInfo&) const; // NOT USED
  bool AreCompatible(const GRingInfo&,const GRingInfo&); // only for debugging GPoly
  friend std::ostream& operator<<(std::ostream& out, const GRingInfo& theGRI);

  //--for internal computation----
  bool IamModule() const {return IamModuleValue;}
  SugarDegree myNewSugar(ConstRefRingElem f) const;

  //--for embed----
  RingElem myY(const degree& the_d) const;
  ConstRefRingElem myEY(long i) const {return myEYValue[i];};
  RingElem myE(long i) const;

  //--for sugar----
  bool IsMyGradingPosPlus()const{return myGradingPosPlusValue;};
  //void MySetComputationInputAndGradingType // NOT USED
  ComputationInputAndGradingType myInputAndGrading() const {return myInputAndGradingValue;}


private:
  long myModuleIndetIndex() const;

private: // member fields
  const SparsePolyRing myPworkValue;  // for embed/deembed
  const SparsePolyRing myPorigValue;  // for embed/deembed
  const PPMonoid myPPMValue;  ///< the monoid for storing LPP's and lcm's for divisibility tests
  const FreeModule myFreeModuleValue; // for embed/deembed
  const FreeModule myOutputFreeModuleValue; // for embed/deembed
  RingHom myWorkToOrigHomValue;       // for embed/deembed
  RingHom myOrigToWorkHomValue;       // for embed/deembed
  const DivMaskRule myDivMaskRuleValue;
  const bool IamModuleValue;
  static const long myMaxComponentIndex; // max num of compts -- depends on type SmallExponent_t (see GBEnv.C)
  std::vector<RingElem> myEYValue; // for embed/deembed
  CoeffEncoding::type myCoeffRingTypeValue;
  ComputationInputAndGradingType myInputAndGradingValue;
  bool myGradingPosPlusValue;
// FM and the two ring hom. Do we want a separate Module2RingEmbedding class?
};// end class GRingInfo

  // pseudo-ctors GRing for ideals
  GRingInfo GRing_IinP(const SparsePolyRing& P,
                       const bool IsHomogIn);

  GRingInfo GRing_IinRx(const SparsePolyRing& Rx,
                        const bool IsHomogIn);

  // pseudo-ctors GRing for submodules
  GRingInfo GRing_M0(const SparsePolyRing& P_work,
                     const SparsePolyRing& P_orig,
                     const bool IsHomogIn);

  GRingInfo GRing_M1(const SparsePolyRing& P_work,
                     const FreeModule& FM,
                     const bool IsHomogIn);

  GRingInfo GRing_M2(const SparsePolyRing& P_work,
                     const FreeModule& FM_in,
                     const FreeModule& FM_out,
                     const bool IsHomogIn);

}

#endif
