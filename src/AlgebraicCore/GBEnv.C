//   Copyright (c)  2005-2017 John Abbott, Anna M. Bigatti
//   Authors: 2005-2010 Massimo Caboara, 2010-2017 Anna M. Bigatti

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

#include "CoCoA/GBEnv.H"

#include "CoCoA/BigIntOps.H"
#include "CoCoA/DenseMatrix.H" // for DetermineIfMyGradingIsPosPlus
#include "CoCoA/FreeModule.H"
#include "CoCoA/PPMonoidEv.H"
#include "CoCoA/RingQQ.H" // for DetermineIfMyGradingIsPosPlus
#include "CoCoA/VectorOps.H" // just for debugging and statistics
#include "CoCoA/assert.H"
#include "CoCoA/matrix.H" // for DetermineIfMyGradingIsPosPlus
#include "CoCoA/symbol.H"

using std::vector;
#include <limits>
using std::numeric_limits;
#include <algorithm>
using std::min;
using std::max;
#include <iostream>
using std::ostream;
using std::endl;
//using std::swap;



namespace CoCoA
{  

  // BUG BUG BUG? remove 30000 from line below!!!
  /*static*/ const long GRingInfo::myMaxComponentIndex = min(30000ul,
                                                             min(static_cast<unsigned long>(numeric_limits<long>::max()-1),
                                                                 static_cast<unsigned long>(numeric_limits<SmallExponent_t>::max()-1))); // max num of compts -- depends on type SmallExponent_t



  namespace // anonymous
  { // namespace // anonymous ----------------------------------------

    RingHom PwToPo(const SparsePolyRing& P_work, const SparsePolyRing& P_orig)
    {
      if (P_work==P_orig)  return  IdentityHom(P_work);
      std::vector<RingElem> images = indets(P_orig);  // x[i] |-> x[i]
      for (long i=0; i!=GradingDim(P_work); ++i)
        images.push_back(one(P_orig));  // y[i] |-> 1
      images.push_back(one(P_orig));    // e |-> 1
      return  PolyAlgebraHom(P_work, P_orig, images);
    }


    RingHom PoToPw(const SparsePolyRing& P_work, const SparsePolyRing& P_orig)
    {
      if (P_work==P_orig)  return  IdentityHom(P_work);
      std::vector<RingElem> images;
      for (long i=0; i < NumIndets(P_orig); ++i)
        images.push_back(indet(P_work, i));       // x[i] |-> x[i]
      return PolyAlgebraHom(P_orig, P_work, images);
    }


  //-------------------------------------------------------
  //---------class GRingInfo-------------------------------
  //-------------------------------------------------------

  ComputationInputAndGradingType  DetermineComputationType(long GrDim,
                                                           const bool IsHomog,
                                                           const bool IsSatAlg)
  {
    if (IsSatAlg)
    { 
      //  if (!IsHomog)  CoCoA_THROW_ERROR1(ERR::ShouldNeverGetHere);
      if (GrDim==0) return SaturatingAlgNoDRL;
      return SaturatingAlg;
    }
    if (GrDim==0) return NOGRADING;
    if (IsHomog) return HOMOG;
    return NONHOMOG_GRADING;
  }//DetermineComputationType


    // AMB 2026-02-05: This function only returns false.  ???
    // Grdim>=2, order matrix first row is 0,..,0,1
    bool DetermineIfMyGradingIsPosPlus(const SparsePolyRing& theSPR)
    {
      // This checks if indeed the order is a PosPlus.
      // Another option is to SET this field at the right time.
      // Slightly more efficient, but more risky.
      return false; // <---- return false  ??? always ???
      if (GradingDim(theSPR)<1)
        return false;
      ConstMatrixView OrdM = OrdMat(ordering(PPM(theSPR)));
      // JAA 2015-11-30 line above replaces the two below
      // matrix OrdM(NewDenseMat(RingQQ(),NumIndets(theSPR),NumIndets(theSPR)));
      // PPM(theSPR)->myOrdering()->myOrdMatCopy(OrdM);
      for (long i=0; i<NumIndets(theSPR)-1; ++i)
        if (OrdM(0,i)!=0)
          return false;
      if (OrdM(0,NumIndets(theSPR)-1)!=1)
        return false;
      return true;
    }

  } // namespace // anonymous -----------------------------------------


  // ----------------------------------------------------------------------
  // GRingInfo ctors

  void GRingInfo::myCtorAux(const SparsePolyRing& P,
                            const bool IsHomog,
                            const bool IsSatAlg)
  {
    myInputAndGradingValue=DetermineComputationType(GradingDim(P),
                                                    IsHomog,
                                                    IsSatAlg);
    myGradingPosPlusValue=DetermineIfMyGradingIsPosPlus(P); // always false???
    mySetCoeffRingType(CoeffEncoding::Field);
  }
  

  GRingInfo::GRingInfo(const SparsePolyRing& P,
                       const bool IsHomog,
                       const bool IsSatAlg,
                       const DivMaskRule& DivMaskR,
                       const CpuTimeLimit& CheckForTimeout):
    myPworkValue(P),
    myPorigValue(P),
    myPPMValue(NewPPMonoidEv(symbols(PPM(P)), ordering(PPM(P)))),
    myFreeModuleValue(NewFreeModule(P,1)),
    myOutputFreeModuleValue(NewFreeModule(P,1)),
    myWorkToOrigHomValue(IdentityHom(P)),
    myOrigToWorkHomValue(IdentityHom(P)),
    myDivMaskRuleValue(DivMaskR),
    IamModuleValue(false),
    myTimeoutChecker(CheckForTimeout)
  {
    myCtorAux(P, IsHomog, IsSatAlg);
    myTimeoutChecker.myReset(IterationVariability::high);
  }// ctor GRingInfo


  GRingInfo::GRingInfo(const SparsePolyRing& P_work,
                       const SparsePolyRing& P_orig,
                       const FreeModule& theFM,
                       const FreeModule& theOutputFM,
                       const bool IsHomog,
                       const bool IsSatAlg,
                       const DivMaskRule& DivMaskR,
                       const CpuTimeLimit& CheckForTimeout):
    myPworkValue(P_work),
    myPorigValue(P_orig),
    myPPMValue(NewPPMonoidEv(symbols(PPM(P_work)), ordering(PPM(P_work)))),
    myFreeModuleValue(theFM),
    myOutputFreeModuleValue(theOutputFM),
    myWorkToOrigHomValue(PwToPo(myPworkValue, myPorigValue)),
    myOrigToWorkHomValue(PoToPw(myPworkValue, myPorigValue)),
    myDivMaskRuleValue(DivMaskR),
    IamModuleValue(true),    //    IamModuleValue(P_work!=P_orig),
    myTimeoutChecker(CheckForTimeout)
  {
    // if (!IsField(CoeffRing(P_orig))) CoCoA_THROW_ERROR1(ERR::ReqField);
    // std::vector<RingElem> Y; // NOT used!
    // const std::vector<RingElem>& x = indets(myPworkValue);
    // Fill Y
    // for (long i=0; i < GradingDim(myPworkValue); ++i)
    //   Y.push_back(x[i+NumIndets(P_orig)]);

    const std::vector<degree> Sh=shifts(myFreeModuleValue);
    //RingElem tmp(myPworkValue);
    for (long i=0; i < NumCompts(myFreeModuleValue); ++i)
      myEYValue.push_back(myE(i) * myY(Sh[i]));
    myCtorAux(P_work, IsHomog, IsSatAlg);
    myTimeoutChecker.myReset(IterationVariability::high);
  }// ctor GRingInfo
  

  GRingInfo::GRingInfo(const SparsePolyRing& P_work,
                       const SparsePolyRing& P_orig,
                       const FreeModule& theOutputFM,
                       const bool IsHomog,
                       const bool IsSatAlg,
                       const DivMaskRule& DivMaskR,
                       const CpuTimeLimit& CheckForTimeout):
    myPworkValue(P_work),
    myPorigValue(P_orig),
    myPPMValue(NewPPMonoidEv(symbols(PPM(P_work)), ordering(PPM(P_work)))),
    myFreeModuleValue(NewFreeModule(P_work,1)), // unused
    myOutputFreeModuleValue(theOutputFM), // unused
    myWorkToOrigHomValue(PwToPo(myPworkValue, myPorigValue)),
    myOrigToWorkHomValue(PoToPw(myPworkValue, myPorigValue)),
    myDivMaskRuleValue(DivMaskR),
    IamModuleValue(true),    //    IamModuleValue(P_work!=P_orig),
    myTimeoutChecker(CheckForTimeout)
  {
    // if (!IsField(CoeffRing(P_orig))) CoCoA_THROW_ERROR1(ERR::ReqField);
    myCtorAux(P_work, IsHomog, IsSatAlg);
    myTimeoutChecker.myReset(IterationVariability::high);
  }// ctor GRingInfo


  GRingInfo::GRingInfo(const SparsePolyRing& P_work,
                       const SparsePolyRing& P_orig,
                       const bool IsHomog,
                       //const bool IsForModule,
                       const bool IsSatAlg,
                       const DivMaskRule& DivMaskR,
                       const CpuTimeLimit& CheckForTimeout):
    myPworkValue(P_work),
    myPorigValue(P_orig),
    myPPMValue(NewPPMonoidEv(symbols(PPM(P_work)), ordering(PPM(P_work)))),
    myFreeModuleValue(NewFreeModule(P_work,1)), // unused
    myOutputFreeModuleValue(NewFreeModule(P_work,1)), // unused
    myWorkToOrigHomValue(PwToPo(myPworkValue, myPorigValue)),
    myOrigToWorkHomValue(PoToPw(myPworkValue, myPorigValue)),
    myDivMaskRuleValue(DivMaskR),
    //    IamModuleValue(IsForModule),
    IamModuleValue(P_work!=P_orig), // Move outside ctor to GRing_Mx
    myTimeoutChecker(CheckForTimeout)
  {
    //    if (!IsField(CoeffRing(P_orig)))
    //      CoCoA_THROW_ERROR1(ERR::ReqField);
    myCtorAux(P_work, IsHomog, IsSatAlg);
    myTimeoutChecker.myReset(IterationVariability::high);
  }// ctor GRingInfo

  // GRingInfo ctors
  // ----------------------------------------------------------------------

  void GRingInfo::mySetCoeffRingType(CoeffEncoding::type CT)
  { myCoeffRingTypeValue = CT; }


  long GRingInfo::myCompt_work(ConstRefPPMonoidElem T) const
  {
    if (!IamModule()) return 0;// True Ring
    return exponent(T, myModuleIndetIndex());
  }

  // for embed/deembed ---
  long GRingInfo::myCompt_orig(ConstRefPPMonoidElem T) const
  {
    CoCoA_ASSERT(IamModule());
    return myMaxComponentIndex - myCompt_work(T);
  }


  // for embed/deembed ---
  long GRingInfo::myCompt_OrigToWork(long i) const
  { return myMaxComponentIndex-i; }  // was inline AMB 2026-04-18

  
  // for embed/deembed ---
  RingElem GRingInfo::myY(const degree& d) const
  {
    const SparsePolyRing P(myP_work());
    RingElem result(one(P));
    const long YFirstIdx = NumIndets(P) -GradingDim(P) -1;
    for (long j=0; j < GradingDim(P); ++j)
      result *= IndetPower(P, YFirstIdx+j, d[j]); // Y(j)^d[j]
    return result;
  }


  RingElem GRingInfo::myE(long i) const
  { // was inline
    return IndetPower(myP_work(), myModuleIndetIndex(), myCompt_OrigToWork(i));
  }


  SugarDegree GRingInfo::myNewSugar(ConstRefRingElem f) const
  {
    switch (myInputAndGrading())
    {
    case HOMOG:            // ANNA: (w)graded + homogeneous
      return NewWSugarConst(f);
    case SaturatingAlg:    // SaturatingAlg
      return NewWSugarSat(f);
    case NONHOMOG_GRADING: // ANNA: (w)graded + non-homogeneous
      if (/*module && */ IsMyGradingPosPlus())
        // ANNA: should be implemented with proper weights
        return NewStdSugarNoIdx(f, myModuleIndetIndex());
      return NewWDeg1CompTmp(f);
    case NOGRADING:        // ANNA: GradingDim = 0 --> StandardSugarAlgorithm
      // if (/*module && */ IsMyGradingPosPlus())
      if (IamModule())
        return NewStdSugarNoIdx(f, myModuleIndetIndex());
      return NewStdSugar(f);
    case SaturatingAlgNoDRL: // GradingDim = 0
      if (/*module && */ IsMyGradingPosPlus())
        return NewStdSugarNoIdxSat(f, myModuleIndetIndex());
      return NewStdSugarSat(f);
    default:
      CoCoA_THROW_ERROR1(ERR::ShouldNeverGetHere);
    }
    return NewStdSugar(f); // just to keep the compiler quiet
  }


ostream& operator<<(ostream& out, const GRingInfo& theGRI)
{
  if (!out) return out;  // short-cut for bad ostreams
  out << " the working ring is " << theGRI.myP_work() << endl
      << " the original ring is " << theGRI.myP_orig() << endl
     //<<" Input Free Module "<<theGRI.myFreeModule()<<endl
     //<<" Output Free Module "<<theGRI.myOutputFreeModule()<<endl
      << " IamModule " << theGRI.IamModule() << endl
      << " myInputAndGrading = " << theGRI.myInputAndGrading() << endl
      << " IsMyGradingPosPlus = " << theGRI.IsMyGradingPosPlus() << endl
      << " EY = " << theGRI.myEYValue << endl;
  out << endl;
  return out;
}


  long GRingInfo::myModuleIndetIndex() const
  { return NumIndets(myPworkValue)-1; }


bool AreCompatible(const GRingInfo& GRI1,const GRingInfo& GRI2)
{  // used only for debugging
  return (GRI1.myP_work() == GRI2.myP_work() &&
          GRI1.myP_orig() == GRI2.myP_orig() &&
          GRI1.myPPM() == GRI2.myPPM());
       //&& // I want to do this, the == operator is not there
         //GRI1.myDivMaskRuleValue==GRI2.myDivMaskRuleValue
}


// pseudo-ctors for GRingInfo -------------------------------

  GRingInfo GRing_IinP(const SparsePolyRing& P,
                       const bool IsHomogIn,
                       const CpuTimeLimit& CheckForTimeout)
  {
    return GRingInfo(P, IsHomogIn,
                     false /*IsSatAlg*/, NewDivMaskEvenPowers(),
                     CheckForTimeout);
  }


  GRingInfo GRing_IinRx(const SparsePolyRing& Rx,
                        const bool IsHomogIn,
                        const CpuTimeLimit& CheckForTimeout)
  {
    GRingInfo GRI(GRing_IinP(Rx, IsHomogIn, CheckForTimeout));
    GRI.mySetCoeffRingType(CoeffEncoding::FrFldOfGCDDomain);
    return GRI;
  }


  GRingInfo GRing_M0(const SparsePolyRing& P_work,
                     const SparsePolyRing& P_orig,
                     const bool IsHomogIn,
                     const CpuTimeLimit& CheckForTimeout)
  {
    return GRingInfo(P_work, P_orig, IsHomogIn,
                     false /*IsSatAlg*/, NewDivMaskEvenPowers(),
                     CheckForTimeout);
  }


  GRingInfo GRing_M1(const SparsePolyRing& P_work,
                     const FreeModule& FM,
                     const bool IsHomogIn,
                     const CpuTimeLimit& CheckForTimeout)
  {
    return GRingInfo(P_work, RingOf(FM), FM, IsHomogIn,
                     false /*IsSatAlg*/, NewDivMaskEvenPowers(),
                     CheckForTimeout);
  }


  GRingInfo GRing_M2(const SparsePolyRing& P_work,
                     const FreeModule& FM_in,
                     const FreeModule& FM_out,
                     const bool IsHomogIn,
                     const CpuTimeLimit& CheckForTimeout)
  {
    return GRingInfo(P_work, RingOf(FM_out), FM_in, FM_out, IsHomogIn,
                     false /*IsSatAlg*/, NewDivMaskEvenPowers(),
                     CheckForTimeout);
  }


}// end namespace cocoa
