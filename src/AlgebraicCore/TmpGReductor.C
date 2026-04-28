//   Copyright (c)  2005-2017  John Abbott, Anna M. Bigatti
//   Authors: 2005-2007  Massimo Caboara, 2016-1017 Anna M. Bigatti

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

#include "CoCoA/TmpGReductor.H"

#include "CoCoA/BigIntOps.H"
#include "CoCoA/DenseMatrix.H"
#include "CoCoA/FractionField.H"
#include "CoCoA/FreeModule.H"
#include "CoCoA/MatrixForOrdering.H"
#include "CoCoA/MatrixOps.H"
#include "CoCoA/MatrixView.H"
//#include "CoCoA/ModuleOrdering.H"
#include "CoCoA/RingDistrMPolyInlFpPP.H"
#include "CoCoA/RingDistrMPolyInlPP.H"
#include "CoCoA/RingFp.H" // for dynamic_cast<RingFpImpl*>(CoeffRing.myRingPtr())
#include "CoCoA/RingQQ.H"  // for RingQQ, QQEmbeddingHom
#include "CoCoA/RingZZ.H"
#include "CoCoA/SparsePolyIter.H"
#include "CoCoA/SparsePolyOps-RealRadical.H"
#include "CoCoA/SparsePolyOps-RingElem.H"
#include "CoCoA/VectorOps.H"  // for printing lists/vectors, HasUniqueOwner
#include "CoCoA/assert.H"
#include "CoCoA/convert.H"
#include "CoCoA/interrupt.H"
#include "CoCoA/matrix.H"
#include "CoCoA/symbol.H"
#include "CoCoA/time.H"
#include "CoCoA/verbose.H"  // for VerboseLog
//#include "CoCoA/utils.H" // for LongRange

//#include <algorithm>
//using std::for_each;
// #include <functional>
// using std::binary_function;
// using std::less;
// using std::mem_fun_ref; // for calling GPair::complete on GPairList
#include <iostream>
using std::ostream;
using std::endl;
using std::flush;
// #include <list>
// using std::list;
#include <sstream> // for ostringstream
#include <utility>
using std::make_pair;
#include <vector>
//using std::vector;

//static bool ANNA_DEBUG = true;
//static const bool MAX_DEBUG = false;


namespace CoCoA
{
  //  int GReductor::ourDefaultStatLevel = -1;


  namespace{ // anonymous

    bool BoolCmpLPPGPoly(const GPoly& f, const GPoly& g)
    {
      CoCoA_ASSERT(!IsZero(f));//BUG HUNTING  ???
      CoCoA_ASSERT(!IsZero(g));//BUG HUNTING  ???
      //const PPMonoid& PPM1=PPM(owner(f));
      return PPM(owner(f))->myCmp(raw(LPPForOrd(f)),raw(LPPForOrd(g)))>0;
    }

  } //   namespace anonymous


  void GReductor::myCtorAux(const BuchbergerOpTypeFlag theBuchbergerOpType)
  //,                        const UseDynamicAlgFlag IsDynamic)
  {
    myPrepared=false;
    myAgeValue = 0;
    //    myWrongLPPFoundValue=false;

    myBuchbergerOpType=theBuchbergerOpType;

    if (!myCriteria.myCoprime) myStat.myCopLevel=1000;
    if (!myCriteria.myGM) myStat.myGMLevel=1000;
    if (!myCriteria.myBack) myStat.myBCLevel=1000;
  }


  GReductor::GReductor(const GRingInfo& theGRI,
                       const std::vector<RingElem>& F,
                       const BuchbergerOpTypeFlag theBuchbergerOpType,
                       const GBCriteria criteria):
      myGRingInfoValue(theGRI),
      myTrueReductors(theGRI),
      mySPoly(theGRI),
      myOldDeg(GradingDim(theGRI.myNewSPR())),
      myIncomingWDeg(GradingDim(theGRI.myNewSPR())),
      myStat(len(F)),
      myCriteria(criteria)
  {
    myCtorAux(theBuchbergerOpType);
    for (const RingElem& g: F)
      if (!IsZero(g))
        myPolys.push_back(GPoly(g,myGRingInfoValue)); // list
    myPolys.sort(BoolCmpLPPGPoly);
    myTruncDegValue = ourNoTruncValue;
  } //  GReductor ctor


  // This ctor allows to avoid transforming gpolys to polys and back if
  // you want to evaluate complex expressions. The input GPolys may contain
  // zeros and/or not be sorted. Take care.
  GReductor::GReductor(const GRingInfo& theGRI,
                       const GPolyList& TheInputGPolys,
                       const BuchbergerOpTypeFlag theBuchbergerOpType,
                       const GBCriteria criteria):
      myGRingInfoValue(theGRI),
      myTrueReductors(theGRI),
      mySPoly(theGRI),
      myOldDeg(GradingDim(theGRI.myNewSPR())),
      myIncomingWDeg(GradingDim(theGRI.myNewSPR())),
      myStat(len(TheInputGPolys)),
      myCriteria(criteria)
  {
    myPolys=TheInputGPolys;
    myCtorAux(theBuchbergerOpType);
    myTruncDegValue = ourNoTruncValue;

    // If you want to remove zeros and/or sort your input GPolys.
    // GPoly Zero(zero(myPolyRing),myGRingInfoValue,Component(LPP(zero(myPolyRing),myGRingInfoValue)),0);
    // myPolys.remove(Zero);
    // myPolys.sort(BoolCmpLPPGPoly);
  } // GReductor ctor



  // ostream& operator<<(ostream& out, const GReductor& GR)
  // {
  //   if (!out) return out;  // short-cut for bad ostreams

  //   out<<"The GROBNER REDUCTOR\n";
  //   out<<"  Reductors Len="<<GR.myReductorsLen()
  //       <<"  GB Len="<<GR.myGBasisLen()
  //       <<"  Pairs Len="<<GR.myPairsLen()
  //       <<"  Byte Size="<<sizeof(GR)<<"\n";
  //   //    GR.myStampaReductors(out);
  //   GR.myTrueReductors.myStampaReductors(out);
  //   //    GR.myStampaGB(out);
  //   out << "The GBASIS\n";
  //   for (const auto& ptr: GR.myGB) out << *ptr << "," << endl;
  //   out << endl;
  //   //    GR.myStampaPairs(out);
  //   out << "The PAIRS\n" << GR.myPairs << "\n";

  //   out<<"\n";
  //   out<<"The Ring"<<GR.myGRingInfoValue<<"\n";
  //   out<<"GradingDim  is "<<GradingDim(GR.myGRingInfoValue.myNewSPR())<<endl;
  //   out<<"The Ring Module Index "<<ModuleVarIndex(GR.myGRingInfoValue.myNewSPR())<<"\n";
  //   out<<"Age "<< GR.myAgeValue <<"\n";
  //   out<<"Preparation done? "<<GR.myPrepared<<"\n";
  //   out<<"myOldDeg "<<GR.myOldDeg<<"\n";
  //   out<<"myIncomingWDeg " << GR.myIncomingWDeg << "\n";
  //   //    out<<"Is Dynamic Algorithm? "<<GR.IsDynamicAlgorithm<<"\n";
  //   //    out<<"Is Wrong LPP been Found? "<<GR.myWrongLPPFoundValue<<"\n";
  //   out<<"Cop Criterion " <<GR.myCriteria.myCoprime<<"\n";
  //   out<<"GM Criteria "   <<GR.myCriteria.myGM<<"\n";
  //   out<<"Back Criterion "<<GR.myCriteria.myBack<<"\n";
  //   out<<"Div Criterion " <<GR.myCriteria.myDiv<<"\n";
  //   out<<"Algorithm "<<GR.myBuchbergerOpType<<"\n";
  //   out<<"\n";
  //   return out;
  // }


  namespace { // anonymous
    void VERBOSE_NewPolyInGB(VerboseLog& VERB, long LenGB, long LenGPair, const GPoly& SPoly)
    {
      if (VerbosityLevel()>=100)
      {
        VERB(100) << "--New poly in GB:"
                  << " len(GB) = " << LenGB
                  << " len(pairs) = " << LenGPair << endl;
        VERB(101) << "--NumTerms = " << NumTerms(SPoly)
                  << " wdeg = " << wdeg(SPoly) << endl;
        VERB(150) << "--New poly is " << poly(SPoly) << endl;
      }
    }
  } // namespace anonymous


  // This procedure may be substituted by a transform_if
  std::vector<RingElem> GReductor::myExportGBasis()
  {
    std::vector<RingElem> GB;  GB.reserve(len(myGB));
    for (const auto& ptr: myGB)
      if (IsActive(*ptr))  GB.push_back(poly(*ptr));
    return GB;
  }


  std::vector<RingElem> GReductor::myExportMinGens()
  {
    std::vector<RingElem> G;  G.reserve(len(myGB));
    for (const auto& ptr: myGB)
      if (IsMinimalGen(*ptr))  G.push_back(poly(*ptr));
    return G;
  }


  namespace { // anonymous    //-- DeEmbedding --------------------------

    // similar copy for this function in TmpGOperations:
    // this copy is only for fn DeEmbedPoly(g, GRI) defined just below
    // used in myExportGBasis/MinGens_module
    ModuleElem DeEmbedPoly(ConstRefRingElem g, const GRingInfo& theGRI)
    {
      const SparsePolyRing OldP=theGRI.myOldSPR();
      const SparsePolyRing NewP=theGRI.myNewSPR();
      const FreeModule FM=theGRI.myOutputFreeModule();
      ModuleElem v(FM);
      
      const std::vector<ModuleElem>& e = gens(FM);
      
      RingElem tmp(OldP);
      for (SparsePolyIter i=BeginIter(g); !IsEnded(i); ++i)
      {
        tmp = theGRI.myNewP2OldP()(monomial(NewP,coeff(i),PP(i)));
        v += tmp * e[theGRI.myCompt_orig(PP(i))];
      }
      return v;
    }

  } // namespace anonymous------------------------------------


  std::vector<ModuleElem> GReductor::myExportGBasis_module()
  {
    std::vector<ModuleElem> G;  G.reserve(len(myGB));
    for (const auto& ptr: myGB)
      if (IsActive(*ptr))
        G.push_back(DeEmbedPoly(poly(*ptr), myGRingInfoValue));
    return G;
  }


  std::vector<ModuleElem> GReductor::myExportMinGens_module()
  {
    std::vector<ModuleElem> G;  G.reserve(len(myGB));
    for (const auto& ptr: myGB)
      if (IsMinimalGen(*ptr))
        G.push_back(DeEmbedPoly(poly(*ptr), myGRingInfoValue));
    return G;
  }



//esame piu' approfondito - sia correttezza sia efficienza
//warning: il CopCriterion is false, still the coprimality is used to decide
//         which pair kill
  long GReductor::myGMInsert(GPairList& L,GPair P)
  {
    long NumPairsConsidered=0;
    bool ToBeInserted=true;
    bool erased=false;
    long P_Component=GPairComponent(P);

    GPairList::iterator it=L.begin();
    while (it!=L.end() && ToBeInserted)
    {
      ++NumPairsConsidered;
      if (P_Component==GPairComponent(*it)
          && IsDivisibleFast(LCMwMask(P), LCMwMask(*it)))
      {
        ToBeInserted=false;
        if (LCMwMask(P)==LCMwMask(*it) && (!it->IamCoprime()) && (P.IamCoprime()))
        {
          //          P.myComplete();          it->myComplete();
          *it=P;
        }
      }
      else
        if (P_Component==GPairComponent(*it)
            && IsDivisibleFast(LCMwMask(*it), LCMwMask(P)) )
        {
          it=L.erase(it);
          erased=true;
        }
      if (!erased)  ++it;
      erased=false;
    } // while
    if (ToBeInserted)
      L.push_back(P);// new pairs are sorted later
    return NumPairsConsidered;
  }


  void GReductor::myBuildNewPairs(GPairList& new_pairs)
  {
    VerboseLog VERBOSE("myBuildNewPairs");
    long standing_index = len(myGB)-1;
    long walking_index = 0;
    long inserted_pairs = 0;//STAT

    GPolyPtrList::const_iterator last=myGB.end(); --last;
    long last_component = component(**last);
    GPolyPtrList::const_iterator it;
    for (it=myGB.begin(); it!=last; ++it,++walking_index)
    {
      if (IsActive(**it)&&last_component == component(**it))
      {
        //std::clog<<"walking_component "<<Component(**it)<<endl;
        if (myCriteria.myDiv && IsDivisibleFast(LPPForDivwMask(**it), LPPForDivwMask(**last)) ) // speed is not necessary
        {
          if (VerbosityLevel() >= myStat.myPolyDeletedLevel)
            VERBOSE(myStat.myPolyDeletedLevel) <<"<"<<walking_index
                                               <<"> "<<LPPForDiv(**it)
                                               <<" DELETED BY NEW "
                <<"<"<<standing_index<<"> "<<LPPForDiv(**last)<< endl;
          (*it)->Deactivate();
          ++myStat.myPolyDeleted;
        } //second if
        //else
        ++inserted_pairs;
        ++myStat.myPInserted;
        if (myCriteria.myGM)
          myStat.myGMTouched+=myGMInsert(new_pairs, GPair(**it,**last));
        else
        {
          myStat.myGMTouched=0;
          Ordered_Insert(new_pairs,GPair(**it,**last));
        }
      };//Active if
    };//for

    myStat.myGMKilled+=inserted_pairs-len(new_pairs);
    if (VerbosityLevel() >= myStat.myGMLevel && (inserted_pairs!=len(new_pairs)))
      VERBOSE(myStat.myGMLevel) << "[GM KILLED "
                                << inserted_pairs-len(new_pairs)
                                << " OUT OF " << inserted_pairs << "]" << endl;

    long pre_cop_test=len(new_pairs);
    if (myCriteria.myCoprime)
    {
      GPairList::iterator it1=new_pairs.begin();
      while (it1!=new_pairs.end())
        if (it1->IamCoprime())
          it1=new_pairs.erase(it1);
        else
          ++it1;
    }
    if (pre_cop_test!=len(new_pairs))
      if (VerbosityLevel() >= myStat.myCopLevel)
        VERBOSE(myStat.myCopLevel) <<"[COP KILLED "<<pre_cop_test-len(new_pairs)
                                   <<" OUT OF "<<inserted_pairs<<"]" << endl;
    myStat.myCopKilled+=pre_cop_test-len(new_pairs);
    if (VerbosityLevel() >=  myStat.myNewPairsLevel)
    {
      std::ostringstream oss;
      for (const auto& pair: new_pairs)
        oss << "<"<<pair.myFirstIndex() << "," << pair.mySecondIndex() << ">, ";
      VERBOSE(myStat.myNewPairsLevel) << len(new_pairs)
                                      << " new pairs: " << oss.str() << endl;
    };
  } // myBuildNewPairs


  void GReductor::myApplyBCriterion()
  {
    VerboseLog VERBOSE("myApplyBCriterion");
    const PPWithMask& newPP(LPPForDivwMask(myPolys.back()));
    const long newPP_component = component(myPolys.back());
    GPairList::iterator it=myPairs.begin();
    while (it!=myPairs.end())
    {
      ++myStat.myBTouched;
      if (GPairComponent(*it)!=newPP_component
          ||
          it->BCriterion_OK(newPP))
      {++it;}
      else
      {
        if (VerbosityLevel() >= myStat.myPolyDeletedLevel)
          VERBOSE(1)<<*it<<" KILLED BY NEW POLY "<<newPP<<" BCRIT\n";
        ++myStat.myBKilled;
        it=myPairs.erase(it);
      };// else
    };//While
  }


  void GReductor::myUpdateBasisAndPairs()
  { myUpdateBasisAndPairs(mySPoly); }


  void GReductor::myUpdateBasisAndPairs(const GPoly& inPoly)
  {
    VerboseLog VERBOSE("myUpdateBasisAndPairs");
    // --> if non-homog, inPoly must have sugar <--
    //if (!IsTrueGCDDomain(CoeffRing(mySPoly)))
    //myTrueReductors.OrderedInterreduce(mySPoly);  // ANNA
    VERBOSE(100) << wdeg(inPoly) << std::endl;
    if (myGRingInfo().myInputAndGrading()==HOMOG)
      myTrueReductors.myReduceTails(inPoly);// this must be the first op
    ++myAgeValue;
    if (IsConstant(poly(inPoly)))
    {
      VERBOSE(100) << "!!!!!!!!!! ideal(1) !!!!!!!!!!!!" << std::endl;
      myPolys.clear();
      myPolys.push_back(inPoly);
      myGB.clear();
      myGB.push_back(&myPolys.back());
      myTrueReductors.myClear();
      myTrueReductors.Insert(&myPolys.back());
      myPairs.clear();
      return;
    }
    myPolys.push_back(inPoly);// this must be the second op
    //myTrueReductors.SuperInterreduce(mySPoly);  // ANNA
    myTrueReductors.Insert(&myPolys.back());
    myGB.push_back(&myPolys.back());
    GPairList new_pairs;
    myBuildNewPairs(new_pairs);
    if (myCriteria.myBack)
      myApplyBCriterion();
    for (auto& pair: new_pairs)  pair.myComplete();
    new_pairs.sort();
    myPairs.merge(new_pairs);
  }


  void GReductor::myReduceCurrentSPoly()
  {
    const char* const FnName = "myReduceCurrentSPoly";
    VerboseLog VERBOSE(FnName);
    //    CheckForInterrupt(FnName);
    //    myGRingInfo().myCheckForTimeout(FnName);
    if (!myPrepared)
    {
      VERBOSE(10)<<"GReductor: no preparation done ";
      return;
    }
    //if (myStat.myDegLevel)
    //  clog<<"GReductor:myReduceCurrentSPoly performing one pair handling";
    if (myPolys.empty() || myPairs.empty())  return;
//     if (VerbosityLevel() >= myStat.myNumPairLevel)
//       VERBOSE(myStat.myNumPairLevel) << "len(pairs) = " << len(myPairs) << endl;
    VERBOSE(myStat.myReductionLevel+1) << myPairs.front() << endl;
    if (myPairs.front().IamCoprime() && myCriteria.myCoprime)
    {
      mySPoly = GPoly(myGRingInfoValue); // initialized as 0
      VERBOSE(myStat.myCopLevel) << "coprime" << endl;
      ++myStat.myCopKilled;
      myStat.myReductionTime=0.0;
    }
    else
    {
      mySPoly.myAssignSPoly(myPairs.front(), myAgeValue);  // ??? SPoly computed only if not coprime
      if (myPairs.front().IsInputPoly())  mySPoly.mySetMinimalGen();
      VERBOSE(200) << " --before: " << poly(mySPoly) << std::endl;
      myStat.myPolyLens.push_back(make_pair(NumTerms(mySPoly),0));
      std::ostringstream VERB_s;
      if (VerbosityLevel() >= myStat.myReductionLevel)
      {
        if (IsZero(mySPoly)) VERB_s << " = 0";
        else VERB_s << "len(SPoly)=" << myStat.myPolyLens.back().first;
      }
      myStat.myReductionTime = CpuTime();
      mySPoly.myReduce(myTrueReductors); // interrupt/timeout
      myStat.myReductionTime -= CpuTime();
      VERBOSE(200) << " --after:  " << poly(mySPoly) << std::endl;
      ++myStat.myNReductions;
      myStat.myPolyLens.back().second = NumTerms(mySPoly);
      if (IsZero(mySPoly)) ++myStat.myUseless; else ++myStat.myUseful;
      // if (!IsTrueGCDDomain(CoeffRing(mySPoly)) || NumTerms(mySPoly)<=2)
      // myTrueReductors.interreduce(mySPoly);
      if (VerbosityLevel() >= myStat.myReductionLevel)
      {
        VERB_s << " -->";
        if (IsZero(mySPoly)) VERB_s << "0";
        else
        {
          //          VERB_s << "<" << len(myGB) << ">: ";
          VERB_s << myStat.myPolyLens.back().second << " " << LPPForDiv(mySPoly) << endl;
          //if (component(mySPoly)!=0) VERB_s <<" compt =" << component(mySPoly) << endl;
          if (NumTerms(mySPoly)<=2) VERB_s <<" short-reducer deg =" << wdeg(mySPoly) << endl;
        }
        VERB_s << " time=" << std::floor(-myStat.myReductionTime);
        VERBOSE(myStat.myReductionLevel) << VERB_s.str() << endl;
      } // (VerbosityLevel() >= myStat.myReductionLevel)
    } // else -if not coprime
    myPairs.erase(myPairs.begin()); // erase the used gpair
    //if (!IsZero(mySPoly)) myUpdateBasisAndPairs();

//// move this check into a more appropriate position (after adding the new pairs)
    // if (!myPairs.empty())
    // {
    //   myFirstPairWDeg = wdeg(myPairs.front()); // ANNA: next pair to do
    //   if (myFirstPairWDeg != myOldDeg)
    //   {
    //     VERBOSE(myStat.myDegLevel) << "--NEW DEG: myFirstPairWDeg = "
    //                                << myFirstPairWDeg
    //                                << "\tSugar = " << sugar(myPairs.front())
    //                                << endl;
    //     myStat.myUpgradeDegStats(myOldDeg, len(myPairs));
    //     myOldDeg = myFirstPairWDeg;
    //   } //if (myFirstPairWDeg!=myOldDeg)
    // } //if (!myPairs.empty())
    // else myStat.myUpgradeDegStats(myFirstPairWDeg,0);
  } // myReduceCurrentSPoly


  void GReductor::myUpdateIncomingWDeg()
  {
    VerboseLog VERBOSE("myUpdateIncomingWDeg");
    if (!myPairs.empty())
    {
      myIncomingWDeg = wdeg(myPairs.front()); // ANNA: next pair to do
      if (myIncomingWDeg != myOldDeg)
      {
        VERBOSE(myStat.myDegLevel) << "--NEW-DEG: myIncomingWDeg = "
                                   << myIncomingWDeg
                                   << "\tSugar = " << sugar(myPairs.front())
                                   << endl;
        myStat.myUpgradeDegStats(myOldDeg, len(myPairs));
        myOldDeg = myIncomingWDeg;
      } //if (myFirstPairWDeg!=myOldDeg)
    } //if (!myPairs.empty())
    else myStat.myUpgradeDegStats(myIncomingWDeg, 0);
  }
  
  
  // ANNA: called by TmpGOperations
  void GReductor::myDoGBasis()
  {
    //    CoCoA_ASSERT(myGetBuchbergerOpType() == HomogeneousAlg);
    VerboseLog VERBOSE("myDoGBasis");
    myPrepareGBasis();
    while (!myPairs.empty())
    {
      myReduceCurrentSPoly();
      if (!IsZero(mySPoly))
      {
        myUpdateBasisAndPairs();
        VERBOSE_NewPolyInGB(VERBOSE, len(myGB), len(myPairs), mySPoly);
        // if (!myPairs.empty())
        //   if (myIncomingWDeg!=myOldDeg && myTrueReductors.IhaveBorelReductors())
        //     myTrueReductors.myBorelReductorsUpdateInNextDegree();
      }
      myUpdateIncomingWDeg();
      if (myTruncDeg() != ourNoTruncValue)
      {
        if (myPairs.empty())  mySetTruncDeg(ourNoTruncValue); // GB complete
        else
          if (myTruncDeg() < myIncomingWDeg[0])
          {
            VERBOSE(100) << "myTruncDeg() =" << myTruncDeg()
                         << " < myIncomingWDeg[0]: "
                         << myIncomingWDeg << std::endl;
            break;
          }
      }
    } // while
    VERBOSE(100) << "--Final clean up ... " << endl;
    myFinalizeGBasis();
    if (VerbosityLevel() >= myStat.myFinalLevel)
      myStat.myStampa(VERBOSE(myStat.myFinalLevel));
  } // myDoGBasis


// ANNA: called by TmpGOperations (ComputeElimFirst)
  RingElem GReductor::myDoGBasisElimFirst(ConstRefPPMonoidElem ElimIndsProd)
  {
    VerboseLog VERBOSE("myDoGBasisElimFirst");
    //    CoCoA_ASSERT(myGetBuchbergerOpType() == HomogeneousAlg);
    myPrepareGBasis();
    //clog << "\nord = " << PPM(owner(poly(mySPoly))) << endl;
    //clog << "\ngens = " << myPairs << endl;
    while (!myPairs.empty())
    {
      myReduceCurrentSPoly();
      if (!IsZero(mySPoly))
      {
        if (IsCoprime(LPP(poly(mySPoly)), ElimIndsProd))
        {
          VERBOSE(100) << "--First Elim Poly found:"
                     << " len(GB) = " << len(myGB)
                     << " len(pairs) = " << len(myPairs)
                     << endl;
          myStat.myTotalTime-=CpuTime();
          if (VerbosityLevel() >= myStat.myFinalLevel)
            myStat.myStampa(VERBOSE(myStat.myFinalLevel));
          return poly(mySPoly);
        }
        myUpdateBasisAndPairs();
        VERBOSE_NewPolyInGB(VERBOSE, len(myGB), len(myPairs), mySPoly);
        // if (!myPairs.empty())
        //   if (myIncomingWDeg!=myOldDeg&&myTrueReductors.IhaveBorelReductors())
        //     myTrueReductors.myBorelReductorsUpdateInNextDegree();
      }
    } // while
    return zero(RingZZ()); // just to keep the compiler quiet
  } // myDoGBasisElimFirst


  // ANNA: called by TmpGOperations
  void GReductor::myDoGBasisSelfSatCore()
  {
    VerboseLog VERBOSE("myDoGBasisSelfSatCore");
    CoCoA_ASSERT(myGetBuchbergerOpType() == SaturatingAlg);
    VERBOSE(100) << "ring is " << myGRingInfoValue.myNewSPR() << std::endl;
    VERBOSE(100) << ordering(PPM(myGRingInfoValue.myNewSPR())) << endl;
    const long HIndetIndex=NumIndets(myGRingInfoValue.myNewSPR())-1;// This is OK for Ideals only
    degree SPolyPredDeg(GradingDim(myGRingInfoValue.myNewSPR()));// Used for stats in the dehmog alg
    myPrepareGBasis();
    //    double T=0.0;
    while (!myPairs.empty())
    {
      myReduceCurrentSPoly();
      if (!IsZero(mySPoly))
      {
      	SPolyPredDeg = wdeg(mySPoly);
        //mySPoly.smart_dehomog_DRL(HIndetIndex);
        mySPoly.smart_dehomog(HIndetIndex);
      	if (SPolyPredDeg!=wdeg(mySPoly))
      	{
          ++myStat.myPolyDHed;
          myStat.myDegDH += ConvertTo<long>((SPolyPredDeg-wdeg(mySPoly))[0]);
          //          if (VerbosityLevel() >= myStat.myPolyDHLevel && false)
          VERBOSE(100) << "Lower degree: "
                 <<SPolyPredDeg<< "-->"<<wdeg(mySPoly)<<" "
                 <<LPPForDiv(mySPoly)<<endl;
        } // if
        myUpdateBasisAndPairs();
        VERBOSE_NewPolyInGB(VERBOSE, len(myGB), len(myPairs), mySPoly);
      }
    } // while
    VERBOSE(100) << "--Final clean up ... " << endl;
    myFinalizeGBasis();
  } // myDoGBasisSelfSatCore


  void GReductor::myDoGBasisRealSolve()
  {
    VerboseLog VERBOSE("myDoGBasisRealSolve");
    SparsePolyRing P = myGRingInfo().myNewSPR();
    if (!IsZZ(CoeffRing(P)))  CoCoA_THROW_ERROR2(ERR::BadRing, "must be over QQ");
    SparsePolyRing PQQ = NewPolyRing(RingQQ(), NewSymbols(NumIndets(P)));
    RingHom P_PQQ = PolyRingHom(P, PQQ, ZZEmbeddingHom(PQQ), indets(PQQ));
    RingHom PQQ_P = PolyRingHom(PQQ, P, QQEmbeddingHom(P), indets(P));

    myPrepareGBasis();
    while (!myPairs.empty())
    {
      myReduceCurrentSPoly();
      if (!IsZero(mySPoly))
      {
//        RingElem RadSPoly = radical(P_PQQ(mySPoly.myPoly()));
        RingElem RadSPoly = RealRadical(P_PQQ(poly(mySPoly)));
        if (deg(RadSPoly) < deg(mySPoly.myPoly()))
          VERBOSE(70) << mySPoly.myPoly() << " [RealRadical]--> "
                       << RadSPoly << std::endl;
        GPoly GP(PQQ_P(ClearDenom(RadSPoly)), myGRingInfoValue, clear);
        GP.myInitializeSugar(sugar(mySPoly));
        myUpdateBasisAndPairs(GP);
        VERBOSE_NewPolyInGB(VERBOSE, len(myGB), len(myPairs), GP);
      }
    } // while
    VERBOSE(100) << "--Final clean up ... " << endl;
    myFinalizeGBasis();
    if (VerbosityLevel() >= myStat.myFinalLevel)
      myStat.myStampa(VERBOSE(myStat.myFinalLevel));
  } // myDoGBasisRealSolve


  void GReductor::myCreateInputPolyPairs(GPolyList& theCandidateBasis)
  {
    for (const auto& p: theCandidateBasis)
      Ordered_Insert(myPairs, GPair(p));
  } // myCreateInputPolyPairs


  // Prepare the first pairs; "input poly pairs"
  void GReductor::myPrepareGBasis()
  {
    VerboseLog VERBOSE("myPrepareGBasis");
    for (auto& p: myPolys)
      p.myInitializeSugar(myGRingInfoValue.myNewSugar(poly(p)));
    myCreateInputPolyPairs(myPolys);
    myPrepared=true;
    if (myGRingInfoValue.IamModule())
      myCriteria.myCoprime = false;// CopCriterion works only for REAL ideals
    CoCoA_ASSERT(len(myPairs)!=0);
    myIncomingWDeg = wdeg(myPairs.front());
    myOldDeg = myIncomingWDeg;
    myStat.myReductionTime=0.0; // STAT
    myStat.myTotalTime=CpuTime(); // STAT
    VERBOSE(myStat.myDegLevel) <<"--myIncomingWDeg="<<myIncomingWDeg<<endl;
  } // myPrepareGBasis


  void GReductor::myFinalizeGBasis()
  {
    const char* const FnName = "myFinalizeGBasis";
    VerboseLog VERBOSE(FnName);
    myStat.myTotalTime-=CpuTime();
    // interreduction
    if (true)  // always reduced gbasis
      if (myGRingInfo().myInputAndGrading()!=HOMOG) //myUpdateBasisAndPairs
      {
        VERBOSE(105) << "interreducing..." << std::endl;
        for (auto it=myGB.begin(); it!=myGB.end(); /*++it*/)
        {
          CheckForInterrupt(FnName);
          myGRingInfo().myCheckForTimeout(FnName);
          std::vector<ReductorData>::iterator it1=myTrueReductors.find(*it);
          it1->mySetIamNotToBeUsed(true);
          if (FindReducer(**it, myTrueReductors) != nullptr)  // surely -->0
          //if (IsZero(**it))    //  remove it
          {
            VERBOSE(110) << "--> zero" << endl;
            it = myGB.erase(it);
            //if (it != myGB.begin()) --it;
          }
          else
          {
            (**it).myReduce(myTrueReductors); // reduces tail
            CoCoA_ASSERT_ALWAYS(!IsZero(**it));
            VERBOSE(110) << "--> non zero" << endl;
            ++it;
            it1->mySetIamNotToBeUsed(false);
          }
        } // myGB for
      } // interreduction
  } // myFinalizeGBasis


} // end namespace cocoa
