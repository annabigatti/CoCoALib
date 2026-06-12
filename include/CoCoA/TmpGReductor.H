#ifndef CoCoA_GReductor_H
#define CoCoA_GReductor_H

//   Copyright (c)  2005-2017  John Abbott, Anna M. Bigatti
//   Author2:  2005-2010  Massimo Caboara, 2010-2017 Anna M. Bigatti 

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


//#include "CoCoA/CpuTimeLimit.H"
#include "CoCoA/GBEnv.H"
#include "CoCoA/TmpGPoly.H"
#include "CoCoA/TmpGPair.H"
#include "CoCoA/TmpGRStats.H"
#include "CoCoA/utils.H"


namespace CoCoA
{
  class FreeModule;     // forward declaration -- defined in FreeModule.H
  class SparsePolyRing; // forward declaration -- defined in SparsePolyRing.H

class GBCriteria
{
public:
  enum CoprimeFlag   { UseCoprime, DontUseCoprime };
  enum GMFlag        { UseGM, DontUseGM };
  enum BackFlag      { UseBack, DontUseBack };
  enum DivFlag       { UseDiv, DontUseDiv }; ///< remove poly if its LPP is divisible by LPP of new poly; true except for RingWeyl
  enum AllSetMarker  { AllSet };

public:
  GBCriteria(AllSetMarker) {myBack=true; myCoprime=true; myDiv=true; myGM=true;}
  GBCriteria(CoprimeFlag c, GMFlag gm, BackFlag b, DivFlag d)
  {
    myCoprime = (c == UseCoprime);
    myBack = (b == UseBack);
    myDiv = (d == UseDiv);
    myGM = (gm == UseGM);
  }
public:
  bool myBack;
  bool myCoprime;
  bool myDiv;
  bool myGM;
};

  class GReductor
  {
  public:

    enum BuchbergerOpTypeFlag { HomogeneousAlg, SaturatingAlg, AffineAlg };

    void myCtorAux(const BuchbergerOpTypeFlag theBuchbergerOpType);
    
    GReductor(const GRingInfo&,
              const PolyList&,
              const CpuTimeLimit& CheckForTimeout,
              const BuchbergerOpTypeFlag theBuchbergerOpType=HomogeneousAlg,
              const GBCriteria criteria=GBCriteria(GBCriteria::AllSet));
    GReductor(const GRingInfo&,
              const GPolyList&,
              const CpuTimeLimit& CheckForTimeout,
              const BuchbergerOpTypeFlag theBuchbergerOpType=HomogeneousAlg,
              const GBCriteria criteria=GBCriteria(GBCriteria::AllSet));
    GReductor(const GReductor&);// copy ctor not working, to be fixed
    ~GReductor(){};

    BuchbergerOpTypeFlag myGetBuchbergerOpType() const {return myBuchbergerOpType;}
    bool myPreparationDone() const {return myPrepared;}
    //    bool WrongLPPFound() const {return myWrongLPPFoundValue;}
    const Stats& myStats() const {return myStat;}

    long myReductorsLen() const {return myTrueReductors.myLen();}
    long myGBasisLen() const {return len(myGB);}
    long myPairsLen() const {return len(myPairs);}

    void mySetBuchbergerOpType(const BuchbergerOpTypeFlag theBuchbergerOpType) 
        {myBuchbergerOpType=theBuchbergerOpType;}

    std::vector<RingElem> myExportGBasis(); // pick & copy relevant elements
    std::vector<RingElem> myExportMinGens(); // pick & copy relevant elements

    void myDoAFFGBasis(); // I am working on sugar selection strategies
    void myDoGBasis();

    RingElem myDoGBasisElimFirst(ConstRefPPMonoidElem ElimIndsProd);
    void myReduceCurrentSPoly();
    void myPrepareGBasis();
    void myFinalizeGBasis();//Last operations (stats at the moment) immediately before shutting down a GB computation
    void myDoGBasis(const int ReductionNumber); // Performs ReductionNumber reductions, -1 means unlimited
    long myAge() const {return myAgeValue;}
    long myTruncDeg() const {return myTruncDegValue;}
    void mySetTruncDeg(long TruncDeg) { myTruncDegValue = TruncDeg; }
    static constexpr long ourNoTruncValue = -1;  // no GB truncation
    void myDoGBasisRealSolve();
    void myDoGBasisSelfSatCore(); ///< dehomog algorithm
    const SparsePolyRing& myPRing()const{return myGRingInfoValue.myP_work();};
    const GRingInfo& myGRingInfo()const{return myGRingInfoValue;};
    void myCreateInputPolyPairs(GPolyList&);

  private:
    long myGMInsert(GPairList&,GPair);
    void myBuildNewPairs(GPairList&);
    void myUpdateBasisAndPairs();
    void myUpdateBasisAndPairs(const GPoly& inPoly);
    void myUpdateIncomingWDeg();
    void myApplyBCriterion();


  private:  // member fields
    const GRingInfo myGRingInfoValue;
    GPairList myPairs;// here the polys are ptrs to myPolys
    Reductors myTrueReductors;// the true reductors.
    std::list<GPoly*> myGB;// the candidate Gbasis - NB polys are ptrs to myPolys
    GPolyList myPolys;// the REAL Polys, the other are ptrs
    GPoly mySPoly;
    degree myOldDeg;// used for flow control and stats. The degree it refers to is the degree of the pair
    degree myIncomingWDeg; // used for flow control and stats
    long myTruncDegValue;
    Stats myStat;// the statistics
    bool myPrepared; // Default false. True after a myPrepareGBasis has been performed
    long myAgeValue;
    GBCriteria myCriteria;
    BuchbergerOpTypeFlag myBuchbergerOpType; // Type of operation performed on the reductor
    static int ourDefaultStatLevel; ///< default verbosity level for statistics
//    CpuTimeLimit myCheckForTimeout;
  };// End class GReductor


}// end namespace cocoa

#endif
