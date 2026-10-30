// Copyright (c) 2026  John Abbott and Anna M. Bigatti
// Authors: Anna M. Bigatti
// This file is part of the CoCoALib suite of examples.
// You are free to use any part of this example in your own programs.

#include "CoCoA/library.H"

///// first prototype
#include "CoCoA/ExternalLibs-MSolve.H"

using namespace std;

//----------------------------------------------------------------------
const string ShortDescription =
  "This program shows a prototype for msolve communication.";

const string LongDescription =
  "Function MSolveGBasis(I)\n"
  "calls export_groebner_qq or export_f4.";

//----------------------------------------------------------------------

namespace CoCoA
{  



void program()
  {
    GlobalManager CoCoAFoundations;

    cout << endl << ShortDescription << endl;
    cout << LongDescription << endl;
    cout << boolalpha; // so that bools print out as true/false

#ifndef CoCoA_WITH_MSOLVE
    cout << "msolve library is not available to CoCoALib." << endl;
#else // MSOLVE is available

    cout << " -----------------------------------------------" << endl;
    ring P = NewPolyRing(RingQQ(), symbols("x,y"));
    ideal I = ideal(RingElems(P, "x^2 + y^2 - 4 , x*y - 1"));
    std::cout << " I is " << I << " in " << P << std::endl;    
    std::cout << " GBasis(I)       gives " << GBasis(I) << std::endl;
    std::cout << " MSolveGBasis(I) gives " << MSolveGBasis(I) << std::endl;
    std::cout << " -^^^^^^^^^^^^^- calls export_groebner_qq (degrevlex)" << std::endl;

    cout << " -----------------------------------------------" << endl;
    const uint32_t p = 1073741827; /* 31 bits -> 32-bit coefficients */
    ring Pp = NewPolyRing(NewZZmod(p), symbols("x,y"));
    ideal Ip = ideal(RingElems(Pp, "x^2 + y^2 - 4 , x*y - 1"));
    std::cout << " Ip is " << Ip << " in " << Pp << std::endl;    
    std::cout << " GBasis(Ip)       gives " << GBasis(Ip) << std::endl;
    std::cout << " MSolveGBasis(Ip) gives " << MSolveGBasis(Ip) << std::endl;
    std::cout << " -^^^^^^^^^^^^^^- calls export_f4 (degrevlex)" << std::endl;

#endif // CoCoA_WITH_MSOLVE
  }


} // end of namespace CoCoA

//----------------------------------------------------------------------
// Use main() to handle any uncaught exceptions and warn the user about them.
int main()
{
  try
  {
    CoCoA::program();
    return 0;
  }
  catch (const CoCoA::ErrorInfo& err)
  {
    cerr << "***ERROR***  UNCAUGHT CoCoA error";
    ANNOUNCE(cerr, err);
  }
  catch (const std::exception& exc)
  {
    cerr << "***ERROR***  UNCAUGHT std::exception: " << exc.what() << endl;
  }
  catch(...)
  {
    cerr << "***ERROR***  UNCAUGHT UNKNOWN EXCEPTION" << endl;
  }

  CoCoA::BuildInfo::PrintAll(cerr);
  return 1;
}
