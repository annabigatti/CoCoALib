// Copyright (c) 2017  John Abbott,  Anna M. Bigatti
// This file is part of the CoCoALib suite of examples.
// You are free to use any part of this example in your own programs.

#include "CoCoA/library.H"

using namespace std;

//----------------------------------------------------------------------
const string ShortDescription =
  "This example show how to call IdealOfPoints.  \n";

const string LongDescription =
  "This short example show how to call IdealOfPoints.                \n"
  "The points are specified as rows of a matrix (over some field k). \n"
  "You need a polynomial ring for the answer: its coeff ring must be \n"
  "the same field k as used in the matrix.                           \n";

//----------------------------------------------------------------------

namespace CoCoA
{

  void program()
  {
    GlobalManager CoCoAFoundations;

    cout << ShortDescription << endl;
    cout << boolalpha; // so that bools print out as true/false

    const int DimOfSpace = 3;
    const int NumPoints = 4;
    const ring& k = RingQQ();
    PolyRing P = NewPolyRing(k, SymbolRange("x", 1,DimOfSpace));
    matrix M = NewDenseMat(k, NumPoints, DimOfSpace);
    // Fill rows of M with the points:
    for (int i=0; i < NumPoints; ++i)
    {
      for (int j=0; j < DimOfSpace; ++j)
        SetEntry(M,i,j, RandomLong(-9,9)); //  random point
    }
    ideal I = IdealOfPoints(P, M);
    cout << "Points are the rows of " << M << endl;
    cout << "Ideal of all polys which vanish at these points:" << endl << I << endl;

    matrix M1 = NewDenseMat(RowMat(M, 0));
    I = IdealOfProjectivePoints(P, M1);
    cout << "Points are the rows of " << M1 << endl;
    cout << "Ideal of all homog polys which vanish at these points:" << endl << I << endl;

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

//----------------------------------------------------------------------
// RCS header/log in the next few lines
// $Header: /Volumes/Home_1/cocoa/cvs-repository/CoCoALib-0.99/examples/ex-IdealOfPoints1.C,v 1.6 2024/03/08 08:14:53 bigatti Exp $
// $Log: ex-IdealOfPoints1.C,v $
// Revision 1.6  2024/03/08 08:14:53  bigatti
// Summary: using  RowMat  instead of  submat  for getting one rwo only.
//
// Revision 1.5  2022/02/13 09:56:56  abbott
// Summary: Updated copyright (John & Anna in almost all cases, redmine 855)
//
// Revision 1.4  2018/09/28 15:54:03  abbott
// Summary: Removed pseudo-ctors NewPolyRing which took just num of indets; now must specify their names
//
// Revision 1.3  2017/07/08 19:07:02  abbott
// Summary: Removed comment out (dodgy) code for reporting unhandled interrupts
//
// Revision 1.2  2017/03/08 15:31:25  bigatti
// -- added IdealOfProjectivePoints
//
// Revision 1.1  2017/02/08 17:00:44  abbott
// Summary: New example for IdealOfPoints
//
// Revision 1.11  2016/11/18 18:05:15  abbott
// Summary: Added commented out code to catch InterruptReceived
//
// Revision 1.10  2015/06/29 14:23:19  abbott
// Summary: added missing CoCoA:: prefix
// Author: JAA
//
// Revision 1.9  2015/06/29 13:25:54  bigatti
// -- code in namespace CoCoA
//
// Revision 1.8  2015/06/25 14:19:02  abbott
// Summary: Added call to CoCoA::BuildInfo::Printall
// Author: JAA
//
// Revision 1.7  2013/05/28 07:07:04  bigatti
// -- added "cout << boolalpha": useful for testing
//
// Revision 1.6  2012/11/30 14:04:55  abbott
// Increased visibility of comment saying "put your code here".
//
// Revision 1.5  2010/12/17 16:07:54  abbott
// Ensured that all i/o in examples is on standard C++ streams
// (rather than GlobalInput(), etc).
//
// Revision 1.4  2008/10/07 12:12:54  abbott
// Removed useless commented out #include.
//
// Revision 1.3  2007/05/31 16:06:16  bigatti
// -- removed previous unwanted checked-in version
//
// Revision 1.1.1.1  2007/03/09 15:16:11  abbott
// Imported files
//
// Revision 1.9  2007/03/07 11:51:40  bigatti
// -- improved test alignment
//
// Revision 1.8  2007/03/03 14:15:45  bigatti
// -- "foundations" renamed into "GlobalManager"
//
// Revision 1.7  2007/03/02 17:46:40  bigatti
// -- unique RingZ and RingQ
// -- requires foundations.H ;  foundations blah;  (thik of a better name)
//
// Revision 1.6  2007/03/02 10:47:53  cocoa
// First stage of RingZ modifications -- tests do not compile currently, Anna will fix this.
//
// Revision 1.5  2007/03/01 13:52:59  bigatti
// -- minor: fixed typo
//
// Revision 1.4  2007/02/28 15:15:56  bigatti
// -- minor: removed quotes in description
//
// Revision 1.3  2007/02/12 16:27:43  bigatti
// -- added strings ShortDescription and LongDescription for indexing
//
// Revision 1.2  2007/02/10 18:44:03  cocoa
// Added "const" twice to each test and example.
// Eliminated dependency on io.H in several files.
// Improved BuildInfo, and added an example about how to use it.
// Some other minor cleaning.
//
// Revision 1.1.1.1  2006/05/30 11:39:36  cocoa
// Imported files
//
// Revision 1.1  2006/03/12 21:28:34  cocoa
// Major check in after many changes
//
