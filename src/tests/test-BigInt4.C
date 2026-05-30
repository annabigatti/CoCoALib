//   Copyright (c)  2026  John Abbott,  Anna M. Bigatti

//   This file is part of the source of CoCoALib, the CoCoA Library.

//   CoCoALib is free software: you can redistribute it and/or modify
//   it under the terms of the GNU General Public License as published by
//   the Free Software Foundation, either version 3 of the License, or
//   (at your option) any later version.

//   CoCoALib is distributed in the hope that it will be useful,
//   but WITHOUT ANY WARRANTY; without even the implied warranty of
//   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//   GNU General Public License for more details.

//   You should have received a copy of the GNU General Public License
//   along with CoCoALib.  If not, see <http://www.gnu.org/licenses/>.


#include "CoCoA/BigIntOps.H"
#include "CoCoA/BuildInfo.H"
#include "CoCoA/GlobalManager.H"
#include "CoCoA/convert.H"
#include "CoCoA/error.H"

#include <cstdlib>
using std::abs;
#include <iostream>
using std::clog;
using std::cerr;
using std::endl;
#include<limits>
using std::numeric_limits;


namespace CoCoA
{

  // test IsExactRoot
  void program()
  {
    using std::abs;
    // This test checks the classes SumBigInt and ProdBigInt.
    GlobalManager CoCoAFoundations(UseGMPAllocator);

    SumBigInt S;
    const long n=1000;
    for (int i=0; i <= n; ++i)
      S += power(-1,i)*binomial(n,i);
    CoCoA_ASSERT_ALWAYS(IsZero(result(S)));

    ProdBigInt P;
    for (int i=1; i <= n; ++i)
      P *= i;
    CoCoA_ASSERT_ALWAYS(result(P) == factorial(n));
  }

} // end of namespace CoCoA


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
    cerr << "***ERROR***  UNCAUGHT CoCoA Error";
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
