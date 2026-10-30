#ifndef CoCoA_msolve_H
#define CoCoA_msolve_H

//   Copyright (c)  2026  John Abbott,  Anna M. Bigatti
//   Original author: 2026 Anna M. Bigatti

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

#include "CoCoA/PREPROCESSOR_DEFNS.H"

#ifdef CoCoA_WITH_MSOLVE

// the following is for libneogb.h: neogb/data.h includes <gmp.h>, and <gmp.h> in C++ pulls in <iosfwd>
// which may not appear inside a C linkage block
#include <gmp.h>
extern "C" {
#include <msolve/neogb/libneogb.h>
}//--------------------^^^^^^^^^^----

#include <vector>
#include "msolve.h"

namespace CoCoA
{
  class ideal; // forward declaration -- defined in ideal.H
  class RingElem; // forward declaration -- defined in ring.H

  const char* MSolveVersion();

  // data_gens_ff_t *msdemo_gens_qq(int32_t nvars, const char *const *vnames,
  //                                int32_t ngens, const int32_t *lens,
  //                                const int32_t *exps,
  //                                const long *num, const long *den);
  
  std::vector<RingElem> MSolveGBasis(const ideal& I);

} // end of namespace CoCoA

#endif // CoCoA_WITH_MSOLVE

#endif
