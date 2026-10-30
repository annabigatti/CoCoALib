//   Copyright (c) 2026  Anna M. Bigatti,  John Abbott
//
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

//#include "BuiltInFunctions.H"
#include "BuiltInOneLiners.H"

using namespace std;
using namespace boost;
using namespace boost::iostreams;
using namespace CoCoA::AST;
using namespace CoCoA::LexerNS;
using namespace CoCoA::ParserNS;

namespace CoCoA {
namespace InterpreterNS {

//  extern std::vector<NameFunPair> builtIns; // declared in BuiltInFunctions.C

#ifndef CoCoA_WITH_MSOLVE

  DECLARE_MISSING_EXTLIB(MSolveGBasis, "MSOLVE")

#else

  //----- supplement

//----- one-liners
DECLARE_COCOALIB_FUNCTION1(MSolveGBasis, IDEAL)

//----- other
// variable number of args
// DECLARE_ARITYCHECK_FUNCTION(FrbAlexanderDual) { return (1<=nArg) && (nArg<=2); }
// DECLARE_BUILTIN_FUNCTION(FrbAlexanderDual) {
//   invocationExpression->checkNumberOfArgs(1,2);
// 	intrusive_ptr<IDEAL> I = runtimeEnv->evalArgAs<IDEAL>(ARG(0));
//   if (invocationExpression->args.size()==1)
//     return Value::from(FrbAlexanderDual(I->theIdeal));
// 	intrusive_ptr<RINGELEM> t = runtimeEnv->evalArgAs<RINGELEM>(ARG(1));
//   return Value::from(FrbAlexanderDual_forC5(I->theIdeal, t->theRingElem));
// }


#endif // CoCoA_WITH_MSOLVE

} // namespace AST
} // namespace CoCoA
