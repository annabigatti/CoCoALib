//   Copyright (c)  2006,2007,2010-2012  John Abbott and Anna M. Bigatti

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

#include "CoCoA/random.H"

#include "CoCoA/BigIntOps.H"
#include "CoCoA/GlobalManager.H" // for GlobalRandomSource()
#include "CoCoA/MachineInt.H"
#include "CoCoA/ULong2Long.H"
#include "CoCoA/error.H"
#include "CoCoA/utils.H"

#include <iostream>
//using std::ostream;
#include <limits>
using std::numeric_limits;


namespace CoCoA
{

  RandomSource::RandomSource(const MachineInt& seed):
      mySeed(seed)
  {
    gmp_randinit_mt(myState);
    gmp_randseed(myState, mpzref(mySeed));
  }


  RandomSource::RandomSource(const BigInt& seed):
      mySeed(seed)
  {
    gmp_randinit_mt(myState);
    gmp_randseed(myState, mpzref(mySeed));
  }


  RandomSource::RandomSource(const RandomSource& copy):
      mySeed(copy.mySeed)
  {
    gmp_randinit_set(myState, copy.myState);
  }


  RandomSource& RandomSource::operator=(const RandomSource& rhs)
  {
    gmp_randclear(myState);                 // Together these effect an assignment
    gmp_randinit_set(myState, rhs.myState); //
    mySeed = rhs.mySeed;
    return *this;
  }


  RandomSource::~RandomSource()
  {
    gmp_randclear(myState);
  }


  long RandomLong(RandomSource& RndSrc, const MachineInt& lwb, const MachineInt& upb)
  {
    if (!IsSignedLong(lwb) || !IsSignedLong(upb))
      CoCoA_THROW_ERROR2(ERR::BadArg, "RandomLong: lwb & upb must each fit into a long");
    const long lo = AsSignedLong(lwb);
    const long hi = AsSignedLong(upb);
    if (lo > hi)  CoCoA_THROW_ERROR1(ERR::ReqNonEmpty);
    const unsigned long RangeWidth = 1ul + ULongDiff(hi,lo);
    if (RangeWidth == 0)
      return ULong2Long(gmp_urandomb_ui(RndSrc.myState, numeric_limits<unsigned long>::digits));
    return ULong2Long(lo + gmp_urandomm_ui(RndSrc.myState, RangeWidth)); // lo is silently converted to ulong
  }


  BigInt RandomBigInt(RandomSource& RndSrc, const MachineInt& lwb, const MachineInt& upb)
  {
    return RandomBigInt(RndSrc, BigInt(lwb), BigInt(upb));
  }

  BigInt RandomBigInt(RandomSource& RndSrc, const MachineInt& lwb, const BigInt& upb)
  {
    return RandomBigInt(RndSrc, BigInt(lwb), upb);
  }

  BigInt RandomBigInt(RandomSource& RndSrc, const BigInt& lwb, const MachineInt& upb)
  {
    return RandomBigInt(RndSrc, lwb, BigInt(upb));
  }

  BigInt RandomBigInt(RandomSource& RndSrc, const BigInt& lwb, const BigInt& upb)
  {
    if (lwb > upb)  CoCoA_THROW_ERROR1(ERR::ReqNonEmpty);
    BigInt sample;
    mpz_urandomm(mpzref(sample), RndSrc.myState, mpzref(upb-lwb+1));
    return lwb + sample;
  }

// NOTE (2011-04-26): this is significantly faster than the fn above.
//   BigInt RandomBigIntmod(RandomSource& RndSrc, const BigInt& M)
//   {
//     if (M <= 0)  CoCoA_THROW_ERROR1(ERR::ReqPositive);
//     BigInt sample;
//     mpz_urandomm(mpzref(sample), RndSrc.myState, mpzref(M));
//     return sample;
//   }


  void reseed(RandomSource& RndSrc, const MachineInt& seed)
  {
    reseed(RndSrc, BigInt(seed));
  }

  void reseed(RandomSource& RndSrc, const BigInt& seed)
  {
    RndSrc.mySeed = seed;
    gmp_randseed(RndSrc.myState, mpzref(RndSrc.mySeed));
    // zero any counters
  }


  std::ostream& operator<<(std::ostream& out, const RandomSource& RndSrc)
  {
    if (!out)  return out;  // short-cut for bad ostreams
    out << "RandomSource(seed=" << RndSrc.mySeed << ", state=unprintable)";
    return out;
  }


  bool RandomBool() noexcept
  { return RandomBool(GlobalRandomSource()); }

  bool RandomBiasedBool(double P)
  {
    // BAD DESIGN: This is an almost identical copy of NextBiasedBool(RandomSeqBool&,double)
    if (P < 0 || P > 1)  CoCoA_THROW_ERROR1(ERR::BadProbability);
    if (P == 1)  return true;
    while (true)
    {
      if (P == 0)  return false;
      const bool bit = (P >= 0.5);
      if (bit ^ RandomBool(GlobalRandomSource()))  return bit;
      P *= 2;
      if (bit) --P;
    }
  }

  bool RandomBiasedBool(unsigned long N, unsigned long D)
  {
    CoCoA_ASSERT(D <= numeric_limits<unsigned long>::max()/2);
    if (D == 0 || N > D)  CoCoA_THROW_ERROR1(ERR::BadProbability);
    if (N == D)  return true;
    while (true)
    {
      if (N == 0)  return false;
      N <<= 1;
      const bool bit = (N >= D);
      if (bit ^ RandomBool(GlobalRandomSource()))  return bit;
      if (bit) N -= D;
    }
  }

  long RandomLong(const MachineInt& lwb, const MachineInt& upb)
  { return RandomLong(GlobalRandomSource(), lwb, upb); }

  BigInt RandomBigInt(const MachineInt& lwb, const MachineInt& upb)
  { return RandomBigInt(GlobalRandomSource(), lwb, upb); }

  BigInt RandomBigInt(const MachineInt& lwb, const BigInt& upb)
  { return RandomBigInt(GlobalRandomSource(), lwb, upb); }

  BigInt RandomBigInt(const BigInt& lwb, const MachineInt& upb)
  { return RandomBigInt(GlobalRandomSource(), lwb, upb); }

  BigInt RandomBigInt(const BigInt& lwb, const BigInt& upb)
  { return RandomBigInt(GlobalRandomSource(), lwb, upb); }


  //////////////////////////////////////////////////////////////////


  RandomSeqLong::RandomSeqLong(const MachineInt& lwb, const MachineInt& upb, const MachineInt& seed):
      myLwb(AsSignedLong(lwb)),
      myUpb(AsSignedLong(upb)),
      myRange((1ul+myUpb) - myLwb), // all arith is between ulongs
      myValue(0), // initialized "properly" in the body
      myCounter(0),
      mySeed(uabs(seed)),
      myState() // init in body
  {
    if (myLwb > myUpb)
      CoCoA_THROW_ERROR1(ERR::ReqNonEmpty);
    gmp_randinit_mt(myState);
    gmp_randseed_ui(myState, mySeed);
    myGenValue();
  }

  RandomSeqLong::RandomSeqLong(const RandomSeqLong& copy):
      myLwb(copy.myLwb),
      myUpb(copy.myUpb),
      myRange(copy.myRange),
      myValue(copy.myValue),
      myCounter(copy.myCounter),
      mySeed(copy.mySeed),
      myState() //init in body
  {
    gmp_randinit_set(myState, copy.myState);
  }

  RandomSeqLong& RandomSeqLong::operator=(const RandomSeqLong& rhs)
  {
    if (this == &rhs) return *this; // this is necessary (because of call to gmp_randclear)
    myLwb = rhs.myLwb;
    myUpb = rhs.myUpb;
    myRange = rhs.myRange;
    myValue = rhs.myValue;
    myCounter = rhs.myCounter;
    mySeed = rhs.mySeed;
    gmp_randclear(myState);                 // Together these effect an assignment
    gmp_randinit_set(myState, rhs.myState); //

    return *this;
  }

  RandomSeqLong::~RandomSeqLong()
  {
    gmp_randclear(myState);
  }


  // Better define this in case some idiot wants to use it...
  // Not inline, so it is as slow as possible >-}
  RandomSeqLong RandomSeqLong::operator++(int)
  {
    RandomSeqLong ans(*this); // Probably not cheap!
    operator++();
    return ans; // Makes another copy upon returning!
  }


  long RandomSeqLong::myIndex() const noexcept
  {
    return myCounter;
  }


  void RandomSeqLong::myGenValue() noexcept
  {
    if (myRange > 0)
      myValue = ULong2Long(myLwb + gmp_urandomm_ui(myState, myRange)); // myLwb is silently converted to ulong, so sum is modulo MaxUlong+1
    else
      // Get here only if myLwb = min_long & myUpb = max_long
      myValue = ULong2Long(gmp_urandomb_ui(myState, numeric_limits<unsigned long>::digits));
  }


  std::ostream& operator<<(std::ostream& out, const RandomSeqLong& RndLong)
  {
    if (!out)  return out;  // short-cut for bad ostreams
    out << "RandomSeqLong(lwb=" << RndLong.myLwb
        << ", upb=" << RndLong.myUpb
        << ", seed=" << RndLong.mySeed
        << ", counter=" << RndLong.myCounter << ")";
    return out;
  }


  //////////////////////////////////////////////////////////////////


  RandomSeqBool::RandomSeqBool(const MachineInt& seed):
      myBitIndex(0),
      myBuffer(0),
      myCounter(0),
      mySeed(uabs(seed)),
      myState() // init in body
  {
    gmp_randinit_mt(myState);
    gmp_randseed_ui(myState, mySeed);
    myFillBuffer();
  }

  RandomSeqBool::RandomSeqBool(const RandomSeqBool& copy):
      myBitIndex(copy.myBitIndex),
      myBuffer(copy.myBuffer),
      myCounter(copy.myCounter),
      mySeed(copy.mySeed),
      myState() //init in body
  {
    gmp_randinit_set(myState, copy.myState);
  }

  RandomSeqBool& RandomSeqBool::operator=(const RandomSeqBool& rhs)
  {
    if (this == &rhs) return *this; // this is necessary (because of call to gmp_randclear)
    myBitIndex = rhs.myBitIndex;
    myBuffer = rhs.myBuffer;
    myCounter = rhs.myCounter;
    mySeed = rhs.mySeed;
    gmp_randclear(myState);                 // Together these effect an assignment
    gmp_randinit_set(myState, rhs.myState); //

    return *this;
  }

  RandomSeqBool::~RandomSeqBool()
  {
    gmp_randclear(myState);
  }


  // Better define this in case some idiot wants to use it...
  // Not inline, so it is as slow as possible >-}
  RandomSeqBool RandomSeqBool::operator++(int)
  {
    RandomSeqBool ans(*this); // Probably not cheap!
    operator++();
    return ans; // Makes another copy upon returning!
  }


  long RandomSeqBool::myIndex() const noexcept
  {
    return myCounter;
  }


  void RandomSeqBool::myFillBuffer()
  {
    myBuffer = std::bitset<ourBufferBits>(gmp_urandomb_ui(myState, ourBufferBits));
    myBitIndex = 0;
  }


  // This would be cleaner if I were to use an unsigned long instead of a double.
  bool NextBiasedBool(RandomSeqBool& RndBool, double P)
  {
    if (P < 0 || P > 1)  CoCoA_THROW_ERROR1(ERR::BadProbability);
    if (P == 1)  return true;
    while (true)
    {
      if (P == 0)  return false;
      const bool bit = (P >= 0.5);
      if (bit ^ NextValue(RndBool))  return bit;
      P *= 2;
      if (bit) --P;
    }
  }


  std::ostream& operator<<(std::ostream& out, const RandomSeqBool& RndBool)
  {
    if (!out)  return out;  // short-cut for bad ostreams
    out << "RandomSeqBool(seed=" << RndBool.mySeed << ", counter=" << RndBool.myCounter << ")";
    return out;
  }


  //////////////////////////////////////////////////////////////////


  RandomSeqBigInt::RandomSeqBigInt(const MachineInt& lwb, const MachineInt& upb, const MachineInt& seed):
      myLwb(lwb),
      myUpb(upb),
      myRange(1+myUpb-myLwb),
      myValue(0), // initialized "properly" in the body
      myCounter(0),
      mySeed(uabs(seed)),
      myState() // init in body
  {
    if (myLwb > myUpb)
      CoCoA_THROW_ERROR1(ERR::ReqNonEmpty);
    gmp_randinit_mt(myState);
    gmp_randseed_ui(myState, mySeed);
    myGenValue();
  }

  RandomSeqBigInt::RandomSeqBigInt(const MachineInt& lwb, const BigInt& upb, const MachineInt& seed):
      myLwb(lwb),
      myUpb(upb),
      myRange(1+myUpb-myLwb),
      myValue(0), // initialized "properly" in the body
      myCounter(0),
      mySeed(uabs(seed)),
      myState() // init in body
  {
    if (myLwb > myUpb)
      CoCoA_THROW_ERROR1(ERR::ReqNonEmpty);
    gmp_randinit_mt(myState);
    gmp_randseed_ui(myState, mySeed);
    myGenValue();
  }

  RandomSeqBigInt::RandomSeqBigInt(const BigInt& lwb, const MachineInt& upb, const MachineInt& seed):
      myLwb(lwb),
      myUpb(upb),
      myRange(1+myUpb-myLwb),
      myValue(0), // initialized "properly" in the body
      myCounter(0),
      mySeed(uabs(seed)),
      myState() // init in body
  {
    if (myLwb > myUpb)
      CoCoA_THROW_ERROR1(ERR::ReqNonEmpty);
    gmp_randinit_mt(myState);
    gmp_randseed_ui(myState, mySeed);
    myGenValue();
  }

  RandomSeqBigInt::RandomSeqBigInt(const BigInt& lwb, const BigInt& upb, const MachineInt& seed):
      myLwb(lwb),
      myUpb(upb),
      myRange(1+myUpb-myLwb),
      myValue(0), // initialized "properly" in the body
      myCounter(0),
      mySeed(uabs(seed)),
      myState() // init in body
  {
    if (myLwb > myUpb)
      CoCoA_THROW_ERROR1(ERR::ReqNonEmpty);
    gmp_randinit_mt(myState);
    gmp_randseed_ui(myState, mySeed);
    myGenValue();
  }


  RandomSeqBigInt::RandomSeqBigInt(const RandomSeqBigInt& copy):
      myLwb(copy.myLwb),
      myUpb(copy.myUpb),
      myRange(copy.myRange),
      myValue(copy.myValue),
      myCounter(copy.myCounter),
      mySeed(copy.mySeed),
      myState() //init in body
  {
    gmp_randinit_set(myState, copy.myState);
  }

  RandomSeqBigInt& RandomSeqBigInt::operator=(const RandomSeqBigInt& rhs)
  {
    if (this == &rhs) return *this; // this is necessary (because of call to gmp_randclear)
    myLwb = rhs.myLwb;
    myUpb = rhs.myUpb;
    myRange = rhs.myRange;
    myValue = rhs.myValue;
    myCounter = rhs.myCounter;
    mySeed = rhs.mySeed;
    gmp_randclear(myState);                 // Together these effect an assignment
    gmp_randinit_set(myState, rhs.myState); //

    return *this;
  }

  RandomSeqBigInt::~RandomSeqBigInt()
  {
    gmp_randclear(myState);
  }


  // Better define this in case some idiot wants to use it...
  // Not inline, so it is as slow as possible >-}
  RandomSeqBigInt RandomSeqBigInt::operator++(int)
  {
    RandomSeqBigInt ans(*this); // Probably not cheap!
    operator++();
    return ans; // Makes another copy upon returning!
  }


  long RandomSeqBigInt::myIndex() const noexcept
  {
    return myCounter;
  }


  void RandomSeqBigInt::myGenValue()
  {
    mpz_urandomm(mpzref(myValue), myState, mpzref(myRange));
    myValue += myLwb;
  }


  std::ostream& operator<<(std::ostream& out, const RandomSeqBigInt& RndBigInt)
  {
    if (!out) return out;  // short-cut for bad ostreams
    out << "RandomSeqBigInt(lwb=" << RndBigInt.myLwb
        << ", upb=" << RndBigInt.myUpb
        << ", seed=" << RndBigInt.mySeed
        << ", counter=" << RndBigInt.myCounter << ")";
    return out;
  }


} // end of namespace CoCoA
