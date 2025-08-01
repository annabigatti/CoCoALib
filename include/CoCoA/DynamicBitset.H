#ifndef CoCoA_DynamicBitset_H
#define CoCoA_DynamicBitset_H

//   Copyright (c)  2006-2010  Anna Bigatti, Massimo Caboara

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


#include "CoCoA/assert.H"
#include "CoCoA/error.H"
#include "CoCoA/utils.H" // for len

#include <bitset>
//using std::bitset;
#include <limits>
//using std::numeric_limits<long>::digits;
#include <vector>
//using std::vector;


namespace CoCoA
{

  class SparsePolyRing; // fwd decl -- defined in SparsePolyRing.H
  class RingElem; // fwd decl -- defined in ring.H
  class PPMonoid; // fwd decl -- defined in PPMonoid.H
  class PPMonoidElem; // fwd decl -- defined in PPMonoid.H
  class ConstRefPPMonoidElem; // fwd decl -- defined in PPMonoid.H

  class DynamicBitset
  {
  public:
    static constexpr long ourNumBitsInBlock =
      std::numeric_limits<unsigned long>::digits; // 32 or 64
    typedef std::bitset<ourNumBitsInBlock> BitBlock;
    enum class OutputStyle {clean, AsRevVecOfLong, WithSeparators};

    explicit DynamicBitset(long n=0);
    explicit DynamicBitset(ConstRefPPMonoidElem pp);
    //    explicit DynamicBitset(const std::vector<long>&);
    DynamicBitset(const DynamicBitset&);
    ~DynamicBitset(){};

    // inline
    long myLen() const noexcept { return myLenValue; }
    inline bool IamAll0s() const noexcept; ///< *this = [00000...0000]
    inline bool Iam1At(long index) const; ///< (*this)[index] == 1
    inline DynamicBitset& mySet(long index, bool val); ///< (*this)[index] = val
    DynamicBitset& mySet(long index) { return mySet(index, true); }

    inline DynamicBitset& operator=(const DynamicBitset& rhs);
    inline DynamicBitset& operator&=(const DynamicBitset& rhs); ///< and
    inline DynamicBitset& operator|=(const DynamicBitset& rhs); ///< or
    inline DynamicBitset& operator^=(const DynamicBitset& rhs); ///< xor
    inline DynamicBitset& operator-=(const DynamicBitset& rhs); ///< diff
    inline bool operator<(const DynamicBitset& rhs) const; ///< Xel????
    inline bool IamSubset(const DynamicBitset& rhs) const; ///< subset of rhs
    inline bool IamDisjoint(const DynamicBitset& rhs) const;

    bool operator==(const DynamicBitset& rhs) const noexcept {return myVec==rhs.myVec;}  // size check???
    bool operator!=(const DynamicBitset& rhs) const noexcept {return myVec!=rhs.myVec;}  // size check???
    // not inline
    bool IamAll1s() const noexcept; ///< *this = 11111...1111
    void myOutputSelf(std::ostream& out) const; ///<  as a bitset of same size
    void myOutputSelf8(std::ostream& out) const;  ///< blocks of 8/ourNumBitsInBlock
    void myOutputSelfLong(std::ostream& out) const;  ///< as reversed vector<unsigned long>


    //--------------------------------------------------
    // By Max: to be renamed into "|=" as in boost
    inline void operator+=(const DynamicBitset&);
    inline bool IamEmpty() const noexcept;
    inline bool IamNotEmpty() const noexcept; // Anna: remove
    inline bool myIsEntryThere(const unsigned int j) const;
    inline void mySetEntryThere(const unsigned int j,bool value);
    //

  private:
    void myResize(long n); ///< resize vector: only for ctors
    long myVecLen() const noexcept { return len(myVec); }

  private:  ///< member fields
    std::vector<BitBlock> myVec;
    long myLenValue;
    friend long count(const DynamicBitset& b) noexcept;
    friend DynamicBitset flip(DynamicBitset DB);

  public:
    static OutputStyle ourOutputStyle; ///< default: clean
  }; // end class DynamicBitset ----------------------------------------

  inline long len(const DynamicBitset& b) noexcept { return b.myLen(); }
  long count(const DynamicBitset& b) noexcept;
  // check length (to avoid checks do:  DynamicBitset b(b1);  b |= b2;)
  inline DynamicBitset operator|(const DynamicBitset&, const DynamicBitset&);
  inline DynamicBitset operator&(const DynamicBitset&, const DynamicBitset&);
  inline DynamicBitset operator-(const DynamicBitset&, const DynamicBitset&);
  inline DynamicBitset operator^(const DynamicBitset&, const DynamicBitset&);
  DynamicBitset flip(DynamicBitset DB);
  inline bool IsSubset(const DynamicBitset&, const DynamicBitset&);
  inline bool IsDisjoint(const DynamicBitset&, const DynamicBitset&);
  inline bool Is1At(const DynamicBitset&, long index);

  std::ostream& operator<<(std::ostream&, const DynamicBitset&);
  PPMonoidElem NewPP(const PPMonoid&, const DynamicBitset&);


  // move (or remove) to TmpIsTree.H (Max)
  inline DynamicBitset operator+(const DynamicBitset&, const DynamicBitset&);
  inline DynamicBitset FacetIntersection(const DynamicBitset&, const DynamicBitset&);
  inline bool contains(const DynamicBitset&,const DynamicBitset&);
  inline bool AreDirectlyConnected(const DynamicBitset&,const DynamicBitset&);
  //


  //======================================================================
  // from Max: seem unused
//   inline bool lesser(const bool&, const bool&);


// Function Object: gives order for set<DynamicBitset>
//   class LexicographicOrderFacet
//   {
//   public:
//     bool operator()(const DynamicBitset& f1, const DynamicBitset& f2)const
//       {
//         return lesser(f1,f2);
//       }
//   }; // end class LexicographicOrderFacet, really a Function Object

///////////// inline facet functions ///////////////////////////////////////////

//   // Returns the list of the indices of the vertices in the facet
//   std::list<unsigned int> DynamicBitset::myVertices() const
//   {
//     std::list<unsigned int> l;
//     for (unsigned int i=0; i!=mySize(); ++i)
//       if (myTest(i))  l.push_back(i);
//     return l;
//   }//DynamicBitset::myVertices()


//   bool lesser(const bool& b1, const bool& b2)
//   {
//     if (!b1&&b2) return true;
//     return false;
//   }//lesser


//   bool DynamicBitset::lesser(const DynamicBitset& f2) const
//   {
//     for (std::vector<BitsetWordLen>::const_iterator it1=myVec.begin(), it2=f2.myVec.begin();
//          it1!=myVec.end(); ++it1,++it2)
//     {
//       for (unsigned int i=0; i!=WordLen; ++i)
//       {
// 	if ((*it1)[i] != (*it2)[i])
//           return (*it2)[i];
//       }//for
//     }//for
//     return false;
//   }//DynamicBitset::lesser


//   bool lesser(const DynamicBitset& f1, const DynamicBitset& f2)
//   {
//     return f1.lesser(f2);
//   }


  //----- inline member functions -----------------

  DynamicBitset& DynamicBitset::operator=(const DynamicBitset& rhs)
  {
    // should this check size????
    myLenValue = rhs.myLenValue;
    myVec = rhs.myVec;
    return *this;
  }


  DynamicBitset& DynamicBitset::operator&=(const DynamicBitset& rhs)
  {
    CoCoA_ASSERT(myLen() == rhs.myLen());
    //// Anna: this is slower
    //for (size_t i=mySize()-1; i!=0; --i)  myVec[i] &= rhs.myVec[i];
    std::vector<BitBlock>::iterator it = myVec.begin();
    std::vector<BitBlock>::const_iterator itr = rhs.myVec.begin();
    for ( ; itr!=rhs.myVec.end(); ++itr, ++it)  *it &= *itr;
    return *this;
  }


  DynamicBitset& DynamicBitset::operator|=(const DynamicBitset& rhs)
  {
    CoCoA_ASSERT(myLen() == rhs.myLen());
    std::vector<BitBlock>::iterator it = myVec.begin();
    std::vector<BitBlock>::const_iterator itr = rhs.myVec.begin();
    for ( ; itr!=rhs.myVec.end(); ++itr, ++it)  *it |= *itr;
    return *this;
  }


  DynamicBitset& DynamicBitset::operator^=(const DynamicBitset& rhs)
  {
    CoCoA_ASSERT(myLen() == rhs.myLen());
    std::vector<BitBlock>::iterator it = myVec.begin();
    std::vector<BitBlock>::const_iterator itr = rhs.myVec.begin();
    for ( ; itr!=rhs.myVec.end(); ++itr, ++it)  *it ^= *itr;
    return *this;
  }


  DynamicBitset& DynamicBitset::operator-=(const DynamicBitset& rhs)
  {
    CoCoA_ASSERT(myLen() == rhs.myLen());
    std::vector<BitBlock>::iterator it = myVec.begin();
    std::vector<BitBlock>::const_iterator itr = rhs.myVec.begin();
    for ( ; itr!=rhs.myVec.end(); ++itr, ++it)  *it &= ~(*itr);
    return *this;
  }


  bool DynamicBitset::operator<(const DynamicBitset& rhs) const
  {
    CoCoA_ASSERT(myLen() == rhs.myLen());
    std::vector<BitBlock>::const_reverse_iterator rit = myVec.rbegin();
    std::vector<BitBlock>::const_reverse_iterator ritr = rhs.myVec.rbegin();
    for ( ; ritr!=rhs.myVec.rend(); ++ritr, ++rit)
    {
      if ( rit->to_ulong() > ritr->to_ulong() )  return false;
      if ( rit->to_ulong() < ritr->to_ulong() )  return true;
    }
    return false;
  }


  bool DynamicBitset::IamSubset(const DynamicBitset& rhs) const
  {
    CoCoA_ASSERT(myLen() == rhs.myLen());
    std::vector<BitBlock>::const_iterator it = myVec.begin();
    std::vector<BitBlock>::const_iterator itr = rhs.myVec.begin();
    for ( ; itr!=rhs.myVec.end(); ++itr, ++it)
      //  if ( std::operator&(*it, *itr) != (*it) )  // Anna: slower
      if ( std::operator&(*it, ~(*itr)).any() )  return false;
    return true;
  }


  bool DynamicBitset::IamDisjoint(const DynamicBitset& rhs) const
  {
    CoCoA_ASSERT(myLen() == rhs.myLen());
    std::vector<BitBlock>::const_iterator it = myVec.begin();
    std::vector<BitBlock>::const_iterator itr = rhs.myVec.begin();
    for ( ; itr!=rhs.myVec.end(); ++itr, ++it)
      if ( std::operator&(*it, *itr).any() )  return false;
    return true;
  }


  bool DynamicBitset::Iam1At(long index) const // index is not checked???? 8-{
  {
    return myVec[index/ourNumBitsInBlock][index%ourNumBitsInBlock];
  }


  DynamicBitset& DynamicBitset::mySet(long index, bool val)  // index is not checked???? 8-{
  {
    myVec[index/ourNumBitsInBlock][index%ourNumBitsInBlock] = val;
    return *this;
  }


  bool DynamicBitset::IamAll0s() const noexcept
  {
    // for (std::vector<BitBlock>::const_iterator it=myVec.begin();
    //      it!=myVec.end(); ++it)
    //   if (it->any()) return false;
    for (const auto& block: myVec)
      if (block.any()) return false;
    return true;
  }



  //----- inline functions on DynamicBitset -----------------

  DynamicBitset operator&(const DynamicBitset& b1, const DynamicBitset& b2)
  {
    if (len(b1) != len(b2))  CoCoA_THROW_ERROR1(ERR::IncompatDims);
    DynamicBitset b(b1);
    b &= b2;
    return b;
  }


  DynamicBitset operator|(const DynamicBitset& b1, const DynamicBitset& b2)
  {
    if (len(b1) != len(b2))  CoCoA_THROW_ERROR1(ERR::IncompatDims);
    DynamicBitset b(b1);
    b |= b2;
    return b;  // Anna: faster than "return b |= b2;" on PPC
  }


  DynamicBitset operator-(const DynamicBitset& b1, const DynamicBitset& b2)
  {
    if (len(b1) != len(b2))  CoCoA_THROW_ERROR1(ERR::IncompatDims);
    DynamicBitset b(b1);
    b -= b2;
    return b;
  }


  DynamicBitset operator^(const DynamicBitset& b1, const DynamicBitset& b2)
  {
    if (len(b1) != len(b2))  CoCoA_THROW_ERROR1(ERR::IncompatDims);
    DynamicBitset b(b1);
    b ^= b2;
    return b;
  }


  bool IsSubset(const DynamicBitset& b1, const DynamicBitset& b2)
  {
    if (len(b1) != len(b2))  CoCoA_THROW_ERROR1(ERR::IncompatDims);
    return b1.IamSubset(b2);
  }


  bool IsDisjoint(const DynamicBitset& b1, const DynamicBitset& b2)
  {
    if (len(b1) != len(b2))  CoCoA_THROW_ERROR1(ERR::IncompatDims);
    return b1.IamDisjoint(b2);
  }


  bool Is1At(const DynamicBitset& b, long index)
  {
    if (index < 0 || index >= len(b))  CoCoA_THROW_ERROR1(ERR::OutOfRange);
    return b.Iam1At(index);
  }

  //----------------------------------------------------------------------
  // Anna ask Max: can be removed?
  bool DynamicBitset::IamEmpty() const noexcept
  { return IamAll0s(); }  // Anna remove?


  bool DynamicBitset::IamNotEmpty() const noexcept
  { return !IamAll0s(); }  // Anna remove?


  void DynamicBitset::operator+=(const DynamicBitset& rhs)
  {  (*this) |= rhs;  }

  // inspects entry j in myFacet
  // Expensive
  bool DynamicBitset::myIsEntryThere(const unsigned int j) const // index j not range checked?  (assert?)
  { return Iam1At(j); }

  // sets entry j in myVec to value
  // Expensive
  void DynamicBitset::mySetEntryThere(const unsigned int j,bool value) // index j not range checked?  (assert?)
  { mySet(j, value); }


  // Anna: move to TmpIsTree
  DynamicBitset operator+(const DynamicBitset& v1, const DynamicBitset& v2)
  { return v1 | v2; }

  DynamicBitset FacetIntersection(const DynamicBitset& v1, const DynamicBitset& v2)
  { return v1 & v2; }

  // f1 contains f2
  bool contains(const DynamicBitset& f1,const DynamicBitset& f2)
  { return IsSubset(f2, f1); }

  // FacetIntersection(f1,f2)!=emptyset
  bool AreDirectlyConnected(const DynamicBitset& f1,const DynamicBitset& f2)
  { return !IsDisjoint(f1, f2); }

  //



}// end namespace cocoa

#endif
