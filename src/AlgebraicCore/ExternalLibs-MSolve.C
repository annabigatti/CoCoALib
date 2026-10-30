//   Copyright (c)  2026  John Abbott,  Anna M. Bigatti
//   Original author: 2026  Anna M. Bigatti

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


// Source code for Msolve integration

#include "CoCoA/ExternalLibs-MSolve.H"

#ifdef CoCoA_WITH_MSOLVE

#include "CoCoA/BigInt.H"
#include "CoCoA/BigRat.H"
#include "CoCoA/DenseMatrix.H"
#include "CoCoA/DenseUPolyRing.H"
#include "CoCoA/PPMonoid.H"
#include "CoCoA/RingFp.H"
#include "CoCoA/RingQQ.H"
#include "CoCoA/RingZZ.H"
#include "CoCoA/SparsePolyIter.H"
#include "CoCoA/SparsePolyOps-RingElem.H"
#include "CoCoA/SparsePolyOps-ideal.H"
#include "CoCoA/VectorOps.H"
#include "CoCoA/convert.H"
#include "CoCoA/error.H"
#include "CoCoA/ideal.H"
#include "CoCoA/matrix.H"
#include "CoCoA/ring.H"
#include "CoCoA/symbol.H"
#include "CoCoA/time.H"
#include "CoCoA/utils.H" // for len
#include "CoCoA/verbose.H"
#include <gmp.h>
#include <iostream>
#include <limits> // for numeric_limits<int32_t>::max()
#include <math.h>
// The recipe that works: Include the system headers neogb needs first
extern "C" {//----------------------
#include <msolve/neogb/libneogb.h>
}//---------------------------------
#include <msolve/msolve/msolve.h>
#include <ostream>
#include <sstream>  // for 
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <vector>
// using std::ostream;
using std::string;
using std::vector;


namespace CoCoA
{

  const char* MSolveVersion()
  {
    return MSOLVE_VERSION_STR;
//    return constants::version;
  }


#ifndef MSDEMO_H
#define MSDEMO_H


/* strdup() is POSIX, not ISO C: roll our own so -std=c11 builds cleanly. */
static inline char *msdemo_strdup(const char *s)
{
    size_t n = strlen(s) + 1;
    char *p = (char *)malloc(n); // anna 2026-10
    memcpy(p, s, n);
    return p;
}


/* Common part: everything except the coefficients. */
static inline data_gens_ff_t *msdemo_skeleton(int32_t nvars, const char *const *vnames,
                                       int32_t field_char, int32_t ngens,
                                       const int32_t *lens,
                                       const int32_t *exps)
{
    int32_t nterms = 0;
    for (int32_t i = 0; i < ngens; i++) nterms += lens[i];

    data_gens_ff_t *gens = allocate_data_gens();

    gens->nvars      = nvars;
    gens->ngens      = ngens;
    gens->nterms     = nterms;
    gens->field_char = field_char;
    gens->elim       = 0;

    /* allocate_data_gens() does not touch these three */
    gens->change_var_order      = -1;
    gens->linear_form_base_coef = 0;
    gens->rand_linear           = 0;

    gens->random_linear_form = (int32_t *)malloc(sizeof(int32_t) * (size_t)nvars);

    gens->vnames = (char **)malloc(sizeof(char *) * (size_t)nvars);
    for (int32_t i = 0; i < nvars; i++) gens->vnames[i] = msdemo_strdup(vnames[i]);

    gens->lens = (int32_t *)malloc(sizeof(int32_t) * (size_t)ngens);
    memcpy(gens->lens, lens, sizeof(int32_t) * (size_t)ngens);

    gens->exps = (int32_t *)malloc(sizeof(int32_t) * (size_t)nterms * (size_t)nvars);
    memcpy(gens->exps, exps, sizeof(int32_t) * (size_t)nterms * (size_t)nvars);

    return gens;
}

/* Build a system with rational coefficients (field_char == 0).
 * `num` and `den` hold one entry per term, in the same order as `exps`. */
data_gens_ff_t *msdemo_gens_qq(int32_t nvars, const char *const *vnames,
                               int32_t ngens, const int32_t *lens,
                               const int32_t *exps,
                               const long *num, const long *den)
{
    data_gens_ff_t *gens = msdemo_skeleton(nvars, vnames, 0, ngens, lens, exps);
    const int32_t nterms = gens->nterms;

    gens->mpz_cfs = (mpz_t **)malloc(sizeof(mpz_t *) * 2 * (size_t)nterms);
    for (long i = 0; i < 2 * nterms; i++) {
      gens->mpz_cfs[i] = (mpz_t *)malloc(sizeof(mpz_t));
        mpz_init(*(gens->mpz_cfs[i]));
    }
    for (long i = 0; i < nterms; i++) {
        mpz_set_si(*(gens->mpz_cfs[2 * i]),     num[i]);
        mpz_set_si(*(gens->mpz_cfs[2 * i + 1]), den ? den[i] : 1);
    }
    /* msolve's parser allocates this scratch buffer over Q as well */
    gens->cfs = (int32_t *)malloc(sizeof(int32_t) * (size_t)nterms);
    return gens;
}


  namespace { // anonymous
    // fill ms data with given CoCoA data

    void vnames_CoCoAfill(char** vnames, const SparsePolyRing& P)
    {
      for (long i=0; i<NumIndets(P); ++i)
      {
        std::ostringstream os;
        os << indet(P,i);
        vnames[i] = msdemo_strdup(os.str().c_str());
      }
    }
  
  
    void lens_CoCoAfill(int32_t *lens, const ideal& I)
    {
      const std::vector<RingElem>& F = gens(I);
      for (long i=0; i<NumGens(I); ++i)
        lens[i] = NumTerms(F[i]); 
    }
  
  
    void cfs_exps_CoCoAfill(mpz_t ** mpz_cfs, int32_t *exps, const ideal& I)
    {
      const std::vector<RingElem>& F = gens(I);
      long N = NumIndets(RingOf(I));
      long TermPos =-1;
      for (long i=0; i<NumGens(I); ++i)
        for (SparsePolyIter iter=BeginIter(F[i]); !IsEnded(iter); ++iter)
        {
          ++TermPos;
          BigRat c = ConvertTo<BigRat>(coeff(iter));
          mpz_set(*(mpz_cfs[2 * TermPos]),     mpzref(num(c)));
          mpz_set(*(mpz_cfs[2 * TermPos + 1]), mpzref(den(c)));
          std::vector<long> e = exponents(PP(iter));
          //std::cout << "   e is  " << e << std::endl;
          for (long j=0; j<N; ++j)  exps[TermPos*N+j] = e[j];
        }
    }

    void cfs_exps_CoCoAfill(int32_t * cfs, int32_t *exps, const ideal& I)
    {
      const std::vector<RingElem>& F = gens(I);
      long N = NumIndets(RingOf(I));
      long TermPos =-1;
      for (long i=0; i<NumGens(I); ++i)
        for (SparsePolyIter iter=BeginIter(F[i]); !IsEnded(iter); ++iter)
        {
          ++TermPos;
          long c = ConvertTo<long>(coeff(iter));
          //std::cout << "   c is  " << c << std::endl;
          cfs[TermPos] = c;
          std::vector<long> e = exponents(PP(iter));
          //std::cout << "   e is  " << e << std::endl;
          for (long j=0; j<N; ++j)  exps[TermPos*N+j] = e[j];
        }
    }

    // put output into CoCoA format -------------------------------------------

    std::vector<RingElem> ms_ToRingElems(SparsePolyRing P, void* bcf, int32_t* bexp, int32_t* blen, int32_t bld, int64_t nb)
    {
      const long N = NumIndets(P);
      const bool HasInt32Coeffs = not(IsQQ(CoeffRing(P)));
      std::vector<RingElem> G;
      
      mpz_t   *mpz_cf;
      int32_t *int32_cf;
      if (HasInt32Coeffs) int32_cf = (int32_t *)bcf;
      else mpz_cf = (mpz_t *)bcf;
      long t = 0;
      for (long i=0; i<bld; ++i)
      {
        RingElem g(P);
        for (long j=0; j<blen[i]; ++j, ++t)
        {
          //          BigInt c=BigIntFromMPZ(cf[t]);
          RingElem T=one(P);
          for (long v=0; v<N; ++v)  T *= IndetPower(P, v, bexp[t*N + v]);
          if (HasInt32Coeffs) g += int32_cf[t]*T;
          else    g += BigIntFromMPZ(mpz_cf[t])*T;
        }
        G.push_back(g);
      }
      return G;
    }
    
  }  // anonymous namespace

  data_gens_ff_t* ms_GetGens(const ideal& I)
  {
    SparsePolyRing P = RingOf(I);

    int32_t nterms = 0;
    for (const auto& f: gens(I)) nterms += NumTerms(f);
    
    data_gens_ff_t *gens = allocate_data_gens();

    gens->nvars      = NumIndets(P);
    gens->ngens      = NumGens(I);
    gens->nterms     = nterms;
    gens->field_char = ConvertTo<long>(characteristic(P));
    gens->elim       = 0;
    // std::cout << "nvars: " << gens->nvars << std::endl;
    // std::cout << "ngens: " << gens->ngens << std::endl;
    // std::cout << "nterms: " << gens->nterms << std::endl;
    // std::cout << "field_char: " << gens->field_char << std::endl;

    /* allocate_data_gens() does not touch these three */
    gens->change_var_order      = -1;
    gens->linear_form_base_coef = 0;
    gens->rand_linear           = 0;
    
    gens->random_linear_form = (int32_t *)malloc(sizeof(int32_t) * (size_t)(gens->nvars));
    
    gens->vnames = (char **)malloc(sizeof(char *) * (size_t)(gens->nvars));
    vnames_CoCoAfill(gens->vnames, P);
    //std::cout << "indets: ";
    //for (long i=0; i<gens->nvars; ++i)  std::cout << " " << gens->vnames[i];
    //std::cout << std::endl;

    gens->lens = (int32_t *)malloc(sizeof(int32_t) * (size_t)(gens->ngens));
    lens_CoCoAfill(gens->lens, I);
    //std::cout << "lens: ";
    //for (long i=0; i<gens->ngens; ++i)  std::cout << " " << gens->lens[i];
    //std::cout << std::endl;
    
    /* msolve's parser allocates this scratch buffer over Q as well */
    gens->cfs = (int32_t *)malloc(sizeof(int32_t) * (size_t)nterms);
    gens->exps = (int32_t *)malloc(sizeof(int32_t) * (size_t)(gens->nterms) * (size_t)(gens->nvars));
    if (IsQQ(CoeffRing(P)))
    {
      gens->mpz_cfs = (mpz_t **)malloc(sizeof(mpz_t *) * 2 * (size_t)(gens->nterms));
      for (long i = 0; i < 2 * (gens->nterms); i++)
      {
        gens->mpz_cfs[i] = (mpz_t *)malloc(sizeof(mpz_t));
        mpz_init(*(gens->mpz_cfs[i]));
      }
      cfs_exps_CoCoAfill(gens->mpz_cfs, gens->exps, I);
    }
    else
      cfs_exps_CoCoAfill(gens->cfs, gens->exps, I);

    //std::cout << "exponents: ";
    //for (long i=0; i<(gens->nterms)*(gens->nvars); ++i)  std::cout << " " << gens->exps[i];
    //std::cout << std::endl;

    return gens;
  }



  
/* Build a system over the prime field F_p (field_char == p > 0). */
static inline data_gens_ff_t *msdemo_gens_ff(int32_t nvars, const char *const *vnames,
                                      int32_t field_char, int32_t ngens,
                                      const int32_t *lens, const int32_t *exps,
                                      const int32_t *cfs)
{
    data_gens_ff_t *gens =
        msdemo_skeleton(nvars, vnames, field_char, ngens, lens, exps);
    const int32_t nterms = gens->nterms;

    gens->cfs = (int32_t *)malloc(sizeof(int32_t) * (size_t)nterms);
    for (int32_t i = 0; i < nterms; i++) {
        int32_t c = cfs[i] % field_char;
        if (c < 0) c += field_char;
        gens->cfs[i] = c;
    }
    return gens;
}

/* A real_point_t coordinate is the dyadic interval
 *     [ val_do / 2^k_do , val_up / 2^k_up ].
 * Convert it to a double (midpoint) for display. */
static inline double msdemo_coord_to_double(coord_t c)
{
    double lo = mpz_get_d(c->val_do) / ldexp(1.0, (int)c->k_do);
    double hi = mpz_get_d(c->val_up) / ldexp(1.0, (int)c->k_up);
    return 0.5 * (lo + hi);
}

static inline void msdemo_print_real_point(real_point_t pt, char *const *vnames)
{
    printf("  (");
    for (long i = 0; i < pt->nvars; i++) {
        printf("%s = %+.12f", vnames ? vnames[i] : "x",
               msdemo_coord_to_double(pt->coords[i]));
        if (i + 1 < pt->nvars) printf(", ");
    }
    printf(")\n");
}

/* Print sum_i coeffs[i] * T^i */
static inline void msdemo_print_upoly(const char *name, mpz_upoly_t p)
{
    printf("  %s = ", name);
    if (p->length <= 0) { printf("0\n"); return; }
    int first = 1;
    for (long i = p->length - 1; i >= 0; i--) {
        if (mpz_sgn(p->coeffs[i]) == 0) continue;
        if (!first) printf(" + ");
        gmp_printf("%Zd", p->coeffs[i]);
        if (i > 0) printf("*T^%ld", i);
        first = 0;
    }
    if (first) printf("0");
    printf("\n");
}

#endif /* MSDEMO_H */


  std::vector<RingElem> MSolveGBasisQQ(const ideal& I)
  {
    SparsePolyRing P = RingOf(I);
    if (!IsQQ(CoeffRing(P))) // IsRingQQ
      CoCoA_THROW_ERROR2(ERR::ReqCoeffsInField, "QQ");
    if (OrdMat(P)!=StdDegRevLexMat(NumIndets(P)))
      CoCoA_THROW_ERROR2(ERR::NYI, "only StdDegRevLex");
    data_gens_ff_t *gens = ms_GetGens(I);

    int32_t   bld  = 0;
    int32_t  *blen = NULL;
    int32_t  *bexp = NULL;
    void     *bcf  = NULL;
    int64_t nb = export_groebner_qq(
            &malloc, &bld, &blen, &bexp, &bcf,
            gens->lens, gens->exps, (const void *)gens->mpz_cfs,
            /* field_char       */ gens->field_char,
            /* mon_order        */ 0,     /* 0 = grevlex */
            /* elim_block_len   */ 0,
            /* nr_vars          */ gens->nvars,
            /* nr_gens          */ gens->ngens,
            /* ht_size          */ 17,
            /* nr_threads       */ 1,
            /* max_nr_pairs     */ 0,
            /* reset_hash_table */ 0,
            /* la_option        */ 2,
            /* print_gb         */ 2,     /* 1 = leading ideal, 2 = full basis */
            /* reduce_gb        */ 1,
            /* pbm_file         */ 0,
            /* truncate_lifting */ 0,
            /* info_level       */ 0);
    //------------------------------------------------------
    std::vector<RingElem> GB = ms_ToRingElems(P, bcf,bexp,blen,bld,nb);
    //- ----------------------------------------------------
    mpz_t *cf = (mpz_t *)bcf;
    for (int64_t i = 0; i < nb; i++) mpz_clear(cf[i]);
    free(bcf);
    free(bexp);
    free(blen);
    free_data_gens(gens);
    //------------------------------------------------------
    return GB;
  }


  std::vector<RingElem> MSolveGBasisF4(const ideal& I)
  {
    SparsePolyRing P = RingOf(I);
    if (!IsRingFp(CoeffRing(P)))
      CoCoA_THROW_ERROR2(ERR::ReqCoeffsInField, "Fp");
    if (!characteristic(P) > numeric_limits<int32_t>::max())
      CoCoA_THROW_ERROR2(ERR::NYI, "characteristic is too large");
    if (OrdMat(P)!=StdDegRevLexMat(NumIndets(P)))
      CoCoA_THROW_ERROR2(ERR::NYI, "only StdDegRevLex");
    data_gens_ff_t *gens = ms_GetGens(I);

    int32_t   bld  = 0;
    int32_t  *blen = NULL;
    int32_t  *bexp = NULL;
    void     *bcf  = NULL;
    int64_t nb = export_f4(
            &malloc, &bld, &blen, &bexp, &bcf,
            gens->lens, gens->exps, (const void *)gens->cfs,
            /* field_char       */ gens->field_char,
            /* mon_order        */ 0,   /* 0 = grevlex, 1 = lex-ish block */
            /* elim_block_len   */ 0,
            /* nr_vars          */ gens->nvars,
            /* nr_gens          */ gens->ngens,
            /* ht_size          */ 17,
            /* nr_threads       */ 1,
            /* max_nr_pairs     */ 0,
            /* reset_hash_table */ 0,
            /* la_option        */ 2,
            /* reduce_gb        */ 1,
            /* pbm_file         */ 0,
            /* info_level       */ 0);
    //------------------------------------------------------
    std::vector<RingElem> GB = ms_ToRingElems(P, bcf,bexp,blen,bld,nb);
    //------------------------------------------------------
    free(bcf);
    free(bexp);
    free(blen);
    free_data_gens(gens);
    //------------------------------------------------------
    return GB;
  }

  std::vector<RingElem> MSolveGBasis(const ideal& I)
  {
    SparsePolyRing P = RingOf(I);
    if (IsQQ(CoeffRing(P)))
      return MSolveGBasisQQ(I);
    if (IsRingFp(CoeffRing(P)))
      return MSolveGBasisF4(I);
    CoCoA_THROW_ERROR2(ERR::NYI, "over Fp");
  }
  

}

#endif
