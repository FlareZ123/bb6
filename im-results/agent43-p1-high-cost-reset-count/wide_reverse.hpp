#pragma once
// Exact shifted-divisor / high-bit greedy reverse block.
// mode 0: original fitted quotient and two digit weights.
// mode 1: shifted quotient; modes 2..5: extra greedy high bits.
// mode 6: shifted fit with exact fixed-point SIMD quotient estimate.
// mode 7: same exact quotient in sixteen 32-bit lanes, using modular low products.
// Proof: SHIFTED-REVERSE.md and ShiftedReverseBlock.lean.
#include <algorithm>
#include <cstdint>
#include <stdexcept>
#include <immintrin.h>

namespace bb6_shifted {
using U=uint64_t; using I=uint32_t;
constexpr I missing=UINT32_MAX;
inline unsigned fit_mode=2;
static inline U dw(U b){return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)+4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)+16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);}
static inline int log2floor(U x){return 63-__builtin_clzll(x);}
static inline int fit(I F,I rem){
 if(F<3||!rem)throw std::runtime_error("reverse clock");
 if(!fit_mode)return int(std::min({rem,I(30),I(std::max(1,log2floor(F)-1))}));
 return int(std::min({rem,I(32),I(log2floor(F-1)+(fit_mode>=6?1:fit_mode)-1),F-2}));
}
struct Block {
 I q; int k,r; U Y,F,M,G; double inv; bool legacy,integer;
 Block(I end,I rem):q(end-fit(end,rem)),k(fit(end,rem)),r(k),Y(0),F(end),legacy(!fit_mode),integer(fit_mode>=6){
  if(!legacy){while(r>1&&(U(1)<<r)>U(q)+r-1)--r;}
  G=legacy?F:U(q)+r-1;M=(U(1)<<r)-1;inv=1.0/G;
  if(!legacy&&(U(1)<<r)>G)throw std::runtime_error("shifted fit");
 }
 I parent(I z,U* word=nullptr)const{
  if(z>=F)return missing;
  U X=(U(z)<<k)+Y,high=0;
  for(int i=k-1;i>=r;--i){
   U w=(U(q)+i)<<i;
   if(X>=w){X-=w;high|=U(1)<<i;}
  }
  U b=U(double(X)*inv);
  if(b*G>X)--b;else if((b+1)*G<=X)++b;
  if(b*G>X||(b+1)*G<=X)b=X/G;
  if(b>M)return missing;
  U c=X-(U(q)*b+dw(b));
  if(c<U(q)){if(word)*word=high|b;return I(c);}
  U u=b+1;
  if(u>M)return missing;
  if(legacy)c=X-(U(q)*u+dw(u));
  else c-=U(q)+2*(u&-u)-2;
  if(c<U(q)){if(word)*word=high|u;return I(c);}
  return missing;
 }
};
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
struct Block8 {
 const Block& b; __m512i G,q,M,Y,shift,one,zero,two; __m512d inv;
 __m512i R,S,cm[5];
 explicit Block8(const Block& x):b(x),G(_mm512_set1_epi64(x.G)),q(_mm512_set1_epi64(x.q)),M(_mm512_set1_epi64(x.M)),Y(_mm512_set1_epi64(x.Y)),shift(_mm512_set1_epi64(x.k)),one(_mm512_set1_epi64(1)),zero(_mm512_setzero_si512()),two(_mm512_set1_epi64(2)),inv(_mm512_set1_pd(x.inv)){
  if(x.integer){
   if(x.k!=x.r||x.G>UINT32_MAX||x.F>=UINT32_MAX||x.k>31)throw std::runtime_error("integer reciprocal range");
   constexpr U H=U(1)<<32;
   // R is clipped only at G=M_radix; the theorem permits equality
   // in the upper R inequality and requires strictness only for S.
   U rr=std::min(H-1,((x.M+1)<<32)/x.G),ss=(x.Y<<32)/x.G;
   R=_mm512_set1_epi64(rr);S=_mm512_set1_epi64(ss);
   U masks[5]={};for(unsigned i=0;i<unsigned(x.k);++i)
    for(unsigned j=0;j<5;++j)if((unsigned(x.k-1)-i)>>j&1)masks[j]|=U(1)<<i;
   for(unsigned j=0;j<5;++j)cm[j]=_mm512_set1_epi64(masks[j]);
  }
 }
 static __m512i wt(__m512i w){
  auto a=_mm512_and_si512(w,_mm512_set1_epi64(0xAAAAAAAAAAAAAAAAull));
  auto b=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xCCCCCCCCCCCCCCCCull)),1);
  auto c=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xF0F0F0F0F0F0F0F0ull)),2);
  auto d=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xFF00FF00FF00FF00ull)),3);
  auto e=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xFFFF0000FFFF0000ull)),4);
  return _mm512_add_epi64(_mm512_add_epi64(_mm512_add_epi64(a,b),_mm512_add_epi64(c,d)),e);
 }
 __m512i parent_integer(__m512i z,__mmask8 active)const{
  active&=_mm512_cmp_epu64_mask(z,_mm512_set1_epi64(b.F),_MM_CMPINT_LT);
  z=_mm512_maskz_mov_epi64(active,z);
  auto X=_mm512_add_epi64(_mm512_sllv_epi64(z,shift),Y);
  // All inputs are <2^32; VPMULUDQ computes exact 32x32->64.
  auto B=_mm512_srli_epi64(_mm512_add_epi64(_mm512_mul_epu32(z,R),S),32);
  auto rem=_mm512_sub_epi64(X,_mm512_mul_epu32(B,G));
  auto up=_mm512_cmp_epu64_mask(rem,G,_MM_CMPINT_NLT);
  B=_mm512_mask_add_epi64(B,up,B,one);
  rem=_mm512_mask_sub_epi64(rem,up,rem,G);
  // X-qB-D(B) = rem + sum_i (k-1-i)*bit_i(B)*2^i.
  auto a=_mm512_and_si512(B,cm[0]);
  auto d=_mm512_slli_epi64(_mm512_and_si512(B,cm[1]),1);
  auto e=_mm512_slli_epi64(_mm512_and_si512(B,cm[2]),2);
  auto f=_mm512_slli_epi64(_mm512_and_si512(B,cm[3]),3);
  auto g=_mm512_slli_epi64(_mm512_and_si512(B,cm[4]),4);
  auto c0=_mm512_add_epi64(rem,_mm512_add_epi64(_mm512_add_epi64(a,d),_mm512_add_epi64(_mm512_add_epi64(e,f),g)));
  auto B1=_mm512_add_epi64(B,one);
  auto low=_mm512_and_si512(B1,_mm512_sub_epi64(zero,B1));
  auto delta=_mm512_add_epi64(q,_mm512_sub_epi64(_mm512_slli_epi64(low,1),two));
  auto c1=_mm512_sub_epi64(c0,delta);
  auto good0=active&_mm512_cmp_epu64_mask(c0,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B,M,_MM_CMPINT_LE);
  auto good1=active&_mm512_cmp_epu64_mask(c1,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B1,M,_MM_CMPINT_LE);
  auto c=_mm512_mask_blend_epi64(good1,_mm512_set1_epi64(missing),c1);
  return _mm512_mask_mov_epi64(c,good0,c0);
 }
 __m512i parent_vec(__m512i z,__mmask8 active)const{
  if(b.integer)return parent_integer(z,active);
  active&=_mm512_cmp_epu64_mask(z,_mm512_set1_epi64(b.F),_MM_CMPINT_LT);
  auto X=_mm512_add_epi64(_mm512_sllv_epi64(z,shift),Y);
  X=_mm512_maskz_mov_epi64(active,X);
  for(int i=b.k-1;i>=b.r;--i){
   auto w=_mm512_set1_epi64((U(b.q)+i)<<i);
   auto take=_mm512_cmp_epu64_mask(X,w,_MM_CMPINT_NLT);
   X=_mm512_mask_sub_epi64(X,take,X,w);
  }
  auto B=_mm512_cvttpd_epu64(_mm512_mul_pd(_mm512_cvtepu64_pd(X),inv));
  auto BG=_mm512_mullo_epi64(B,G);
  auto hi=_mm512_cmp_epu64_mask(BG,X,_MM_CMPINT_GT);
  auto lo=_mm512_cmp_epu64_mask(_mm512_add_epi64(BG,G),X,_MM_CMPINT_LE);
  B=_mm512_mask_sub_epi64(B,hi,B,one);B=_mm512_mask_add_epi64(B,lo,B,one);
  BG=_mm512_mullo_epi64(B,G);
  auto bad=_mm512_cmp_epu64_mask(BG,X,_MM_CMPINT_GT)|_mm512_cmp_epu64_mask(_mm512_add_epi64(BG,G),X,_MM_CMPINT_LE);
  auto c0=_mm512_sub_epi64(X,_mm512_add_epi64(_mm512_mullo_epi64(B,q),wt(B)));
  auto good0=active&_mm512_cmp_epu64_mask(c0,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B,M,_MM_CMPINT_LE);
  auto B1=_mm512_add_epi64(B,one);
  __m512i c1;
  if(b.legacy)c1=_mm512_sub_epi64(X,_mm512_add_epi64(_mm512_mullo_epi64(B1,q),wt(B1)));
  else{
   auto low=_mm512_and_si512(B1,_mm512_sub_epi64(zero,B1));
   auto delta=_mm512_add_epi64(q,_mm512_sub_epi64(_mm512_slli_epi64(low,1),two));
   c1=_mm512_sub_epi64(c0,delta);
  }
  auto good1=active&_mm512_cmp_epu64_mask(c1,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B1,M,_MM_CMPINT_LE);
  auto c=_mm512_mask_blend_epi64(good1,_mm512_set1_epi64(missing),c1);
  c=_mm512_mask_mov_epi64(c,good0,c0);
  bad&=active;
  if(bad){alignas(64) U in[8],out[8];_mm512_store_si512(in,z);_mm512_store_si512(out,c);
   while(bad){unsigned j=__builtin_ctz(bad);bad&=bad-1;out[j]=b.parent(I(in[j]));}
   c=_mm512_load_si512(out);
  }
  return c;
 }
};
// Only the fixed-point numerator requires 64 bits. Since F<2^31, the
// provisional remainder is <2G<2^32 and its low word is the full remainder.
// All valid-word shifted corrections and adjacent gaps are likewise <2G.
struct Block16 {
 __m512i G,q,M,Y,shift,one,two,zero,F,R,S,cm[5];
 explicit Block16(const Block& b):G(_mm512_set1_epi32(b.G)),q(_mm512_set1_epi32(b.q)),M(_mm512_set1_epi32(b.M)),Y(_mm512_set1_epi32(b.Y)),shift(_mm512_set1_epi32(b.k)),one(_mm512_set1_epi32(1)),two(_mm512_set1_epi32(2)),zero(_mm512_setzero_si512()),F(_mm512_set1_epi32(b.F)){
  if(!b.integer||b.k!=b.r||b.F>INT32_MAX||b.k>30)throw std::runtime_error("integer lane range");
  constexpr U H=U(1)<<32;
  U rr=std::min(H-1,((b.M+1)<<32)/b.G),ss=(b.Y<<32)/b.G;
  R=_mm512_set1_epi64(rr);S=_mm512_set1_epi64(ss);
  I masks[5]={};for(unsigned i=0;i<unsigned(b.k);++i)
   for(unsigned j=0;j<5;++j)if((unsigned(b.k-1)-i)>>j&1)masks[j]|=I(1)<<i;
  for(unsigned j=0;j<5;++j)cm[j]=_mm512_set1_epi32(masks[j]);
 }
 __m512i parent_vec(__m512i z,__mmask16 active)const{
  active&=_mm512_cmp_epu32_mask(z,F,_MM_CMPINT_LT);
  z=_mm512_maskz_mov_epi32(active,z);
  auto ev=_mm512_add_epi64(_mm512_mul_epu32(z,R),S);
  auto od=_mm512_add_epi64(_mm512_mul_epu32(_mm512_srli_epi64(z,32),R),S);
  auto B=_mm512_mask_blend_epi32(0xAAAA,_mm512_srli_epi64(ev,32),od);
  auto Xlo=_mm512_add_epi32(_mm512_sllv_epi32(z,shift),Y);
  auto rem=_mm512_sub_epi32(Xlo,_mm512_mullo_epi32(B,G));
  auto up=_mm512_cmp_epu32_mask(rem,G,_MM_CMPINT_NLT);
  B=_mm512_mask_add_epi32(B,up,B,one);
  rem=_mm512_mask_sub_epi32(rem,up,rem,G);
  auto a=_mm512_and_si512(B,cm[0]);
  auto d=_mm512_slli_epi32(_mm512_and_si512(B,cm[1]),1);
  auto e=_mm512_slli_epi32(_mm512_and_si512(B,cm[2]),2);
  auto f=_mm512_slli_epi32(_mm512_and_si512(B,cm[3]),3);
  auto g=_mm512_slli_epi32(_mm512_and_si512(B,cm[4]),4);
  auto c0=_mm512_add_epi32(rem,_mm512_add_epi32(_mm512_add_epi32(a,d),_mm512_add_epi32(_mm512_add_epi32(e,f),g)));
  auto B1=_mm512_add_epi32(B,one);
  auto low=_mm512_and_si512(B1,_mm512_sub_epi32(zero,B1));
  auto delta=_mm512_add_epi32(q,_mm512_sub_epi32(_mm512_slli_epi32(low,1),two));
  auto c1=_mm512_sub_epi32(c0,delta);
  auto good0=active&_mm512_cmp_epu32_mask(c0,q,_MM_CMPINT_LT)&_mm512_cmp_epu32_mask(B,M,_MM_CMPINT_LE);
  // Explicit non-underflow guard is essential for 32-bit lanes.
  auto good1=active&_mm512_cmp_epu32_mask(c0,delta,_MM_CMPINT_NLT)&_mm512_cmp_epu32_mask(c1,q,_MM_CMPINT_LT)&_mm512_cmp_epu32_mask(B1,M,_MM_CMPINT_LE);
  auto c=_mm512_mask_blend_epi32(good1,_mm512_set1_epi32(missing),c1);
  return _mm512_mask_mov_epi32(c,good0,c0);
 }
};
#endif
} // namespace bb6_shifted
