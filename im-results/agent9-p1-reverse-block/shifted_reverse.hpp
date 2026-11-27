#pragma once
// Exact shifted-divisor / high-bit greedy reverse block.
// mode 0: original fitted quotient and two digit weights.
// mode 1: shifted quotient; mode >=2: allow mode-1 extra high bits.
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
 return int(std::min({rem,I(32),I(log2floor(F-1)+fit_mode-1),F-2}));
}
struct Block {
 I q; int k,r; U Y,F,M,G; double inv; bool legacy;
 Block(I end,I rem):q(end-fit(end,rem)),k(fit(end,rem)),r(k),Y(0),F(end),legacy(!fit_mode){
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
 explicit Block8(const Block& x):b(x),G(_mm512_set1_epi64(x.G)),q(_mm512_set1_epi64(x.q)),M(_mm512_set1_epi64(x.M)),Y(_mm512_set1_epi64(x.Y)),shift(_mm512_set1_epi64(x.k)),one(_mm512_set1_epi64(1)),zero(_mm512_setzero_si512()),two(_mm512_set1_epi64(2)),inv(_mm512_set1_pd(x.inv)){}
 static __m512i wt(__m512i w){
  auto a=_mm512_and_si512(w,_mm512_set1_epi64(0xAAAAAAAAAAAAAAAAull));
  auto b=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xCCCCCCCCCCCCCCCCull)),1);
  auto c=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xF0F0F0F0F0F0F0F0ull)),2);
  auto d=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xFF00FF00FF00FF00ull)),3);
  auto e=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xFFFF0000FFFF0000ull)),4);
  return _mm512_add_epi64(_mm512_add_epi64(_mm512_add_epi64(a,b),_mm512_add_epi64(c,d)),e);
 }
 __m512i parent_vec(__m512i z,__mmask8 active)const{
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
#endif
} // namespace bb6_shifted
