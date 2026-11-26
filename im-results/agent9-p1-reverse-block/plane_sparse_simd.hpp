#pragma once
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
#include <immintrin.h>
static __m512i dw8(__m512i B){
 auto a=_mm512_and_si512(B,_mm512_set1_epi64(0xAAAAAAAAAAAAAAAAull));
 auto b=_mm512_slli_epi64(_mm512_and_si512(B,_mm512_set1_epi64(0xCCCCCCCCCCCCCCCCull)),1);
 auto c=_mm512_slli_epi64(_mm512_and_si512(B,_mm512_set1_epi64(0xF0F0F0F0F0F0F0F0ull)),2);
 auto d=_mm512_slli_epi64(_mm512_and_si512(B,_mm512_set1_epi64(0xFF00FF00FF00FF00ull)),3);
 auto e=_mm512_slli_epi64(_mm512_and_si512(B,_mm512_set1_epi64(0xFFFF0000FFFF0000ull)),4);
 return _mm512_add_epi64(_mm512_add_epi64(a,b),_mm512_add_epi64(c,_mm512_add_epi64(d,e)));
}
struct Block8 {
 const Block& b;
 __m512i F,q,M,Y,shift,one;
 __m512d inv;
 explicit Block8(const Block& bb):b(bb),F(_mm512_set1_epi64(b.F)),q(_mm512_set1_epi64(b.q)),M(_mm512_set1_epi64(b.M)),Y(_mm512_set1_epi64(b.Y)),shift(_mm512_set1_epi64(b.k)),one(_mm512_set1_epi64(1)),inv(_mm512_set1_pd(b.inv)){}
 __mmask8 eval(const I* ptr,I* out)const{
  auto z=_mm512_cvtepu32_epi64(_mm256_loadu_si256((const __m256i*)ptr));
  auto X=_mm512_add_epi64(_mm512_sllv_epi64(z,shift),Y);
  auto B=_mm512_cvttpd_epu64(_mm512_mul_pd(_mm512_cvtepu64_pd(X),inv));
  auto P=_mm512_mullo_epi64(B,F);
  auto minus=_mm512_cmp_epu64_mask(P,X,_MM_CMPINT_GT);
  auto plus=_mm512_cmp_epu64_mask(_mm512_add_epi64(P,F),X,_MM_CMPINT_LE);
  B=_mm512_mask_sub_epi64(B,minus,B,one);
  B=_mm512_mask_add_epi64(B,plus,B,one);
  P=_mm512_mullo_epi64(B,F);
  auto bad=_mm512_cmp_epu64_mask(P,X,_MM_CMPINT_GT)|_mm512_cmp_epu64_mask(_mm512_add_epi64(P,F),X,_MM_CMPINT_LE);
  if(bad){
   alignas(64) U aa[8];_mm512_store_si512(aa,B);
   for(unsigned i=0;i<8;i++)if((bad>>i)&1)aa[i]=((U(ptr[i])<<b.k)+b.Y)/b.F;
   B=_mm512_load_si512(aa);
  }
  auto R=_mm512_sub_epi64(X,_mm512_add_epi64(_mm512_mullo_epi64(q,B),dw8(B)));
  auto good=_mm512_cmp_epu64_mask(R,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B,M,_MM_CMPINT_LT);
  if(good!=255){
   auto B1=_mm512_add_epi64(B,one);
   auto R1=_mm512_sub_epi64(X,_mm512_add_epi64(_mm512_mullo_epi64(q,B1),dw8(B1)));
   auto good1=__mmask8(~good)&_mm512_cmp_epu64_mask(R1,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B1,M,_MM_CMPINT_LT);
   R=_mm512_mask_mov_epi64(R,good1,R1);
   good|=good1;
  }
  _mm256_storeu_si256((__m256i*)out,_mm512_cvtepi64_epi32(R));
  return good;
 }
};
static void scalar_reverse(vector<I>& a,const Block& b,Bits& seen){
 size_t w=0;for(I z:a){I c;U B;if(b.parent(z,c,B)&&!seen.get(c)){seen.set(c);a[w++]=c;}}
 a.resize(w);for(I c:a)seen.a[c>>6]&=~(U(1)<<(c&63));
}
static void simd_reverse(vector<I>& a,const Block& b,Bits& seen){
 Block8 bb(b);
 size_t w=0,i=0;
 for(;i+8<=a.size();i+=8){
  I out[8];unsigned good=bb.eval(a.data()+i,out);
  while(good){
   unsigned j=__builtin_ctz(good);good&=good-1;
   I c=out[j];if(!seen.get(c)){seen.set(c);a[w++]=c;}
  }
 }
 for(;i<a.size();i++){
  I c;U B;if(b.parent(a[i],c,B)&&!seen.get(c)){seen.set(c);a[w++]=c;}
 }
 a.resize(w);for(I c:a)seen.a[c>>6]&=~(U(1)<<(c&63));
}
#else
static void simd_reverse(vector<I>& a,const Block& b,Bits& seen){
 size_t w=0;for(I z:a){I c;U B;if(b.parent(z,c,B)&&!seen.get(c)){seen.set(c);a[w++]=c;}}
 a.resize(w);for(I c:a)seen.a[c>>6]&=~(U(1)<<(c&63));
}
#endif
