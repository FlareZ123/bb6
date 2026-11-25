#pragma once
#include <algorithm>
#include <array>
#include <cstdint>
#include <vector>
#include <stdexcept>
// D(B)=sum j 2^j bit_j(B), evaluated by fixed index-bit masks.
static inline uint64_t digitWeight(uint64_t b){
 return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)
 +4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)
 +16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);
}
// Largest block k <= remaining with k*2^k <= F-k, for q=F-k.
static inline int fit(int F,int remaining){
 int k=1;while(k<remaining&&k<25&&uint64_t(k+1)*(uint64_t(1)<<(k+1))<=uint64_t(F-k-1))++k;return k;
}
// Fixed-target exact reverse block. y is little-endian in original
// chronological order, X=2^k*z+y, c=X-q*B-D(B). For a legal
// block 0<=D(B)<q and 0<=c<q, hence B=floor(X/q) or one less.
// Interior at c and y=0 guarantee every intermediate interior guard.
static inline int blockParent(int q,int k,int z,uint64_t y,bool strict){
 uint64_t X=(uint64_t(z)<<k)+y, b=X/uint64_t(q), max=(uint64_t(1)<<k)-1;
 for(int i=0;i<2;++i){
  if(b<=max){uint64_t f=uint64_t(q)*b+digitWeight(b);
   if(f<=X){uint64_t c=X-f;
    if(strict?(c>=1&&c+3<=uint64_t(q)):c<uint64_t(q))return int(c);
   }
  }
  if(!b)break;--b;
 }
 return -1;
}
// Sorted vector by nonnegative 32-bit key .c; scratch is reused.
template<class Entry> static void radix(std::vector<Entry>&a,std::vector<Entry>&b){
 if(a.size()<12000){std::sort(a.begin(),a.end(),[](Entry x,Entry y){return x.c<y.c;});return;}
 b.resize(a.size());
 for(unsigned shift:{0,16}){
  std::array<uint32_t,65536> count{};
  for(auto x:a)++count[(uint32_t(x.c)>>shift)&65535];
  uint32_t sum=0;for(auto &x:count){uint32_t n=x;x=sum;sum+=n;}
  for(auto x:a)b[count[(uint32_t(x.c)>>shift)&65535]++]=x;
  a.swap(b);
 }
}
