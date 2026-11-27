#include "shifted_reverse.hpp"
#include <chrono>
#include <iostream>
#include <random>
#include <vector>
#include <cstdlib>
using namespace bb6_shifted;
static I scalar(const Block& b,I z,U* word){
 *word=0;
 if(z>=b.F)return missing;
 for(int j=b.k-1;j>=0;--j){
  I q=b.q+j;
  if(z>=q)return missing;
  U x=2*U(z)+((b.Y>>j)&1);
  if(x>=q){*word|=U(1)<<j;x-=q;}
  z=I(x);
 }
 return z;
}
static void require(bool h){if(!h){std::cerr<<"mismatch\n";std::exit(1);}}
int main(){
 std::mt19937_64 rng(0x9d3b9b2c);
 U small=0,large=0,simd=0;
 for(unsigned mode=0;mode<=5;++mode){
  fit_mode=mode;
  for(I F=18;F<=90;++F)for(I rem=1;rem<=9;++rem){
   Block b(F,rem);
   for(U Y=0;Y<(U(1)<<b.k);++Y){b.Y=Y;
    for(I z=0;z<F;++z){U a=0,c=0;auto x=scalar(b,z,&a),y=b.parent(z,&c);require(x==y&&(x==missing||a==c));++small;}
   }
  }
  for(unsigned trial=0;trial<50000;++trial){
   I F=18+I(rng()%2147483629ull);Block b(F,1+I(rng()%42));b.Y=rng()&((U(1)<<b.k)-1);
   alignas(64) U zz[8],out[8];
   for(unsigned i=0;i<8;++i){zz[i]=rng()%(F+U(1));U a=0,c=0;auto x=scalar(b,I(zz[i]),&a),y=b.parent(I(zz[i]),&c);require(x==y&&(x==missing||a==c));++large;}
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
   Block8 v(b);_mm512_store_si512(out,v.parent_vec(_mm512_load_si512(zz),255));
   for(unsigned i=0;i<8;++i){U a;require(out[i]==scalar(b,I(zz[i]),&a));++simd;}
#endif
  }
 }
 std::cout<<"exact small="<<small<<" large="<<large<<" simd="<<simd<<"\n";
 // Same endpoint population and target seed; differing block lengths mean
 // the metric is clock-queries/second, not a whole-scan speedup.
 for(I F: {100000000u,650000000u,1000000000u,2000000000u}){
  std::vector<U> zz(1<<20);for(auto& z:zz)z=rng()%F;
  for(unsigned mode=0;mode<=5;++mode){fit_mode=mode;Block b(F,64);b.Y=0x9abcdef01234ull&((U(1)<<b.k)-1);
   auto start=std::chrono::steady_clock::now();U sum=0;
   for(int pass=0;pass<12;++pass){
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
    Block8 v(b);__m512i acc=_mm512_setzero_si512();
    for(size_t j=0;j<zz.size();j+=8)acc=_mm512_add_epi64(acc,v.parent_vec(_mm512_loadu_si512(zz.data()+j),255));
    sum+=U(_mm512_reduce_add_epi64(acc));
#else
    for(U z:zz)sum+=b.parent(I(z));
#endif
   }
   double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
   std::cout<<"bench F="<<F<<" mode="<<mode<<" k="<<b.k<<" r="<<b.r<<" Mclock/s="<<12.0*zz.size()*b.k/sec/1e6<<" checksum="<<sum<<"\n";
  }
 }
}
