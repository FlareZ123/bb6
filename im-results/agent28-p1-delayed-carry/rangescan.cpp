#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#ifdef __BMI2__
#include <immintrin.h>
#endif
#include <vector>
using namespace std;
// Compress 64 bits into 32 even-position bits.
static inline uint32_t even(uint64_t x) {
#ifdef __BMI2__
 return _pext_u64(x,0x5555555555555555ULL);
#else
 x &= 0x5555555555555555ULL;
 x = (x | (x >> 1)) & 0x3333333333333333ULL;
 x = (x | (x >> 2)) & 0x0f0f0f0f0f0f0f0fULL;
 x = (x | (x >> 4)) & 0x00ff00ff00ff00ffULL;
 x = (x | (x >> 8)) & 0x0000ffff0000ffffULL;
 x = (x | (x >> 16)) & 0xffffffffULL;
 return uint32_t(x);
#endif
}
struct Result{unsigned k,w,peak;};
struct Scan {
 vector<unsigned> a,b;
 vector<uint64_t> u,v;
 Result run(unsigned n,unsigned cutoff){
  a.assign(1,(n+2)/2);unsigned k=1,peak=1;
  for(;k<cutoff && !a.empty();){
   unsigned C=n+k+3;
   if(a.size()*128 < C){
    b.clear();for(auto p:a){if(!(p&1))b.push_back(p/2);if(!((p+C)&1))b.push_back((p+C)/2);}
    a.swap(b);++k;peak=max(peak,unsigned(a.size()));continue;
   }
   // All carries in [0,C). At most one predecessor within [0,C) for each output.
   unsigned words=(C+64)/64;
   u.assign(words,0);for(unsigned p:a)u[p>>6]|=1ULL<<(p&63);
   while(k<cutoff){
    C=n+k+3;unsigned outWords=(C+1+63)/64;v.assign(outWords,0);
    int shift=C>>6; unsigned r=C&63;
    auto get=[&](int i)->uint64_t{return i>=0&&unsigned(i)<u.size()?u[i]:0;};
    unsigned count=0;
    for(unsigned i=0;i<outWords;++i){
     uint64_t x=0;
     for(unsigned t=0;t<2;++t){int z=2*i+t;uint64_t y=get(z-shift)<<r;if(r)y|=get(z-shift-1)>>(64-r);x|=uint64_t(even(get(z)|y))<<(32*t);}
     v[i]=x;count+=__builtin_popcountll(x);
    }
    u.swap(v);++k;peak=max(peak,count);
    if(!count)return {k,0,peak};
    if(k==cutoff)return {k,count,peak};
    if(count*256<C){a.clear();for(unsigned i=0;i<u.size();++i){uint64_t x=u[i];while(x){unsigned t=__builtin_ctzll(x);a.push_back(64*i+t);x&=x-1;}}break;}
   }
  }
  return {k,unsigned(a.size()),peak};
 }
};
int main(int argc,char**argv){unsigned lo=argc>1?stoul(argv[1]):10002,hi=argc>2?stoul(argv[2]):1000000;Scan s;constexpr unsigned D=4096;vector<unsigned> depth(D);for(unsigned r=0;r<D;r+=2){auto z=s.run(r,12);if(!z.w)depth[r]=z.k;}
 uint64_t done=0,early=0,exceptions=0;unsigned deepest=0,maxN=0;auto start=chrono::steady_clock::now();for(unsigned n=lo;n<=hi;n+=2){unsigned k=depth[n%D];if(k){++early;}else{auto z=s.run(n,n);k=z.k;if(z.w||k+32>n){cout<<n<<" "<<k<<" "<<z.w<<" "<<z.peak<<endl;++exceptions;}}if(k>deepest){deepest=k;maxN=n;}++done;if(n%10000==2)cerr<<n<<" checked="<<done<<" early="<<early<<" exceptions="<<exceptions<<" maxK="<<deepest<<" at "<<maxN<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;}
 cerr<<"DONE "<<done<<" early="<<early<<" exceptions="<<exceptions<<" maxK="<<deepest<<" at "<<maxN<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
