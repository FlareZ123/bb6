#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <bit>
#include <chrono>
#include <vector>
#include <algorithm>
using U=uint64_t; using I=int64_t;
struct State{U a,k;};
static inline bool bounce(U k,U c, State &s){
  if(c<4)return false;
  const U b=(k&1)?3:4,B=k+b,N=c+2*B;
  int delta=int(std::bit_width(N))-int(std::bit_width(B))-2;
  unsigned n=delta>0?unsigned(delta):0;
  while((B<<(n+2))<N+3*n)++n;
  U K=(B<<n)-b,C=c+2*k+3*n-2*K;
  if(k&1){s={2*K+6-C,C};return true;}
  if(C==4){s={2*K+2,3};return true;}
  if(C==5)return false;
  s={2*K+8-C,C-1};return true;
}
static inline bool next(State &s){
  const U a=s.a,k=s.k;
  if(a>=2&&k&&2*k<=a){s={a-2*k,2*k+2};return true;}
  if(a>=2&&k)return bounce(a-1,2*k-a+3,s);
  if(a==0){if(k==0)return false;if(k==1){s={0,4};return true;}return bounce(1,2*k+1,s);}
  if(a==1){switch(k){case 0:s={5,1};return true;case 1:s={2,3};return true;case 2:s={2,5};return true;case 3:s={0,7};return true;default:return bounce(4,2*k-3,s);}}
  s={a-2,2};return true;
}
// Exact affine block. WordBlock.lean: block_certificate.
struct Coeff{int32_t c[2]; uint32_t p,q;uint16_t w,l;};
static std::vector<Coeff> table(unsigned bits){
  std::vector<Coeff> out(U(1)<<bits);
  for(U q=1;q<out.size();++q){
    Coeff &v=out[q];v.p=1;
    U gap=0;
    for(int j=int(bits)-1;j>=0;--j){
      ++gap;if(!(q&(U(1)<<j)))continue;
      U p=U(1)<<gap,w=3*gap+1;
      for(U o=0;o<2;++o){U parity=(o+v.w)&1;v.c[o]=I(p)*v.c[o]-I(v.w)+I(p)*I(2+parity)-I(w)-2*I(parity);}
      v.p*=p;v.q=p*v.q+1;v.w+=w;++v.l;gap=0;
    }
    assert(v.q==q>>std::countr_zero(q));
  }
  return out;
}
int main(int argc,char**argv){
  U i=argc>1?strtoull(argv[1],nullptr,10):0;
  State s{argc>2?strtoull(argv[2],nullptr,10):5,argc>3?strtoull(argv[3],nullptr,10):1};
  U end=argc>4?strtoull(argv[4],nullptr,10):1000000000;
  unsigned bits=argc>5?strtoul(argv[5],nullptr,10):12;
  assert(bits>=1&&bits<=20);
  auto coeffs=table(bits);
  U blocks=0,singles=0,checkpoint=(i/1000000000+1)*1000000000;
  const auto start=std::chrono::steady_clock::now();
  while(i<end){
    U mass=s.a+2*s.k;
    if(mass>=U(1)<<(62-bits)){puts("mass cap");return 2;}
    U q=(s.a<<bits)/mass;
    U limit=std::min(end,checkpoint);
    bool done=false;
    if(q&&q<coeffs.size()){
      const Coeff &v=coeffs[q];
      if(i+v.l<=limit&&mass>=8*U(v.p)){
        I a=I(U(v.p)*s.a)-I(U(v.q)*mass)+v.c[mass&1];
        U m=mass+v.w;
        if(a>=0&&I(m)-a+4>=20*I(v.p)){
          assert(((m-U(a))&1)==0);
          s={U(a),(m-U(a))/2};i+=v.l;++blocks;done=true;
        }
      }
    }
    if(!done){State old=s;if(!next(s)){printf("TERMINAL return=%llu a=%llu k=%llu mass=%llu\n",(unsigned long long)i,(unsigned long long)old.a,(unsigned long long)old.k,(unsigned long long)mass);return 0;}++i;++singles;}
    if(i==checkpoint||i==end){printf("LIVE return=%llu a=%llu k=%llu mass=%llu blocks=%llu singles=%llu elapsed=%.3f\n",(unsigned long long)i,(unsigned long long)s.a,(unsigned long long)s.k,(unsigned long long)(s.a+2*s.k),(unsigned long long)blocks,(unsigned long long)singles,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());fflush(stdout);if(i==checkpoint)checkpoint+=1000000000;}
  }
}
