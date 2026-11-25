#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>
using U=uint64_t; using I=int64_t; using W=__int128_t; using UW=__uint128_t;
struct State{U a,m; bool operator==(const State&)const=default;};
static inline State fromAK(U a,U k){return {a,a+2*k};}
static inline U right(State s){return (s.m-s.a)/2;}
static inline bool bounce(U k,U c,State &s){
  if(c<4)return false;
  U o=1-(k&1),b=3+o,B=k+b,N=c+2*B;
  int d=int(std::bit_width(N))-int(std::bit_width(B))-2; unsigned n=d>0?unsigned(d):0;
  while((UW(B)<<(n+2))<N+3*n)++n;
  U K=(B<<n)-b,C=c+2*k+3*n-2*K;
  if(!o){s=fromAK(2*K+6-C,C);return true;}
  if(C==4){s=fromAK(2*K+2,3);return true;}
  if(C==5)return false;
  s=fromAK(2*K+8-C,C-1);return true;
}
static inline bool next(State &s){
  U a=s.a,k=right(s);
  if(a>=2&&k&&2*k<=a){s=fromAK(a-2*k,2*k+2);return true;}
  if(a>=2&&k)return bounce(a-1,2*k-a+3,s);
  if(a==0){if(k==0)return false;if(k==1){s=fromAK(0,4);return true;}return bounce(1,2*k+1,s);}
  if(a==1){switch(k){case 0:s=fromAK(5,1);return true;case 1:s=fromAK(2,3);return true;case 2:s=fromAK(2,5);return true;case 3:s=fromAK(0,7);return true;default:return bounce(4,2*k-3,s);}}
  s=fromAK(a-2,2);return true;
}
// Exact bit interpreter: mass grows by 3+e, B doubles, and an event
// subtracts M_new-2+2*o-o_new. The old parity o is retained on idle bits.
// Each fixed-width chunk has B'=2^K B-q M+c; o' is stored for all 4 inputs.
struct Chunk{int32_t c[4]{};uint8_t p[4]{};uint8_t d=0,l=0;};
template<unsigned K> struct Tables{
  std::array<Chunk,U(1)<<K> t{};
  Tables(){for(U q=0;q<t.size();++q){auto &v=t[q];v.l=std::popcount(q);v.d=3*K+v.l;
    for(U in=0;in<4;++in){I c=0,dm=0;U o=in&1,mp=in>>1;for(int j=K-1;j>=0;--j){U e=(q>>j)&1;dm+=3+e;c*=2;if(e){U op=(mp+dm)&1;c-=dm-2+2*I(o)-I(op);o=op;}}v.c[in]=c;v.p[in]=((mp+dm)&1)*2+o;}
  }}
};
// Approximate quotient only. Refreshing/correcting changes acceptance rate,
// never the meaning of an accepted block. No predictor claim is trusted.
template<unsigned N> struct Reciprocal{
  U inv=0,base=0,slope=0,limit=0;
  inline U quotient(State s){
    if(!s.m)return 0;
    if(s.m<=U(1)<<N)return U((UW(s.a)<<N)/s.m);
    if(s.m<base||s.m>=limit||!inv){
      base=s.m;inv=U((UW(1)<<(64+N))/base);slope=U((UW(inv)+base/2)/base);
      // Bound rounding drift for performance at large masses. Correctness is
      // independent of refresh frequency because the word guard is exact.
      limit=base+std::max<U>(1,std::min<U>(4096,(U(1)<<56)/base));
    }
    return U(UW(s.a)*(inv-slope*(s.m-base))>>64);
  }
};
// Exact long-word guard of StreakWord, used if the simpler total-shift guard
// fails. It uses conservative bounds: max zero streak+1 for max shift, and
// max one streak for max direct streak. Final trailing ones overcount at most 1.
static inline bool streak_guard(U q,unsigned R,U mass,U gap){
  U mask=(U(1)<<R)-1,zeros=(~q)&mask,ones=q;unsigned z=0,d=0;
  for(;zeros;zeros&=zeros>>1)++z;
  for(;ones;ones&=ones>>1)++d;
  unsigned tail=std::countr_one(q);
  return mass>=8*(U(1)<<(z+1))&&mass>=40*(U(1)<<d)&&gap+4>=20*(U(1)<<tail);
}
template<unsigned K,unsigned C> static inline bool block(State &s,U q,U lim,U &len,const Tables<K>&tab){
  constexpr unsigned N=K*C;constexpr U mask=(U(1)<<K)-1;
  if(!q||q>=(U(1)<<N)||s.a>s.m)return false;
  U l=std::popcount(q);if(l>lim)return false;
  U o=s.m&1,pi=3*o;I d=0;W c=0;
  // Compose coefficients without forming a giant counter at intermediate
  // chunk boundaries. Each chunk is exact even when it ends in idle bits.
  for(unsigned i=0;i<C;++i){U part=(q>>(K*(C-i-1)))&mask;const auto &v=tab.t[part];c=c*(U(1)<<K)-W(part)*d+v.c[pi];d+=v.d;pi=v.p[pi];}
  unsigned tz=std::countr_zero(q),R=N-tz;
  W b=(W(s.a+2+o)<<N)-W(q)*s.m+c;
  // The final tz ticks are idle, so undo them to reach the last event.
  if(b<0)return false;
  b>>=tz;U m=s.m+d-3*tz;W a=b-2-(pi&1);
  if(a<0||a>m||((m-U(a))&1))return false;
  U g=m-U(a);
  if(!(s.m>=8*(U(1)<<R)&&g+4>=20*(U(1)<<R))&&!streak_guard(q>>tz,R,s.m,g))return false;
  s={U(a),m};len=l;return true;
}
// Independent literal CLine interpreter, not the accelerated section formula.
static bool literal(State &s){U a=s.a,k=right(s),c=0;do{if(c==1){++k;c=0;}else if(c==2)return false;else if(c==3){k+=2;c=1;}else if(c==0){if(!a){a=1;c=2*k+2;k=0;}else if(a==1&&!k){a=5;c=1;}else if(a==1){a=2;c=2*k-1;k=2;}else{a-=2;c=2*k+1;k=1;}}else if(a){--a;++k;--c;}else if(k&1){a=2*k+3;k=0;}else{a=2*k+2;k=2;c-=3;}}while(c);s=fromAK(a,k);return true;}
template<unsigned K,unsigned C> static int run(int argc,char **argv){
  constexpr unsigned N=K*C;Tables<K> tab;Reciprocal<N> pred;
  for(U a=0;a<128;++a)for(U k=0;k<128;++k){auto x=fromAK(a,k),y=x;bool p=next(x),q=literal(y);assert(p==q&&(!p||x==y));}
  std::mt19937_64 rng(12);U checked=0;
  for(U j=0;j<300000;++j){U m=(U(1)<<34)+(rng()%(U(1)<<46));U a=(rng()%m);a=(a&~U(1))|(m&1);if(a>m)continue;State x{a,m},y=x;U n=0;U q=pred.quotient(x);if(j%3==0)q^=U(1)<<(rng()%N);if(!block<K,C>(x,q,100,n,tab))continue;for(U i=0;i<n;++i)assert(next(y));assert(x==y);++checked;}
  printf("N=%u chunk=%u, literal tests=16384, accepted adversarial/random blocks=%llu\n",N,K,(unsigned long long)checked);
  U i=strtoull(argv[1],0,10);State s=fromAK(strtoull(argv[2],0,10),strtoull(argv[3],0,10));U end=strtoull(argv[4],0,10),interval=argc>6?strtoull(argv[6],0,10):1000000000ULL;
  U check=std::min(end,(i/interval+1)*interval),blocks=0,singles=0;auto start=std::chrono::steady_clock::now();
  while(i<end){if(s.m>=U(1)<<60)return 2;U q=pred.quotient(s),n=0;if(block<K,C>(s,q,check-i,n,tab)){i+=n;++blocks;}else{State old=s;if(!next(s)){printf("TERMINAL return=%llu a=%llu k=%llu mass=%llu\n",(unsigned long long)i,(unsigned long long)old.a,(unsigned long long)right(old),(unsigned long long)old.m);return 0;}++i;++singles;}
    if(i==check){printf("LIVE return=%llu a=%llu k=%llu mass=%llu blocks=%llu singles=%llu elapsed=%.3f\n",(unsigned long long)i,(unsigned long long)s.a,(unsigned long long)right(s),(unsigned long long)s.m,(unsigned long long)blocks,(unsigned long long)singles,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());fflush(stdout);check=std::min(end,check+interval);}
  }return 0;
}
int main(int argc,char**argv){assert(argc>=6);int mode=atoi(argv[5]);switch(mode){case 20:return run<10,2>(argc,argv);case 24:return run<12,2>(argc,argv);case 28:return run<14,2>(argc,argv);case 30:return run<10,3>(argc,argv);case 32:return run<16,2>(argc,argv);case 36:return run<12,3>(argc,argv);default:return 1;}}
