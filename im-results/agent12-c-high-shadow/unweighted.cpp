#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <bit>
#include <chrono>
#include <vector>
#include <algorithm>
using U=uint64_t; using I=int64_t;
struct S{U a,k;};
static inline bool bounce(U k,U c,S &s){
 U o=1-(k&1),b=3+o,B=k+b,N=c+2*B;
 int d=int(std::bit_width(N))-int(std::bit_width(B))-2;unsigned n=d>0?unsigned(d):0;
 while((B<<(n+2))<N+3*n)++n;
 U K=(B<<n)-b,C=c+2*k+3*n-2*K;
 if(!o){s={2*K+6-C,C};return true;}if(C==4){s={2*K+2,3};return true;}if(C==5)return false;s={2*K+8-C,C-1};return true;
}
static inline bool next(S &s){U a=s.a,k=s.k;if(a>=2&&k&&2*k<=a){s={a-2*k,2*k+2};return true;}if(a>=2&&k)return bounce(a-1,2*k-a+3,s);if(a==0){if(k==0)return false;if(k==1){s={0,4};return true;}return bounce(1,2*k+1,s);}if(a==1){switch(k){case 0:s={5,1};return true;case 1:s={2,3};return true;case 2:s={2,5};return true;case 3:s={0,7};return true;default:return bounce(4,2*k-3,s);}}s={a-2,2};return true;}
struct Coeff{int32_t c[2]{};uint32_t p=1,q=0,w=0,l=0;};
static std::vector<Coeff> table(unsigned bits){std::vector<Coeff> out(U(1)<<bits);for(U q=1;q<out.size();++q){auto &v=out[q];U g=0;for(int j=int(bits)-1;j>=0;--j){++g;if(!(q&(U(1)<<j)))continue;I p=I(1)<<g,w=3*g+1;for(U o=0;o<2;++o){I parity=(o+v.w)&1;v.c[o]=p*(v.c[o]+2+parity)-v.w-w-2*parity;}v.p*=p;v.q=p*v.q+1;v.w+=w;++v.l;g=0;}assert(v.q==q>>std::countr_zero(q));}return out;}
int main(int argc,char **argv){U i=strtoull(argv[1],0,10);S s{strtoull(argv[2],0,10),strtoull(argv[3],0,10)};U end=strtoull(argv[4],0,10);unsigned bits=atoi(argv[5]);assert(bits>=1&&bits<=20);auto tab=table(bits);U check=(i/1000000000+1)*1000000000;auto start=std::chrono::steady_clock::now();while(i<end){U M=s.a+2*s.k;if(M>=U(1)<<(62-bits))return 2;U q=(s.a<<bits)/M;const auto &v=tab[q];U m=M+v.w;I a=I(U(v.p)*s.a)-I(U(v.q)*M)+v.c[M&1];if(q&&v.l<=std::min(end,check)-i&&M>=8*U(v.p)&&a>=0&&I(m)-a+4>=20*I(v.p)){assert(((m-U(a))&1)==0);s={U(a),(m-U(a))/2};i+=v.l;}else{if(!next(s)){printf("TERMINAL return=%llu a=%llu k=%llu\n",(unsigned long long)i,(unsigned long long)s.a,(unsigned long long)s.k);return 0;}++i;}if(i==check||i==end){printf("LIVE return=%llu a=%llu k=%llu mass=%llu elapsed=%.3f\n",(unsigned long long)i,(unsigned long long)s.a,(unsigned long long)s.k,(unsigned long long)(s.a+2*s.k),std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());fflush(stdout);if(i==check)check+=1000000000;}}}
