#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <bit>
#include <chrono>
#include <vector>
#include <algorithm>
#include <string>
#include <random>
using U=uint64_t; using I=int64_t; using W=__int128_t;
struct State{U a,k; bool operator==(const State&)const=default;};
// The guard below limits all input masses to 2^41. A section has O(M^2)
// primitive moves and at most M/2 successful sections precede the cap,
// so 128-bit accumulation is ample; still detect any accidental overflow.
static void addClock(W &total,W increment){W out;if(increment<0||__builtin_add_overflow(total,increment,&out)){std::fputs("clock overflow\n",stderr);std::abort();}total=out;}
static std::string dec(W x){assert(x>=0);std::string s;do{s+=char('0'+x%10);x/=10;}while(x);std::reverse(s.begin(),s.end());return s;}
static inline W drain(U h,U k){return W(h)*(2*W(h)+4*W(k)+7);}
// Count ordinary primitive transitions only; add one for the final halt query.
static inline bool bounce(U k,U c,State &s,W &raw,U &calls){
  assert(c>=4);
  U o=1-(k&1),b=3+o,B=k+b,N=c+2*B;
  int delta=int(std::bit_width(N))-int(std::bit_width(B))-2;
  unsigned n=delta>0?unsigned(delta):0;
  while((W(B)<<(n+2))<N+3*n)++n;
  U T=B<<n,K=T-b,C=c+2*k+3*n-2*K;
  W sum3=8*(W(T)*T-W(B)*B)-3*W(5+8*o)*(T-B)-3*W(5+12*o)*n;
  assert(sum3>=0&&sum3%3==0);raw+=sum3/3;
  if(!o){calls+=c+n;raw+=2*W(C)*C-5*W(C)+5*W(T)+9;s={2*K+6-C,C};return true;}
  if(C==4){calls+=c-2*n-2;raw+=5*W(K)+23;s={2*K+2,3};return true;}
  if(C==5){calls+=c-2*n-3;raw+=5*W(K)+24;return false;}
  calls+=c-2*n-3;raw+=2*W(C)*C-9*W(C)+5*W(T)-3;s={2*K+8-C,C-1};return true;
}
static inline bool next(State &s,W &raw,U &calls){
  U a=s.a,k=s.k;
  if(a>=2&&k&&2*k<=a){raw+=8*W(k)*k+8*W(k)+4;calls+=2*k+1;s={a-2*k,2*k+2};return true;}
  if(a>=2&&k){raw+=2*W(a)*a+3*W(a)+2*W(k)-10;calls+=a-1;return bounce(a-1,2*k-a+3,s,raw,calls);}
  if(a==0){if(k==0){raw+=6;calls+=2;return false;}if(k==1){raw+=28;calls+=4;s={0,4};return true;}raw+=2*W(k)+12;calls+=2;return bounce(1,2*k+1,s,raw,calls);}
  if(a==1){switch(k){case 0:raw+=13;calls+=2;s={5,1};return true;case 1:raw+=20;calls+=2;s={2,3};return true;case 2:raw+=34;calls+=3;s={2,5};return true;case 3:raw+=74;calls+=5;s={0,7};return true;default:raw+=2*W(k)+54;calls+=3;return bounce(4,2*k-3,s,raw,calls);}}
  raw+=6;calls+=2;s={a-2,2};return true;
}
// Independent literal CLine interpreter for small-state tests.
static bool ref(State &s,W &raw,U &calls){
  U a=s.a,k=s.k,c=0;
  do {++calls;
    if(c==1){raw+=2;++k;c=0;}
    else if(c==2){raw+=3;return false;}
    else if(c==3){raw+=12;k+=2;c=1;}
    else if(c==0){if(!a){raw+=2*k+3;a=1;c=2*k+2;k=0;}else if(a==1&&!k){raw+=11;a=5;c=1;}else if(a==1){raw+=2*k+16;a=2;c=2*k-1;k=2;}else{raw+=2*k+4;a-=2;c=2*k+1;k=1;}}
    else if(a){raw+=4*k+9;--a;++k;--c;}
    else if(k&1){raw+=5*k+13;a=2*k+3;k=0;}
    else{raw+=5*k+21;a=2*k+2;k=2;c-=3;}
  }while(c);
  s={a,k};return true;
}
struct Lin{I a,m,c;};
struct Quad{I aa=0,am=0,mm=0,a=0,m=0,c=0;
  void mul(I t,Lin p,Lin q){aa+=t*p.a*q.a;am+=t*(p.a*q.m+p.m*q.a);mm+=t*p.m*q.m;a+=t*(p.a*q.c+p.c*q.a);m+=t*(p.m*q.c+p.c*q.m);c+=t*p.c*q.c;}
  void lin(I t,Lin p){a+=t*p.a;m+=t*p.m;c+=t*p.c;}
  W eval(U A,U M)const{return W(aa)*A*A+W(am)*A*M+W(mm)*M*M+W(a)*A+W(m)*M+c;}
};
struct Coeff{I c[2]{};U p=1,q=0,w=0,l=0;Quad raw[2];Lin calls[2]{};};
static std::vector<Coeff> table(unsigned bits){
  std::vector<Coeff> out(U(1)<<bits);
  for(U q=1;q<out.size();++q){
    Coeff &v=out[q];U gap=0;
    for(int j=int(bits)-1;j>=0;--j){
      ++gap;if(!(q&(U(1)<<j)))continue;
      I r=gap,p=I(1)<<gap,w=3*r+1;
      for(U o=0;o<2;++o){
        I parity=(o+v.w)&1;Lin A{I(v.p),-I(v.q),v.c[o]},M{0,1,I(v.w)};
        Lin X{p*A.a,p*A.m-1,p*A.c-M.c+p*(2+parity)-w-2*parity};
        auto &z=v.raw[o];z.mul(-4,A,A);z.mul(4,M,M);z.mul(-4,M,X);z.mul(4,X,X);
        z.lin(16*parity-22,A);z.lin(24*r-8*parity-1,M);z.lin(11-8*parity-12*r,X);
        z.c+=-96*parity*r+96*parity+36*r*r-51*r+39;
        auto &t=v.calls[o];t.a-=A.a;t.m+=1-A.m;t.c+=M.c-A.c+r+parity*(3-3*r);
        v.c[o]=X.c;
      }
      v.p*=p;v.q=p*v.q+1;v.w+=w;++v.l;gap=0;
    }
    assert(v.q==q>>std::countr_zero(q));
  }
  return out;
}
static bool block(State &s,U lim,const std::vector<Coeff>&tab,unsigned bits,U &len,W &raw,U &calls){
  U M=s.a+2*s.k;if(!M)return false;
  U q=(s.a<<bits)/M;if(!q||q>=tab.size())return false;
  const auto &v=tab[q];if(v.l>lim||M<8*v.p)return false;
  U o=M&1,m=M+v.w;I a=I(v.p*s.a)-I(v.q*M)+v.c[o];
  if(a<0||I(m)-a+4<20*I(v.p))return false;
  W w=v.raw[o].eval(s.a,M);assert(w>=0&&w%6==0);raw+=w/6;
  Lin t=v.calls[o];I cc=t.a*I(s.a)+t.m*I(M)+t.c;assert(cc>=0);calls+=U(cc);
  assert(((m-U(a))&1)==0);s={U(a),(m-U(a))/2};len=v.l;return true;
}
static void test(const std::vector<Coeff>&tab,unsigned bits){
  for(U a=0;a<128;++a)for(U k=0;k<128;++k){State x{a,k},y=x;W w=0,v=0;U c=0,d=0;bool p=next(x,w,c),q=ref(y,v,d);if(p!=q||(p&&x!=y)||w!=v||c!=d){printf("fail a=%llu k=%llu cost=%s/%s calls=%llu/%llu\n",(unsigned long long)a,(unsigned long long)k,dec(w).c_str(),dec(v).c_str(),(unsigned long long)c,(unsigned long long)d);abort();}}
  std::mt19937_64 rng(12);U accepted=0;
  for(U j=0;j<100000;++j){State x{rng()%1000000000000ULL,rng()%1000000000000ULL},y=x;W w=0,v=0;U c=0,d=0,n=0;if(!block(x,100,tab,bits,n,w,c))continue;++accepted;for(U i=0;i<n;++i)assert(next(y,v,d));assert(x==y&&w==v&&c==d);}
  printf("tests passed: 16384 literal states, %llu accepted random blocks\n",(unsigned long long)accepted);
}
int main(int argc,char**argv){
  U i=argc>1?strtoull(argv[1],nullptr,10):0;State s{argc>2?strtoull(argv[2],nullptr,10):5,argc>3?strtoull(argv[3],nullptr,10):1};U end=argc>4?strtoull(argv[4],nullptr,10):1000000000;unsigned bits=argc>5?strtoul(argv[5],nullptr,10):12;assert(bits>=1&&bits<=16);auto tab=table(bits);test(tab,bits);
  W raw=i==0?14:0,callTotal=i==0?1:0;U blocks=0,singles=0,checkpoint=(i/1000000000+1)*1000000000;auto start=std::chrono::steady_clock::now();
  if(s.a>=(U(1)<<41)||s.k>=(U(1)<<40)){puts("input cap");return 2;}
  const bool blank=i==0&&s==State{5,1};raw=blank?14:0;callTotal=blank?1:0;
  printf("clock_origin=%s return=%llu\n",blank?"blank":"relative",(unsigned long long)i);
  while(i<end){U M=s.a+2*s.k;if(M>=(U(1)<<41)){puts("mass cap");return 2;}U n=0,c=0;W local=0;bool ok=block(s,std::min(end,checkpoint)-i,tab,bits,n,local,c);if(ok){i+=n;++blocks;}else{if(!next(s,local,c)){addClock(raw,local);addClock(callTotal,c);printf("TERMINAL return=%llu a=%llu k=%llu ordinary=%s terminal_score_or_delta=%s calls=%s\n",(unsigned long long)i,(unsigned long long)s.a,(unsigned long long)s.k,dec(raw).c_str(),dec(raw+1).c_str(),dec(callTotal).c_str());return 0;}++i;++singles;}addClock(raw,local);addClock(callTotal,c);
    if(i==checkpoint||i==end){printf("LIVE return=%llu a=%llu k=%llu mass=%llu ordinary=%s calls=%s blocks=%llu singles=%llu elapsed=%.3f\n",(unsigned long long)i,(unsigned long long)s.a,(unsigned long long)s.k,(unsigned long long)(s.a+2*s.k),dec(raw).c_str(),dec(callTotal).c_str(),(unsigned long long)blocks,(unsigned long long)singles,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());fflush(stdout);if(i==checkpoint)checkpoint+=1000000000;}
  }
}
