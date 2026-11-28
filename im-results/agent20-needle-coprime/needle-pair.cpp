#include <gmpxx.h>
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
#include <omp.h>
using U=unsigned long;
using Z=mpz_class;
static Z pow2(U e){ Z z=1; mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),e); return z; }
static U bits(const Z& z){ return mpz_sizeinbase(z.get_mpz_t(),2); }
static U bitsu(U z){ return z?8*sizeof(U)-__builtin_clzl(z):0; }
static U powmod(U a,U e,U p){ U z=1; while(e){if(e&1)z=z*a%p; a=a*a%p; e>>=1;}return z; }
static U apmod(U r,U a,U p){ U A=powmod(2,a,p),P=0,n=1; for(U i=0;i<r;i++){P=(A*A%p*P+n*((A+p-3)%p))%p;n=n*9%p;}return A*P%p; }
struct Cache {
  U k=0; Z v=1;
  Z get(U n){
    if(n==k)return v;
    if(n<k&&k-n<=5000){
      U delta=k-n;
      if(delta<=20){U p=1;for(U i=0;i<delta;i++)p*=3;mpz_divexact_ui(v.get_mpz_t(),v.get_mpz_t(),p);}
      else {Z p;mpz_ui_pow_ui(p.get_mpz_t(),3,delta);mpz_divexact(v.get_mpz_t(),v.get_mpz_t(),p.get_mpz_t());}
    }else mpz_ui_pow_ui(v.get_mpz_t(),3,n);
    k=n;return v;
  }
};
// The reduction 2^m = -3 (mod 2^m+3) is exact, including negative inputs.
static void fold(Z& s,U m){ Z hi,lo; while(bits(s)>m){mpz_tdiv_q_2exp(hi.get_mpz_t(),s.get_mpz_t(),m);mpz_tdiv_r_2exp(lo.get_mpz_t(),s.get_mpz_t(),m);s=lo-3*hi;} }
static Z pow3special(U k,U m){ Z z=1;int b=0;for(U t=k;t>>=1;)++b;for(;b>=0;--b){z*=z;fold(z,m);if((k>>b)&1){z*=3;fold(z,m);}}return z; }
static Z red(U e,U m,const Z&D,Cache&cache){
  U k=e/m,s=e%m;Z z,three=3;
  if(m>=25000 && k<=8*m) z=cache.get(k);
  else if(m>=25000){
    unsigned h=0;while((k>>h)>m/2)h++;
    z=cache.get(k>>h);
    for(int j=int(h)-1;j>=0;j--){z*=z;fold(z,m);if((k>>j)&1){z*=3;fold(z,m);}}
  }
  else if(m>=8) z=pow3special(k,m);
  else mpz_powm_ui(z.get_mpz_t(),three.get_mpz_t(),k,D.get_mpz_t());
  mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),s);if(k&1)z=-z;return z;
}
static bool divisible(Z s,U m,const Z&D){ if(m<8)return mpz_divisible_p(s.get_mpz_t(),D.get_mpz_t());fold(s,m);return s==0; }
// p <= 10^7, all products fit uint64_t.
static U inverse(U a,U m){int64_t x=1,y=0,b=m,c=a;while(c){int64_t q=b/c,t=b%c;b=c;c=t;t=y-q*x;y=x;x=t;}assert(b==1);return (y%int64_t(m)+m)%m;}
struct PrimeLog {
  U p,q,g,k,step;
  std::vector<std::pair<U,U>> baby;
  PrimeLog(U p_,U q_,U g_):p(p_),q(q_),g(g_){
    if(q<=32)return;
    k=U(std::sqrt(double(q)))+1;
    U x=1;baby.reserve(k);
    for(U j=0;j<k;j++){baby.emplace_back(x,j);x=x*g%p;}
    std::sort(baby.begin(),baby.end());step=powmod(g,q-k%q,p);
  }
  U get(U x)const{
    if(q<=32){U t=1;for(U j=0;j<q;j++){if(t==x)return j;t=t*g%p;}assert(false);}
    for(U i=0;i*k<q;i++){
      auto it=std::lower_bound(baby.begin(),baby.end(),std::pair<U,U>(x,0));
      if(it!=baby.end()&&it->first==x){U r=i*k+it->second;if(r<q)return r;}
      x=x*step%p;
    }
    assert(false);return q;
  }
};
// Returns order and canonical logarithm of -3, or order and order if not in subgroup.
static std::pair<U,U> order_log(U p,const std::vector<uint32_t>&spf){
  U ord=p-1,n=ord;std::vector<std::pair<U,U>> fac;
  while(n>1){U q=spf[n],e=0;do{n/=q;e++;}while(n%q==0);while(e&&powmod(2,ord/q,p)==1){ord/=q;e--;}if(e)fac.emplace_back(q,e);}
  if(powmod(p-3,ord,p)!=1)return {ord,ord};
  U sol=0,mod=1;
  for(auto [q,e]:fac){
    U x=0,Q=1;PrimeLog log(p,q,powmod(2,ord/q,p));
    for(U i=0;i<e;i++){
      U y=(p-3)*powmod(2,(ord-x)%ord,p)%p;
      U digit=log.get(powmod(y,ord/(Q*q),p));
      x+=digit*Q;Q*=q;
    }
    U diff=(x+Q-sol%Q)%Q;
    U k=diff*inverse(mod%Q,Q)%Q;
    sol+=mod*k;mod*=Q;
  }
  assert(mod==ord&&sol<ord&&powmod(2,sol,p)==p-3);return {ord,sol};
}
// Three candidate shifts are sufficient for the per-term size filter: on
// every interval between exponent wraps the actual width constraints increase.
static bool rotation_reject(U m,U a,U E,U N,bool four){
  const long C=four?15-70*long(m):5-2*long(m);
  const U c=four?32:1, HC=bitsu(3*U(std::abs(C))), HD=bitsu(U(std::abs(C-long(c*N))));
  if(a/m<HC)return false;
  auto good=[&](U h,U e,U H){U q=(e+h)/m,s=(e+h)%m;return s+H+8*((q+4)/5)+2<m;};
  for(U h:{U(0),(m-E%m)%m,(m-a%m)%m})
    if(good(h,E,bitsu(c))&&good(h,a,HD)&&good(h,0,HC))return true;
  return false;
}
int main(int argc,char**argv){
  assert(argc==5||argc==6);bool childOnly=argc==6;assert(!childOnly||std::string(argv[5])=="child-only");U r=std::stoul(argv[1]),lo=std::stoul(argv[2]),hi=std::stoul(argv[3]),limit=std::stoul(argv[4]);
  assert(r>=8&&r<=14&&r%3==1&&limit>=7&&limit<=10000000);
  U N=1;for(U i=0;i<r;i++)N*=9;U a=(N+5)/2,M=2*r*a,E=M+a;
  Z L=(Z(13)*(r+1)*a-1)/4,sq;mpz_sqrt(sq.get_mpz_t(),L.get_mpz_t());U cut=sq.get_ui();
  assert(lo>=1&&lo<=hi&&hi<=cut);
  auto begin=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();};
  std::vector<uint32_t> spf(limit+1);std::vector<U> primes;
  for(U p=2;p<=limit;p++)if(!spf[p]){spf[p]=p;primes.push_back(p);if(p<=limit/p)for(U k=p*p;k<=limit;k+=p)if(!spf[k])spf[k]=p;}
  std::vector<uint8_t> flags(hi-lo+1,childOnly?1:0); // bit 0=root rejected/skipped, bit 1=four rejected
  U sieveR=childOnly?hi-lo+1:0,sieveF=0,ladic=0,rotR=0,rotF=0;
  for(U p:primes){if(p<5)continue;auto [period,res]=order_log(p,spf);
    if(p<10000){U t=1,per=0,ref=0;do{++per;t=t*2%p;if(t==p-3)ref=per;}while(t!=1);assert(period==per&&((ref==0&&res==period)||(ref&&res==ref%per)));}
    if(res==period)continue;
    U ap=apmod(r,a,p),start=res?res:period;
    if(start<lo)start+=((lo-start+period-1)/period)*period;
    U pp=p*p,app=0;if(p==5||p==7)app=apmod(r,a,pp);
    for(U m=start;m<=hi;m+=period){U v=m%p;auto& f=flags[m-lo];
      if(!(f&1)&&(ap+(5+p-2*v%p)%p)%p){f|=1;sieveR++;}
      if(!(f&2)&&(32*ap%p+15+p-70*v%p)%p){f|=2;sieveF++;}
      if(!(f&2)&&(p==5||p==7)&&(32*app%pp+15+pp-70*(m%pp)%pp)%pp){f|=2;ladic++;}
    }
  }
  for(U m=lo;m<=hi;m++){auto&f=flags[m-lo];if(!(f&1)&&rotation_reject(m,a,E,N,false)){f|=1;rotR++;}if(!(f&2)&&rotation_reject(m,a,E,N,true)){f|=2;rotF++;}}
  U both=0;for(auto f:flags)both+=(f==3);
  std::cerr<<"SIEVE root="<<sieveR<<" four="<<sieveF<<" L-adic="<<ladic<<" rotationR="<<rotR<<" rotationF="<<rotF<<" union_survivors="<<hi-lo+1-both<<" seconds="<<elapsed()<<std::endl;
  U sparseR=0,sparseF=0,fullR=0,fullF=0;std::vector<U> parentsR,parentsF;
  auto exact=[&](U m,const Z&C,const Z&D,bool four){Z LD=four?35*D:D,A,two=2,P=0,n=1;mpz_powm_ui(A.get_mpz_t(),two.get_mpz_t(),a,LD.get_mpz_t());for(U i=0;i<r;i++){P=(A*A*P+n*(A-3))%LD;n*=9;}Z F=(four?32:1)*A*P+C;if(!mpz_divisible_p(F.get_mpz_t(),LD.get_mpz_t()))return false;assert(bits(3*LD+abs(C))<M-1);return true;};
  #pragma omp parallel reduction(+:sparseR,sparseF,fullR,fullF)
  {
    Cache ce,ca;
    #pragma omp for schedule(static)
    for(U m=lo;m<=hi;m++){
      auto f=flags[m-lo];if(f==3)continue;
      Z D=pow2(m)+3,C=5-2*Z(m),RE=red(E,m,D,ce),RA=red(a,m,D,ca);
      Z S=RE+(C-N)*RA+3*C;
      if(!(f&1)){
        bool hit=divisible(S,m,D);if(m%997==0||hit)assert(hit==bool(mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t())));
        if(!hit)++sparseR;else{++fullR;if(exact(m,C,D,false)){
          #pragma omp critical
          {parentsR.push_back(m-1);std::cerr<<"ROOT_PARENT="<<m-1<<std::endl;}
        }}
      }
      if(!(f&2)){
        Z C4=35*C-160,S4=32*S+(3*C-160)*(RA+3);
        bool hit=divisible(S4,m,D);if(m%997==0||hit)assert(hit==bool(mpz_divisible_p(S4.get_mpz_t(),D.get_mpz_t())));
        if(!hit)++sparseF;else{++fullF;if(exact(m,C4,D,true)){
          #pragma omp critical
          {parentsF.push_back(m-1);std::cerr<<"FOUR_PARENT="<<m-1<<std::endl;}
        }}
      }
    }
  }
  assert(sieveR+rotR+sparseR+fullR==hi-lo+1);assert(sieveF+ladic+rotF+sparseF+fullF==hi-lo+1);
  std::sort(parentsR.begin(),parentsR.end());std::sort(parentsF.begin(),parentsF.end());
  std::cout<<"r="<<r<<" range="<<lo<<".."<<hi<<" cut="<<cut<<(childOnly?" root skipped: sieve=":" root: sieve=")<<sieveR<<" rotation="<<rotR<<" sparse="<<sparseR<<" exact="<<fullR<<" parents=";for(U v:parentsR)std::cout<<v<<",";std::cout<<" four: sieve="<<sieveF<<" Ladic="<<ladic<<" rotation="<<rotF<<" sparse="<<sparseF<<" exact="<<fullF<<" parents=";for(U v:parentsF)std::cout<<v<<",";std::cout<<" seconds="<<elapsed()<<std::endl;
}
