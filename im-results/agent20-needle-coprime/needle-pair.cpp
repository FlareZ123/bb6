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
#include "needle-modular.hpp"
using namespace needle_modular;
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
