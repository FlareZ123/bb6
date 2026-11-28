#include "needle-modular.hpp"
#include "needle-sparse-exact.hpp"
#include <chrono>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <omp.h>

using U=unsigned long;
using Z=mpz_class;
namespace ns=needle_sparse;
namespace nm=needle_modular;
struct Params {U r,N,a,M,E;};
struct Node {U x=0;Z d=0,L=1;};
struct Candidates {U ordinary=0;std::set<U> extra;U ternary=0;};

static Z correction(const Node&t,U m){return t.d+t.L*(5-2*Z(m));}
static U modui(const Z& z,U p){return mpz_fdiv_ui(z.get_mpz_t(),p);}
static Z ap_big(const Params&p,const Z& mod){Z A=ns::powm(2,p.a,mod),P=0,n=1,AA=(A*A)%mod;for(U i=0;i<p.r;i++){P=(AA*P+n*(A-3))%mod;n*=9;}return A*P%mod;}
static bool positive(const Params&p,const Node&t,U m){auto v=ns::numerator(p.r,p.a,t.x,correction(t,m)-9*t.L);v.push_back({m,-3*t.L});return ns::sign(std::move(v))>=0;}
static bool dense_parent(const Params&p,const Node&t,U m){Z LD=t.L*(ns::pow2(m)+3),F=ns::powm(2,t.x,LD)*ap_big(p,LD)+correction(t,m);return mpz_divisible_p(F.get_mpz_t(),LD.get_mpz_t())&&positive(p,t,m);}
static bool parent(const Params&p,const Node&t,U m){
  if(m==0||m>p.M)return false;
  // Exact sparse method for huge m. For small m, direct modular powers avoid
  // materializing enormous powers of 3 from the exponent quotients.
  if(m>20000000 && ns::checked_add(p.M,t.x)/m<=m/2)return ns::legal_parent(p.r,p.a,t.x,t.d,t.L,m);
  return dense_parent(p,t,m);
}
static Node step(const Node&t,U m){Z z=ns::pow2(m);return {ns::checked_add(t.x,m),z*correction(t,m),t.L*(z+3)};}
static bool is_blank(const Params&p,const Node&t){return ns::sign(ns::numerator(p.r,p.a,t.x,t.d-6*t.L))==0;}
static void divisors(U n,U lo,U hi,std::set<U>&out){assert(n>0);for(U d=1;d<=n/d;++d)if(n%d==0){U q=n/d;if(lo<=d&&d<=hi)out.insert(d);if(lo<=q&&q<=hi)out.insert(q);}}
static U v3(Z n){assert(n!=0);Z q,three=3;return mpz_remove(q.get_mpz_t(),n.get_mpz_t(),three.get_mpz_t());}
static U v2(const Z& n){assert(n!=0);Z q=abs(n);return mpz_scan1(q.get_mpz_t(),0);}
static U sqrt_floor(const Z& n){Z s;mpz_sqrt(s.get_mpz_t(),n.get_mpz_t());assert(s.fits_ulong_p());return s.get_ui();}
static Candidates candidates(const Params&p,const Node&t){
  // Source-equation cutoffs for the two already certified special families.
  if(p.r>=8&&(t.x==0||(p.r%3==1&&t.x==5&&t.d==-160&&t.L==35)))return {sqrt_floor((Z(13)*(p.r+1)*p.a-1)/4),{},0};
  // For small roots use the exact physical exponent bound. No invented cutoff.
  if(t.x==0)return {p.M,{},0};
  U e=ns::checked_add(p.E,t.x);Z maxC=abs(t.d)+t.L*(2*Z(p.M)+5),cN=ns::pow2(t.x)*p.N;
  U H2=ns::bits(maxC+cN),H3=ns::bits(3*maxC);Z B=Z(H2)+H3+23;
  // 5 m^2 <= 5 B m + 8(e+a); larger m must be resonant AND ternary-admissible.
  U root=sqrt_floor(25*B*B+160*(Z(e)+p.a));Z q=(5*B+root)/10;assert(q.fits_ulong_p());
  Candidates out;out.ordinary=std::min(p.M,q.get_ui());
  if(out.ordinary==p.M)return out;
  divisors(e-p.a,out.ordinary+1,p.M,out.extra);divisors(e,out.ordinary+1,p.M,out.extra);divisors(p.a,out.ordinary+1,p.M,out.extra);
  for(auto i=out.extra.begin();i!=out.extra.end();){if(p.a/(*i)>v3(3*correction(t,*i))){i=out.extra.erase(i);++out.ternary;}else ++i;}
  return out;
}

// Every candidate shift at which an exponent wraps is considered. If all
// three magnitudes fit, zero is necessary. Unique binary/ternary minimum
// valuations are a contradiction, without computing the large powers.
static bool rotation_reject(U m,U a,U e,const Z& B,const Z& C3){
  U hb=ns::bits(B),hc=ns::bits(C3);assert(C3!=0);
  auto good=[&](U h,U f,U H){U z=ns::checked_add(f,h),q=z/m,s=z%m;return __uint128_t(s)+H+8*__uint128_t((q+4)/5)+2<m;};
  for(U h:{U(0),(m-e%m)%m,(m-a%m)%m}){
    if(!good(h,e,1)||!good(h,0,hc)||(B!=0&&!good(h,a,hb)))continue;
    U qe=(e+h)/m,qa=(a+h)/m,se=(e+h)%m,sa=(a+h)%m;
    auto unique_min=[](U u,U v,U w){U z=std::min({u,v,w});return (u==z)+(v==z)+(w==z)==1;};
    if(unique_min(se,B==0?~0UL:ns::checked_add(sa,v2(B)),ns::checked_add(h,v2(C3))))return true;
    if(unique_min(qe,B==0?~0UL:ns::checked_add(qa,v3(B)),v3(C3)))return true;
  }
  return false;
}

struct PrimeWitness {U p,period,res,ap;};
static std::vector<PrimeWitness> factorbase(const Params&p,U limit){
  std::vector<uint32_t> spf(limit+1);std::vector<U> primes;
  for(U z=2;z<=limit;z++)if(!spf[z]){spf[z]=z;primes.push_back(z);if(z<=limit/z)for(U k=z*z;k<=limit;k+=z)if(!spf[k])spf[k]=z;}
  std::vector<PrimeWitness> out;
  for(U z:primes){if(z<5)continue;auto [period,res]=nm::order_log(z,spf);if(res!=period)out.push_back({z,period,res?res:period,nm::apmod(p.r,p.a,z)});}
  return out;
}
static std::pair<U,U> sieve(const Params&p,const Node&t,const std::vector<PrimeWitness>&base,U lo,U hi,std::vector<uint8_t>&flags){
  U removed=0,lifted=0;
  for(auto z:base){U prime=z.p,cm=nm::powmod(2,t.x,prime),lm=modui(t.L,prime),dm=modui(t.d,prime),ap=z.ap;
    U start=z.res;if(start<lo)start+=((lo-start+z.period-1)/z.period)*z.period;
    bool lift=lm==0;U pp=prime*prime,c2=0,l2=0,d2=0,a2=0;
    if(lift){c2=ns::powm(2,t.x,Z(pp)).get_ui();l2=modui(t.L,pp);d2=modui(t.d,pp);a2=modui(ap_big(p,Z(pp)),pp);}
    for(U m=start;m<=hi;m+=z.period){auto&f=flags[m-lo];if(f)continue;
      U v=(5+prime-2*(m%prime)%prime)%prime;
      if((cm*ap+dm+lm*v)%prime){f=1;++removed;continue;}
      if(lift){U v2=(5+pp-2*(m%pp)%pp)%pp;using W=__uint128_t;if((W(c2)*a2+d2+W(l2)*v2)%pp){f=1;++lifted;}}
    }
  }
  return {removed,lifted};
}

static void scan(const Params&p,const Node&t,const Candidates&c,U lo,U hi,U limit,bool extras){
  auto start=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  std::vector<U> parents;U nPrime=0,nLift=0,nRot=0,nSparse=0,nExact=0,nExtra=0;
  if(lo<=hi){assert(lo>=1&&hi<=c.ordinary&&hi-lo+1<=100000000);auto base=factorbase(p,limit);std::vector<uint8_t> flags(hi-lo+1);
    auto [prime,lifted]=sieve(p,t,base,lo,hi,flags);nPrime=prime;nLift=lifted;Z cN=ns::pow2(t.x)*p.N;U e=ns::checked_add(p.E,t.x);
    #pragma omp parallel reduction(+:nRot,nSparse,nExact)
    {
      nm::Cache ce,ca;
      #pragma omp for schedule(static)
      for(U m=lo;m<=hi;m++){
        if(flags[m-lo])continue;
        Z C=correction(t,m),B=C-cN,C3=3*C;
        if(rotation_reject(m,p.a,e,B,C3)){++nRot;continue;}
        Z D=ns::pow2(m)+3,S=nm::red(e,m,D,ce)+B*nm::red(p.a,m,D,ca)+C3;
        bool hit=nm::divisible(S,m,D);if(m%997==0||hit)assert(hit==bool(mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t())));
        if(!hit){++nSparse;continue;}++nExact;
        if(dense_parent(p,t,m)){
          #pragma omp critical
          {parents.push_back(m);std::cerr<<"PARENT m="<<m<<" w="<<m-1<<std::endl;}
        }
      }
    }
    assert(nPrime+nLift+nRot+nSparse+nExact==hi-lo+1);
  }
  if(extras){for(U m:c.extra){++nExtra;if(ns::legal_parent(p.r,p.a,t.x,t.d,t.L,m)){parents.push_back(m);std::cerr<<"EXTRA_PARENT m="<<m<<" w="<<m-1<<std::endl;}}}
  std::sort(parents.begin(),parents.end());
  std::cout<<"r="<<p.r<<" x="<<t.x<<" Lbits="<<ns::bits(t.L)<<" dbits="<<ns::bits(t.d)<<" blank="<<is_blank(p,t)<<" ordinary="<<c.ordinary<<" extras="<<c.extra.size()<<" ternaryExcluded="<<c.ternary<<" range="<<lo<<".."<<hi<<" prime="<<nPrime<<" lifted="<<nLift<<" rotation="<<nRot<<" sparse="<<nSparse<<" exact="<<nExact<<" checkedExtras="<<nExtra<<" complete="<<(lo==1&&hi==c.ordinary&&extras)<<" parents_m=";
  for(U m:parents)std::cout<<m<<",";std::cout<<" seconds="<<elapsed()<<std::endl;
}

int main(int argc,char**argv){
  // r, exact inverse path in m-values (comma-separated or -), mode, lo, hi, prime bound.
  if(argc!=7){std::cerr<<"usage: needle-ancestry r m1,m2,...|- range|extras|all lo hi prime-limit\n";return 2;}
  U r=std::stoul(argv[1]),lo=std::stoul(argv[4]),hi=std::stoul(argv[5]),limit=std::stoul(argv[6]);assert(r>=1&&r<=14&&limit>=7&&limit<=10000000);
  U N=1;for(U j=0;j<r;j++)N*=9;U a=(N+5)/2,M=2*r*a;Params p{r,N,a,M,M+a};Node t;
  if(std::string(argv[2])!="-"){
    std::istringstream s(argv[2]);std::string v;
    while(std::getline(s,v,',')){U m=std::stoul(v);if(m>100000000){std::cerr<<"history coefficient materialization limit, unexpanded\n";return 3;}if(!parent(p,t,m)){std::cerr<<"illegal inverse path at m="<<m<<"\n";return 4;}t=step(t,m);}
  }
  Candidates c=candidates(p,t);std::string mode=argv[3];
  if(mode=="all")scan(p,t,c,1,c.ordinary,limit,true);
  else if(mode=="range")scan(p,t,c,lo,hi,limit,false);
  else if(mode=="extras")scan(p,t,c,1,0,limit,true);
  else return 2;
}
