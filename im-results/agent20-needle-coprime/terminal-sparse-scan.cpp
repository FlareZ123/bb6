#include "needle-modular.hpp"
#include "needle-sparse-exact.hpp"
#include <chrono>
#include <iostream>
#include <sstream>
#include <string>
#include <omp.h>
using U=unsigned long;using Z=mpz_class;using W=__uint128_t;
namespace ns=needle_sparse;namespace nm=needle_modular;
struct Node {U n;Z L=1,d=0;};
static Z C(const Node&t,U m){return t.d+t.L*(5-2*Z(m));}
static bool positive(const Node&t,U m){return ns::sign({{t.n,1},{0,C(t,m)-9*t.L},{m,-3*t.L}})>=0;}
static bool exact(const Node&t,U m,bool sparse){
  if(!positive(t,m))return false;
  if(sparse)return ns::divisible({{t.n,1},{0,C(t,m)}},m,t.L);
  Z LD=t.L*(ns::pow2(m)+3),F=ns::powm(2,t.n,LD)+C(t,m);return mpz_divisible_p(F.get_mpz_t(),LD.get_mpz_t());
}
static Node step(const Node&t,U m){Z p=ns::pow2(m);return {ns::checked_add(t.n,m),t.L*(p+3),p*C(t,m)};}
static bool is_blank(const Node&t){return ns::sign({{t.n,1},{0,t.d-6*t.L}})==0;}
static W log3ceil(U k){return (8*W(k)+4)/5;}
static U ordinary(const Node&t,U K,U H){
  U lo=0,hi=K;
  while(lo<hi){U m=lo+(hi-lo)/2+1,q=t.n/m;
    if(W(m)<W(H)+2*W(q)+2&&W(m)<W(H)+(8*(W(q)+1)+4)/5+1)lo=m;else hi=m-1;
  }
  return lo;
}
static U exception(const Node&t,U H,U K,U cut){
  if(cut>=K)return 0;U min_m=std::max<U>(4,cut+1),hi=std::min(H-1,t.n/min_m)/2,lo=1;if(hi<lo)return 0;
  Z rhs=2*t.L*t.n,base=t.d+5*t.L;
  auto lhs=[&](U half){Z p;mpz_ui_pow_ui(p.get_mpz_t(),3,2*half);Z z=(base+p)*(2*half);return z;};
  while(lo<hi){U mid=lo+(hi-lo)/2;if(lhs(mid)>=rhs)hi=mid;else lo=mid+1;}
  U q=2*lo;if(lhs(lo)!=rhs||t.n%q)return 0;U m=t.n/q;return m>=min_m&&m<=K?m:0;
}
static bool rotation(U n,U m,const Z& c){
  U q=n/m,s=n%m,H=ns::bits(c);assert(c!=0);
  if(log3ceil(q)+s<m&&H<m){
    if(s)return true; // odd residual, and each term fits in m-1 bits
    if((q%2==0&&c>0)||(q%2==1&&c<0))return true;
    Z unit,three=3;U v=mpz_remove(unit.get_mpz_t(),c.get_mpz_t(),three.get_mpz_t());
    if(v!=q||abs(unit)!=1)return true;
  }
  if(s&&log3ceil(q+1)<m&&W(H)+m-s<m)return true;
  return false;
}
static U modui(const Z& z,U p){return mpz_fdiv_ui(z.get_mpz_t(),p);}
static std::pair<U,U> sieve(const Node&t,U lo,U hi,U limit,std::vector<uint8_t>&flags){
  std::vector<uint32_t> spf(limit+1);std::vector<U> primes;U removed=0,lifted=0;
  for(U p=2;p<=limit;p++)if(!spf[p]){spf[p]=p;primes.push_back(p);if(p<=limit/p)for(U k=p*p;k<=limit;k+=p)if(!spf[k])spf[k]=p;}
  for(U p:primes){if(p<5)continue;auto [period,res]=nm::order_log(p,spf);if(res==period)continue;
    U start=res?res:period;if(start<lo)start+=((lo-start+period-1)/period)*period;
    U pow=nm::powmod(2,t.n,p),l=modui(t.L,p),d=modui(t.d,p),pp=p*p,pow2=0,l2=0,d2=0;
    if(!l){pow2=ns::powm(2,t.n,Z(pp)).get_ui();l2=modui(t.L,pp);d2=modui(t.d,pp);}
    for(U m=start;m<=hi;m+=period){auto& f=flags[m-lo];if(f)continue;
      U v=(5+p-2*(m%p)%p)%p;if((pow+d+l*v)%p){f=1;++removed;continue;}
      if(!l){U v2=(5+pp-2*(m%pp)%pp)%pp;if((W(pow2)+d2+W(l2)*v2)%pp){f=1;++lifted;}}
    }
  }
  return {removed,lifted};
}
static void scan(const Node&t,U K,U cut,U ex,U lo,U hi,U limit,bool extras){
  auto st=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count();};
  U prime=0,lifted=0,rot=0,sparse=0,full=0;std::vector<U> parents;
  if(lo<=hi){assert(lo>=1&&hi<=cut&&hi-lo+1<=100000000);std::vector<uint8_t> flags(hi-lo+1);auto counts=sieve(t,lo,hi,limit,flags);prime=counts.first;lifted=counts.second;
    #pragma omp parallel reduction(+:rot,sparse,full)
    {
      nm::Cache cache;
      #pragma omp for schedule(static)
      for(U m=lo;m<=hi;m++){
        if(flags[m-lo])continue;Z c=C(t,m);
        if(rotation(t.n,m,c)){++rot;continue;}
        Z D=ns::pow2(m)+3,S=nm::red(t.n,m,D,cache)+c;bool hit=nm::divisible(S,m,D);
        if(m%997==0||hit)assert(hit==bool(mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t())));
        if(!hit){++sparse;continue;}++full;
        if(t.L==1?positive(t,m):exact(t,m,false)){
          #pragma omp critical
          {parents.push_back(m);std::cerr<<"PARENT m="<<m<<" w="<<m-1<<std::endl;}
        }
      }
    }
    assert(prime+lifted+rot+sparse+full==hi-lo+1);
  }
  bool exParent=false;if(extras&&ex){exParent=exact(t,ex,true);if(exParent){parents.push_back(ex);std::cerr<<"EXCEPTION_PARENT m="<<ex<<" w="<<ex-1<<std::endl;}}
  std::sort(parents.begin(),parents.end());std::cout<<"K="<<K<<" n="<<t.n<<" Lbits="<<ns::bits(t.L)<<" dbits="<<ns::bits(t.d)<<" blank="<<is_blank(t)<<" ordinary="<<cut<<" exception="<<ex<<" exceptionChecked="<<extras<<" exceptionParent="<<exParent<<" range="<<lo<<".."<<hi<<" prime="<<prime<<" lifted="<<lifted<<" rotation="<<rot<<" sparse="<<sparse<<" exact="<<full<<" complete="<<(lo==1&&hi==cut&&extras)<<" parents_m=";for(U m:parents)std::cout<<m<<",";std::cout<<" seconds="<<elapsed()<<std::endl;
}
int main(int argc,char**argv){
  if(argc!=7){std::cerr<<"usage: terminal-sparse-scan K m1,m2,...|- range|extras|all lo hi prime-limit\n";return 2;}
  U K=std::stoul(argv[1]),lo=std::stoul(argv[4]),hi=std::stoul(argv[5]),limit=std::stoul(argv[6]);assert(K>=2&&K<~0UL&&limit>=7&&limit<=10000000);Node t{K+1};
  if(std::string(argv[2])!="-"){std::istringstream s(argv[2]);std::string v;while(std::getline(s,v,',')){U m=std::stoul(v);if(m>100000000){std::cerr<<"history materialization limit, use sparse cancellation feeder representation for large initial exception\n";return 3;}if(m==0||m>K||!exact(t,m,false)){std::cerr<<"illegal inverse path at m="<<m<<"\n";return 4;}t=step(t,m);}}
  U H=ns::bits(abs(t.d)+t.L*(2*Z(K)+5)),cut=ordinary(t,K,H),ex=exception(t,H,K,cut);std::string mode=argv[3];
  if(mode=="all")scan(t,K,cut,ex,1,cut,limit,true);else if(mode=="range")scan(t,K,cut,ex,lo,hi,limit,false);else if(mode=="extras")scan(t,K,cut,ex,1,0,limit,true);else return 2;
}
