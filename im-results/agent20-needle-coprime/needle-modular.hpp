#pragma once
#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <vector>

namespace needle_modular {
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
} // namespace needle_modular
