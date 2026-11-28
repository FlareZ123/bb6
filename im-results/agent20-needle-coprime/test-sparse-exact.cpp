#include "needle-sparse-exact.hpp"
#include <iostream>
#include <random>
using namespace needle_sparse;
static Z dense(const Terms& t){Z z=0;for(auto&s:t)z+=s.c*pow2(s.e);return z;}
int main(){
  std::mt19937_64 rng(20261128);
  for(int i=0;i<20000;i++){
    U m=1+rng()%200,L=1+rng()%500;Terms t;
    for(U j=0,n=1+rng()%15;j<n;j++)t.push_back({rng()%1000,Z(long(rng()%20001)-10000)});
    Z S=dense(t),D=Z(L)*(pow2(m)+3);
    assert(sign(t)==mpz_sgn(S.get_mpz_t()));assert(divisible(t,m,Z(L))==mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t()));
    // Inject a nontrivial exact multiple, including negative multiples.
    Z q=long(rng()%20001)-10000;Terms v{{m,Z(L)*q},{0,3*Z(L)*q}};
    U e=rng()%1000;Z c=long(rng()%10001)-5000;v.push_back({e,c});v.push_back({e,-c});assert(divisible(v,m,Z(L)));
  }
  const U M=1000000000000UL;Terms t{{M+4,-17},{M,272},{0,-1}};
  assert(sign(t)==-1);t.back().c=1;assert(sign(t)==1);
  for(U L:{1UL,5UL,35UL,567UL}){
    Terms v{{M,Z(L)*17},{0,Z(L)*51}};assert(divisible(v,M,Z(L)));v.back().c+=1;assert(!divisible(v,M,Z(L)));
    // 2^(2M)-9=(2^M+3)(2^M-3); multiply by L.
    Terms w{{2*M,Z(L)},{0,-9*Z(L)}};assert(divisible(w,M,Z(L)));w.back().c+=1;assert(!divisible(w,M,Z(L)));
  }
  for(U r=1;r<=4;r++){
    U N=1;for(U j=0;j<r;j++)N*=9;U a=(N+5)/2;
    Z AP=dense(numerator(r,a,0,0));
    for(U m=1;m<=500;m++)for(U x:{0UL,5UL}){
      Z L=x?35:1,d=x?-160:0,C=d+L*(5-2*Z(m)),D=L*(pow2(m)+3),num=AP*pow2(x)+C;
      bool ref=num>=3*D&&mpz_divisible_p(num.get_mpz_t(),D.get_mpz_t());assert(legal_parent(r,a,x,d,L,m)==ref);
    }
  }
  std::cout<<"PASS sparse sign, quotient, full L*D divisibility, and positivity; 20,000 random cases, injected multiples, 4,000 feeder cases, trillion-bit gaps\n";
}
