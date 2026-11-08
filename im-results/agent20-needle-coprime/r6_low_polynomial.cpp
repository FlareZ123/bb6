// Exact r=6 cancellation-feeder parent audit for 0 <= u <= v.
// Build on Linux: g++ -O3 -std=c++17 r6_low_polynomial.cpp -lgmpxx -lgmp -o r6_low
#include <gmpxx.h>
#include <chrono>
#include <iostream>
#include <vector>

int main() {
  constexpr unsigned r=6, nine=531441, v=(nine+3)/2, a=v+1;
  constexpr unsigned K=r*(nine+5)-1, primeLimit=10000;
  mpz_class B(1); B <<= a;
  mpz_class P(0), pow9(1);
  for (unsigned i=0;i<r;++i) { P=B*B*P+pow9*(B-3); pow9*=9; }
  mpz_class lhs=(B+3)*P+pow9, rhs;
  mpz_pow_ui(rhs.get_mpz_t(),B.get_mpz_t(),2*r);
  if (lhs!=rhs || P<3 || mpz_even_p(P.get_mpz_t())) return 2;
  mpz_class q=(P-3)/2, x=B*P/2;
  mpz_class twoK(1);twoK <<=K;
  mpz_class twoV(1);twoV <<=v;
  if ((B+3)*q+3*twoV+v+3!=twoK ||
      mpz_sizeinbase(x.get_mpz_t(),2)!=K) return 3;
  mpz_class N0=B*P+3;
  std::vector<unsigned char> composite(primeLimit+1),rejected(v+1);
  for (unsigned p=2;p*p<=primeLimit;++p)
    if (!composite[p])
      for (unsigned k=p*p;k<=primeLimit;k+=p) composite[k]=1;
  unsigned useful=0;
  for (unsigned p=5;p<=primeLimit;++p) {
    if (composite[p]) continue;
    unsigned z=1,order=0,exponent=0;
    for (unsigned j=1;j<p;++j) {
      z=(2*z)%p;
      if(z==(p-3) && exponent==0) exponent=j;
      if(z==1) {order=j;break;}
    }
    if(exponent==0 || order==0) continue;
    ++useful;
    unsigned xmod=mpz_fdiv_ui(x.get_mpz_t(),p);
    for (unsigned u=(exponent-1)%order;u<=v;u+=order)
      if ((static_cast<long long>(2*xmod+3)-2*static_cast<long long>(u))%p!=0)
        rejected[u]=1;
  }
  unsigned removed=0,checked=0,hits=0;
  for (unsigned u=0;u<=v;++u) removed+=rejected[u];
  std::cout<<"r="<<r<<" K="<<K<<" v="<<v<<" useful_primes="<<useful
           <<" rejected_low="<<removed<<" low_survivors="<<v+1-removed
           <<std::endl;
  mpz_class d,b,sq,pm,h,neg3(-3),power9,test;
  auto start=std::chrono::steady_clock::now();
  for (unsigned u=0;u<=v;++u) {
    if(rejected[u]) continue;
    unsigned ell=u+1,div=a/ell,mod=a%ell;
    mpz_set_ui(d.get_mpz_t(),1);
    mpz_mul_2exp(d.get_mpz_t(),d.get_mpz_t(),ell);
    d+=3;
    mpz_powm_ui(b.get_mpz_t(),neg3.get_mpz_t(),div,d.get_mpz_t());
    mpz_mul_2exp(b.get_mpz_t(),b.get_mpz_t(),mod);
    mpz_mod(b.get_mpz_t(),b.get_mpz_t(),d.get_mpz_t());
    sq=(b*b)%d;
    pm=0;power9=1;
    for (unsigned k=0;k<r;++k) {pm=(sq*pm+power9*(b-3))%d;power9*=9;}
    h=(b*pm+3-2*u)%d;
    if(h==0) {++hits;std::cout<<"HIT valuation="<<u<<std::endl;}
    if(checked%5000==0) {
      test=(N0-2*u)%d;
      if(test!=h) {std::cerr<<"Crosscheck mismatch at u="<<u<<std::endl;return 4;}
    }
    ++checked;
    if(checked%5000==0) {
      auto now=std::chrono::steady_clock::now();
      std::cout<<"checked_low="<<checked<<" last_u="<<u<<" hits="<<hits
               <<" seconds="<<std::chrono::duration<double>(now-start).count()
               <<std::endl;
    }
  }
  std::cout<<"DONE low="<<checked<<" parent_candidates="<<hits<<std::endl;
  return hits==0?0:1;
}
