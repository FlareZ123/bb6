#pragma once
#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <limits>
#include <optional>
#include <stdexcept>
#include <vector>

namespace needle_sparse {
using U = unsigned long;
using Z = mpz_class;
struct Term { U e; Z c; };
using Terms = std::vector<Term>;
inline U bits(const Z& z) { return z==0 ? 0 : mpz_sizeinbase(z.get_mpz_t(),2); }
inline U checked_add(U a,U b) { if(b>std::numeric_limits<U>::max()-a)throw std::overflow_error("exponent addition");return a+b; }
inline U checked_mul(U a,U b) { if(a&&b>std::numeric_limits<U>::max()/a)throw std::overflow_error("exponent multiplication");return a*b; }
inline Z pow2(U e) { Z z=1;mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),e);return z; }
inline Z powm(const Z& base,U e,const Z& mod) { Z z;mpz_powm_ui(z.get_mpz_t(),base.get_mpz_t(),e,mod.get_mpz_t());return z; }

// Exact sign of a sparse signed binary sum, with no allocation for exponent gaps.
// Lower residues removed by floor division are nonnegative. The remaining carry
// gives the sign, except that zero carry with any nonzero lower residue is positive.
inline int sign(Terms t) {
  if(t.empty())return 0;
  std::sort(t.begin(),t.end(),[](const Term&a,const Term&b){return a.e<b.e;});
  U e=t.front().e; Z acc=0;bool low=false;
  for(const auto& s:t){
    U gap=s.e-e;
    if(gap&&acc!=0){
      if(gap>=bits(acc)){low=true;acc=acc<0?-1:0;}
      else {low|=!mpz_divisible_2exp_p(acc.get_mpz_t(),gap);mpz_fdiv_q_2exp(acc.get_mpz_t(),acc.get_mpz_t(),gap);}
    }
    acc+=s.c;e=s.e;
  }
  return acc==0?int(low):mpz_sgn(acc.get_mpz_t());
}

// Exact quotient by 2^m+3 for terms whose exponents are <m. No giant modulus
// is allocated when 3*coefficient mass <2^m. The fallback is also exact;
// when it is needed at least m bits occur in the coefficient-mass bound.
inline std::optional<Z> reduced_quotient(const Terms& t,U m) {
  assert(m>0);Z mass=0,Q=0;
  for(const auto& s:t){assert(s.e<m);mass+=abs(s.c);Z q;mpz_tdiv_q_2exp(q.get_mpz_t(),s.c.get_mpz_t(),m-s.e);Q+=q;}
  if(bits(3*mass)<=m){
    // |S-Q*2^m|<t.size()*2^m; if S=kD then |k|<=mass.
    // Consequently |k-Q|<t.size()+1, and every possible k is tested.
    long n=static_cast<long>(t.size());
    for(long j=-n;j<=n;++j){Z k=Q+j;Terms v=t;v.push_back({m,-k});v.push_back({0,-3*k});if(sign(std::move(v))==0)return k;}
    return std::nullopt;
  }
  Z S=0,D=pow2(m)+3;
  for(const auto& s:t){Z c=s.c;mpz_mul_2exp(c.get_mpz_t(),c.get_mpz_t(),s.e);S+=c;}
  if(!mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t()))return std::nullopt;
  Z q;mpz_divexact(q.get_mpz_t(),S.get_mpz_t(),D.get_mpz_t());return q;
}

// G_n(X,Y)=sum_{i=0}^{n-1} X^i*Y^{n-1-i}, evaluated modulo L
// by a multiplication-only binary monoid. No inverse of X-Y is required.
struct Geo { Z X,Y,G; };
inline Geo combine(const Geo& a,const Geo& b,const Z& L) {
  return {(a.X*b.X)%L,(a.Y*b.Y)%L,(a.X*b.G+b.Y*a.G)%L};
}
inline Z geometric(U n,const Z& X,const Z& Y,const Z& L) {
  assert(L>0);Geo a{1%L,1%L,0},b{X%L,Y%L,1%L};
  while(n){if(n&1)a=combine(a,b,L);n>>=1;if(n)b=combine(b,b,L);}return a.G;
}

// Decide L*(2^m+3) | sum c_i*2^e_i. For each e=q*m+s,
// 2^e=(-3)^q*2^s + (2^m+3)*2^s*G_q(2^m,-3).
// First decide the reduced quotient exactly, then recover the full quotient
// modulo L. The coefficient powers of 3 cost O(max e/m) bits, not O(m) bits.
inline bool divisible(const Terms& t,U m,const Z& L) {
  assert(m>0&&L>0);Terms reduced;reduced.reserve(t.size());
  for(const auto& s:t){U q=s.e/m;Z p;mpz_ui_pow_ui(p.get_mpz_t(),3,q);if(q&1)p=-p;reduced.push_back({s.e%m,s.c*p});}
  auto k=reduced_quotient(reduced,m);if(!k)return false;
  if(L==1)return true;
  Z rem=*k%L,X=powm(2,m,L),Y=Z(-3)%L;
  for(const auto& s:t){U q=s.e/m;if(q)rem=(rem+(s.c%L)*powm(2,s.e%m,L)*geometric(q,X,Y,L))%L;}
  return rem==0;
}

// AP = sum_{j=1}^{2r} (-3)^(2r-j)*2^(j*a). Absorb c=2^x in the exponent.
inline Terms numerator(U r,U a,U x,const Z& C) {
  Terms t{{0,C}};Z c=1;U j=checked_mul(2,r);
  while(j){t.push_back({checked_add(checked_mul(j,a),x),c});c*=-3;--j;}
  return t;
}
inline bool legal_parent(U r,U a,U x,const Z& d,const Z& L,U m) {
  assert(m>0&&L>0&&mpz_odd_p(L.get_mpz_t())&&mpz_even_p(d.get_mpz_t()));
  Z C=d+L*(5-2*Z(m));Terms t=numerator(r,a,x,C);
  if(!divisible(t,m,L))return false;
  // The quotient is odd by parity. It is a valid 2q+3 iff >=3.
  t.push_back({m,-3*L});t.push_back({0,-9*L});return sign(std::move(t))>=0;
}
} // namespace needle_sparse
