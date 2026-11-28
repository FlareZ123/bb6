#include "needle-modular.hpp"
#include <random>
#include <iostream>
using namespace needle_modular;
int main(){
  gmp_randclass rng(gmp_randinit_mt);rng.seed(20261128);std::mt19937_64 r(20261128);
  for(U i=0;i<10000;i++){
    U m=8+r()%2000,b=1+r()%(64*m);Z z=rng.get_z_bits(b);if(r()&1)z=-z;
    Z f=fold_digits(z,m),D=pow2(m)+3,x=z;fold(x,m);
    Z diff=f-z;assert(mpz_divisible_p(diff.get_mpz_t(),D.get_mpz_t()));assert(bits(f)<=m);
    Z diff2=f-x;assert(mpz_divisible_p(diff2.get_mpz_t(),D.get_mpz_t()));
  }
  for(U m:{25000UL,100001UL,1000000UL}){
    Z D=pow2(m)+3;Cache c;for(U k:{U(6*m+7),U(6*m+5),U(6*m-29),U(6*m-70)}){
      U e=k*m+m/3;Z z=red(e,m,D,c),ref=2;mpz_powm_ui(ref.get_mpz_t(),ref.get_mpz_t(),e,D.get_mpz_t());Z diff=z-ref;assert(mpz_divisible_p(diff.get_mpz_t(),D.get_mpz_t()));
    }
  }
  std::cout<<"PASS digit reduction 10,000 random signed inputs and cached large powers\n";
}
