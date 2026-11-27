#define main fastprefix_main
#include "fastprefix.cpp"
#undef main
#include <random>
int main(){std::mt19937_64 gen(20261127);for(int i=0;i<50000;i++){I F=2+gen()%4294967292ull; I rem=1+gen()%std::min(I(64),F-1);Block b(F,rem);if(!b.k)continue;b.Y=gen()&b.M;I in[8],out[8];for(auto&z:in)z=gen()%F;
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
Block8(b).parent8(in,out);for(unsigned j=0;j<8;j++)if(out[j]!=b.parent(in[j]))throw std::runtime_error("vector/scalar mismatch");
#endif
for(I z:in){I got=b.parent(z),c=z;for(I q=F;q>b.q;){--q;U t=U(2)*c+((b.Y>>(q-b.q))&1);if(c>=q||t>=2*U(q)){c=missing;break;}c=t%q;}if(got!=c)throw std::runtime_error("scalar exact step mismatch");}}
std::cout<<"400000 random broad block comparisons passed\n";}
