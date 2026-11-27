#include "wide_reverse.hpp"
#include <random>
#include <iostream>
#include <cstdlib>
using namespace bb6_shifted;
I ref(I q,int k,U Y,I z,U* w=nullptr){
 U b=0;
 for(int i=k-1;i>=0;--i){U a=U(z)*2+((Y>>i)&1),v=U(q)+i;if(a>=2*v)return missing;if(a>=v){a-=v;b|=U(1)<<i;}z=I(a);}
 if(w)*w=b;return z;
}
int main(){std::mt19937_64 rng(814324766);fit_mode=7;U count=0;
 for(int t=0;t<300000;t++){
 I F=t<10000?I(3+rng()%1024):I(3+rng()%(U(UINT32_MAX)-3));
 if(t%4==0&&t>=10000)F=I(2147483648ull+rng()%2147483646ull);
 Block b(F,1+rng()%std::min(I(31),F-2));b.Y=rng()&((U(1)<<b.k)-1);
 alignas(64) U zin[8],zout[8];alignas(64) I in16[16],out16[16];
 for(int j=0;j<16;j++){in16[j]=I(rng()%F);if(j<8)zin[j]=in16[j];}
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
 Block8 v(b);_mm512_store_si512(zout,v.parent_vec(_mm512_load_si512(zin),255));
 if(F<=INT32_MAX){Block16 w(b);_mm512_store_si512(out16,w.parent_vec(_mm512_load_si512(in16),65535));}
#endif
 for(int j=0;j<16;j++){U a=0,c=0;I rr=ref(b.q,b.k,b.Y,in16[j],&a),ss=b.parent(in16[j],&c);if(rr!=ss||(rr!=missing&&a!=c)){std::cerr<<"scalar mismatch "<<F<<" "<<b.k<<"\n";return 1;}
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
 if(j<8&&rr!=zout[j]){std::cerr<<"wide SIMD mismatch "<<F<<" "<<b.k<<"\n";return 2;}
 if(F<=INT32_MAX&&rr!=out16[j]){std::cerr<<"narrow SIMD mismatch\n";return 3;}
#endif
 ++count;}
 }
 std::cout<<"PASS "<<count<<" exact comparisons\n";
}
