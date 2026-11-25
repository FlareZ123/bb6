// Exact decreasing-clock reverse blocks. g++ -O3 -std=c++17 reverse_block.cpp -o reverse_block
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using U = uint64_t;
using I = int64_t;
static std::array<U,65536> weighted;
static void init(){for(unsigned b=1;b<weighted.size();++b)weighted[b]=2*weighted[b/2]+2*(b/2);}
static U corr(unsigned k,U B){U h=B>>16,l=B&65535;return k*B-(weighted[l]+((weighted[h]+16*h)<<16));}
// Restricted to F<=2^31, k<=30, 2^(k+1)<=F; all products fit U.
static I fast(U F,U z,unsigned k,U Y){
 U X=(z<<k)+Y, B=X/F;
 for(unsigned j=0;j<2;++j,++B){if(B>=(U(1)<<k))break; U v=X+corr(k,B), w=F*B;
  if(v>=w&&v-w<F-k)return I(v-w);
 }
 return -1;
}
static I scalar(U F,U z,unsigned k,U Y){
 for(unsigned j=0;j<k;++j){--F;if(z>=F)return -1;z=(2*z+((Y>>(k-j-1))&1))%F;}
 return I(z);
}
static unsigned fit(U F,U left,unsigned cap){unsigned k=0;while(k<cap&&k<left&&(U(1)<<(k+2))<=F)++k;return k;}
static void regress(){
 U count=0;
 for(U F=2;F<=128;++F)for(unsigned k=0;k<=6&&(U(1)<<(k+1))<=F;++k)for(U z=0;z<F;++z)for(U y=0;y<(U(1)<<k);++y){if(fast(F,z,k,y)!=scalar(F,z,k,y))throw std::runtime_error("exhaustive mismatch");++count;}
 std::mt19937_64 rng(0xB645);for(int j=0;j<1000000;++j){U F=4+(rng()%((U(1)<<31)-4));unsigned k=fit(F,30,30);U z=rng()%F,Y=rng()%(U(1)<<k);if(fast(F,z,k,Y)!=scalar(F,z,k,Y))throw std::runtime_error("random mismatch");}
 std::cout<<"exhaustive="<<count<<" random=1000000 ok\n";
}
// Compare sorted merge scalar against hybrid block maps for a zero-target
// full terminal interval. No source-level conclusion is inferred from this test.
static std::vector<U> back(U q,const std::vector<U>& a){
 auto mid=std::lower_bound(a.begin(),a.end(),(q+1)/2),hi=std::lower_bound(a.begin(),a.end(),q),i=a.begin(),j=mid;
 std::vector<U>b;b.reserve(a.size());while(i<mid||j<hi){U l=i<mid?2*(*i):UINT64_MAX,r=j<hi?2*(*j)-q:UINT64_MAX;
  if(l<r){b.push_back(l);++i;}else if(r<l){b.push_back(r);++j;}else{b.push_back(l);++i;++j;}}
 return b;
}
static std::vector<U> image(U F,unsigned k,const std::vector<U>& a){std::vector<U>b;b.reserve(a.size());for(U z:a){I r=fast(F,z,k,0);if(r>=0)b.push_back(U(r));}std::sort(b.begin(),b.end());b.erase(std::unique(b.begin(),b.end()),b.end());return b;}
static std::vector<U> sweep(U F,U q,U threshold){std::vector<U>a(F);std::iota(a.begin(),a.end(),0);U visits=0,blocks=0,steps=0;auto start=std::chrono::steady_clock::now();
 while(F>q&&!a.empty()){visits+=a.size();unsigned k=(a.size()<=threshold)?fit(F,F-q,30):0;if(k>1){a=image(F,k,a);F-=k;++blocks;}else{a=back(F-1,a);--F;++steps;}}
 std::cout<<"threshold="<<threshold<<" visits="<<visits<<" scalar="<<steps<<" blocks="<<blocks<<" end="<<a.size()<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";return a;
}
int main(int argc,char**argv){init();regress();if(argc==3){U F=std::stoull(argv[1]),q=std::stoull(argv[2]);if(q<2||F<q||F>(U(1)<<31))return 2;auto a=sweep(F,q,0);for(U threshold:{64,1024,16384,262144})if(sweep(F,q,threshold)!=a)throw std::runtime_error("sweep mismatch");}}
