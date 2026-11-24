#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <bit>
#include <vector>
#include <utility>
#include <chrono>
using U=uint64_t; using W=__uint128_t;
struct G { U r,n,z; bool operator==(const G&) const = default;};
void scalar(G &g){assert(g.r); if(!g.z)g.z=1;else if(g.z>=g.n-g.z){g.z=g.z-(g.n-g.z);--g.r;}else g.z*=2; ++g.n;}
template<unsigned T> struct Batch {
 static constexpr unsigned B=1u<<T;
 std::vector<unsigned> J, count;
 Batch():J(B),count(B){for(unsigned w=1;w<B;w++){unsigned k=std::countr_zero(w); J[w]=J[w&(w-1)]+(T-1-k)*(1u<<k);count[w]=count[w&(w-1)]+1;}}
 bool run(G &g) const {
  if(g.n<B || g.r<=T || !g.z)return false;
  W q=W(g.z)<<T;
  unsigned w=unsigned(q/g.n);assert(w<B);
  W f=W(g.n)*w+J[w];
  if(f>q){assert(w);--w;f=W(g.n)*w+J[w];}
  assert(f<=q);U z=U(q-f);
  if(!z)return false;
  g.z=z;g.r-=count[w];g.n+=T;return true;
 }
};
std::pair<U,U> evalK(U k,U c){if(!c)c=1;while(c<=k){k-=c;c=2*c+1;}return{2*k+2,c-k-1};}
std::pair<U,U> source(U a,U c){U d=0;while(a--){if(!c){auto p=evalK(d+1,0);d=p.first;c=p.second;}else if(c-1<=d+1){auto p=evalK(d+2-c,2*c-1);d=p.first;c=p.second;}else{c-=d+3;d=2*d+4;}}return {d+1,c};}
int main(int argc,char**argv){
 Batch<16> b;Batch<8> small;
 for(U n=256;n<1024;n++)for(U z=1;z+2<=n;z++){G x{100,n,z},y=x;if(small.run(x)){for(unsigned j=0;j<8;j++)scalar(y);assert(x==y);}}
 U rand=12345;for(unsigned i=0;i<100000;i++){rand=rand*6364136223846793005ULL+1;U n=65536+(rand>>25);rand=rand*6364136223846793005ULL+1;U z=1+rand%(n-2);G x{100,n,z},y=x;if(b.run(x)){for(unsigned j=0;j<16;j++)scalar(y);assert(x==y);}}
 for(U a=0;a<100;a++)for(U c=1;c<100;c++){G g{a,c+3,c};while(g.r)scalar(g);auto p=source(a,c);assert(g.z==p.second&&g.n-g.z-2==p.first);}
 U a=0,c=1,section=0,cap=argc>1?strtoull(argv[1],nullptr,10):1000000000ULL;
 if(argc>=5){section=strtoull(argv[2],nullptr,10);a=strtoull(argv[3],nullptr,10);c=strtoull(argv[4],nullptr,10);}
 U steps=0;auto begin=std::chrono::steady_clock::now();
 while(steps<cap){printf("section %llu a=%llu c=%llu steps=%llu\n",(unsigned long long)section,(unsigned long long)a,(unsigned long long)c,(unsigned long long)steps);fflush(stdout);G g{a,c+3,c};U zero=0;while(g.r && steps+g.n-(c+3)<cap){if(!g.z)++zero;if(!b.run(g)&&!small.run(g))scalar(g);}
 steps+=g.n-(c+3);
 if(g.r){printf("incomplete r=%llu n=%llu z=%llu\n",(unsigned long long)g.r,(unsigned long long)g.n,(unsigned long long)g.z);return 0;}
 if(!g.z){printf("HALT section=%llu terminal modulus=%llu zero_rescues=%llu\n",(unsigned long long)section,(unsigned long long)g.n,(unsigned long long)zero);return 0;}
 printf("  rescues=%llu seconds=%.3f\n",(unsigned long long)zero,std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count());a=g.n-g.z-2;c=g.z;++section;
 }
}
