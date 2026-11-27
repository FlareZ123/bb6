// Comparative deterministic exact benchmark for the fused partial-map pipeline.
#define main prefix_main
#include "compact_prefix.cpp"
#undef main
#include <iomanip>

static U mix(U x){
 x+=0x9e3779b97f4a7c15ull;x=(x^(x>>30))*0xbf58476d1ce4e5b9ull;
 x=(x^(x>>27))*0x94d049bb133111ebull;return x^(x>>31);
}
static U target(I q,unsigned k){
 unsigned j=q&63;U x=mix(q/64)>>j;
 if(j&&k>64-j)x|=mix(U(q/64)+1)<<(64-j);
 return x&mask(k);
}
int main(int argc,char** argv){
 I F=argc>1?I(std::stoul(argv[1])):650000000u;
 I len=argc>2?I(std::stoul(argv[2])):1000000u;
 if(F<100||len<1||len>=F/2)return 2;
 I start=F-len;
 vector<I> ref,ref_filter;
 I root=0;
 double baseline=0;
 for(unsigned lim:{1u,16u,64u,128u}){
  fusion_limit=lim;U visits=0,fw=0;
  auto t=std::chrono::steady_clock::now();
  auto a=live(start,F,target,visits);
  double live_sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
  std::sort(a.begin(),a.end());
  if(lim==1){
   ref=a;baseline=live_sec;
   // Find a genuine root for a shorter prefix. All comparisons include it.
   for(I c:a){I q=start,z=c;
    while(q>start-len&&z!=missing){Block b(q,q-(start-len));b.Y=target(b.q,b.k);z=b.parent(z);q=b.q;}
    if(z!=missing){root=z;break;}
   }
  }else if(a!=ref)throw std::runtime_error("fused live image mismatch");
  t=std::chrono::steady_clock::now();
  auto f=filter(start-len,start,target,root,a,fw);
  double filter_sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
  if(lim==1)ref_filter=f;else if(f!=ref_filter)throw std::runtime_error("fused labelled image mismatch");
  std::cout<<std::fixed<<std::setprecision(3)<<"F="<<F<<" len="<<len<<" fuse="<<lim
    <<" live="<<a.size()<<" filter="<<f.size()<<" root="<<root<<" visits="<<visits<<" fvisits="<<fw
    <<" live_sec="<<live_sec<<" filter_sec="<<filter_sec<<" speedup="<<baseline/live_sec<<std::endl;
 }
}
