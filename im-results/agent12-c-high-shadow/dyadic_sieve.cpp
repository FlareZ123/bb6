// Finite dyadic congruence overapproximation of authentic Machine C.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <array>
#include <algorithm>
using U=uint32_t; using W=uint64_t;
int main(int argc,char**argv){
 U K=argc>1?atoi(argv[1]):10;if(K<1||K>14)return 2;
 U B=1U<<K,mask=B-1;W total=2*W(B)*B;
 std::vector<uint8_t> seen(total);std::vector<U> queue;
 auto add=[&](U l,U h,U o){U id=(o<<(2*K))|((h&mask)<<K)|(l&mask);if(!seen[id]){seen[id]=1;queue.push_back(id);}};
 for(U o=0;o<2;++o)for(U h=0;h<B;++h){
   add(1-h,h,o);add(0-h,h,o);
   for(U t=0;t<K;++t){U p=1U<<t;add(1+p-h,h,o);add(p-h,h,o);}
   for(U k=0;k<8;++k)add(h+1+o-k,h,o);
 }
 add(4,3,1);W births=queue.size();
 for(W head=0;head<queue.size();++head){
   U id=queue[head],o=id>>(2*K),h=(id>>K)&mask,l=id&mask;
   for(U r=1;r<K;++r){U op=(o+r+1)&1,d=(o+3*r+1-op)/2,h2=(h+d)&mask;
     add((l<<r)-h2+1-o,h2,op);}
 }
 U maxH=0,maxL=0,maxHigh=0;W low=0;
 for(U o=0;o<2;++o){std::vector<U> byL(B);
   for(U h=0;h<B;++h){U byH=0;for(U l=0;l<B;++l)
     if(seen[(o<<(2*K))|(h<<K)|l]){++byH;++byL[l];}
     maxH=std::max(maxH,byH);if(o==1)maxHigh=std::max(maxHigh,byH);
   }
   maxL=std::max(maxL,*std::max_element(byL.begin(),byL.end()));
   if(o==1)low=byL[2&mask];
 }
 for(U m=0;2*m+2<K;++m){U c=0,p=1U<<(2*m+2);for(U l=0;l<B;++l){
   U h=(p*l-3*m-4)&mask;c+=seen[(1U<<(2*K))|(h<<K)|l];}
   maxHigh=std::max(maxHigh,c);
 }
 printf("K=%u states=%llu births=%llu reachable=%llu density=%.9f maxH=%u/%u maxL=%u/%u low=%llu/%u maxHigh=%u/%u\n",
 K,(unsigned long long)total,(unsigned long long)births,(unsigned long long)queue.size(),double(queue.size())/total,maxH,B,maxL,B,(unsigned long long)low,B,maxHigh,B);
}
