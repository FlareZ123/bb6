// Exact finite screening, using the recurrence proved in BatchCarry.lean.
// Build: g++ -O3 -std=c++17 batch.cpp -o batch
// Usage: ./batch L R ; common clock F=2*L+3, with L<=R<=2*L-1.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 uint32_t L=argc>1?stoul(argv[1]):1000002,R=argc>2?stoul(argv[2]):1500000;
 if(L<14||L>100000000||R<L||uint64_t(R)+4>2*uint64_t(L)+3)return 2;
 uint32_t F=2*L+3;
 vector<uint32_t> live,next,stamp(F+1);
 for(uint32_t c=1;c<=F-3;c++)live.push_back(c);
 uint64_t work=0;vector<uint32_t> survivors;
 for(uint32_t q=F-1;q>=L+4;q--){
  next.clear();work+=live.size();
  for(auto c:live){
   uint32_t p=2*c;if(p>=q)p-=q;
   if(p>=1&&p<=q-3&&stamp[p]!=q){stamp[p]=q;next.push_back(p);}
  }
  live.swap(next);
  if(q<=R+4&&q%2==0&&stamp[(q-2)/2]==q)survivors.push_back(q-4);
  if(live.empty()){cout<<"empty at q="<<q<<'\n';break;}
 }
 cout<<"L="<<L<<" R="<<R<<" F="<<F<<" work="<<work
     <<" survivors="<<survivors.size()<<" final_width="<<live.size()<<'\n';
 for(auto n:survivors)cout<<n<<' ';cout<<'\n';
}
