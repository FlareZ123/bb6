// Exact block-macro simulation, local transitions evaluated from the supplied table.
// Every block entry starts at its left edge when dir=1, otherwise right edge.
#include <array>
#include <vector>
#include <iostream>
#include <cstdint>
#include <algorithm>
using namespace std;
using Table=array<int,12>;
constexpr unsigned W=12,A=1<<W;
struct Result { uint16_t bits; uint8_t q,dir,kind,slot; uint32_t steps; };
Result compute(const Table&p,unsigned a,unsigned q,unsigned d){
 int h=d?0:W-1; unsigned n=0;
 while(h>=0 && h<(int)W){
  unsigned s=2*q+((a>>h)&1),v=p[s];
  if(v==24)return {uint16_t(a),uint8_t(q),uint8_t(d),1,uint8_t(s),n};
  a=(a&~(1u<<h))|(((v>>1)&1)<<h);h+=(v&1)?1:-1;q=v>>2;
  if(++n>6*W*A)return {uint16_t(a),uint8_t(q),uint8_t(d),2,0,n};
 }
 return {uint16_t(a),uint8_t(q),uint8_t(h>=0),0,0,n};
}
int main(int argc,char**argv){
 uint64_t limit=argc>1?stoull(argv[1]):100000000;
 int id; Table p;
 while(cin>>id){
  for(int&v:p)cin>>v;
  vector<Result> cache(A*12); vector<uint8_t> seen(A*12);
  vector<uint16_t> left(1,0),right(1,0);
  int64_t b=0,lo=0,hi=0;unsigned q=0,d=1;uint64_t n=0,mac=0;
  unsigned kind=0,slot=0;
  while(n<limit){
   auto &vec=b<0?left:right;
   size_t j=b<0?size_t(-b-1):size_t(b);
   if(j>=vec.size())vec.resize(j+1,0);
   unsigned a=vec[j],i=(2*q+d)*A+a;
   if(!seen[i]){cache[i]=compute(p,a,q,d);seen[i]=1;}
   Result r=cache[i];n+=r.steps;mac++;vec[j]=r.bits;
   if(r.kind){kind=r.kind;slot=r.slot;break;}
   q=r.q;d=r.dir;b+=d?1:-1;
   lo=min(lo,b);hi=max(hi,b);
  }
  cout<<id<<' '<<(kind==1?"hole":kind==2?"internal_cycle":"open")<<' '<<n<<' '<<slot<<" blocks "<<lo<<' '<<hi<<" macro "<<mac<<endl;
 }
}
