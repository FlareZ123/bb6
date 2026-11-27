// Exact first-hole/late trace with arbitrary precision head-relative snapshots.
// Witnesses are candidate data; Lean checks them independently.
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/functional/hash.hpp>
#include <array>
#include <vector>
#include <unordered_map>
#include <fstream>
#include <iostream>
#include <string>
#include <algorithm>
#include <chrono>
using namespace std;using boost::multiprecision::cpp_int;
using T=array<int,12>;using I=cpp_int;
struct C{int q,h;I l,r;};
struct K{int q;I x;bool operator==(const K&b)const{return q==b.q&&x==b.x;}};
struct H{size_t operator()(const K&k)const{size_t h=boost::hash<I>()(k.x);boost::hash_combine(h,k.q);return h;}};
struct W{char kind;int n=0,p=0,dir=0,boundary=0,slot=0;};
constexpr int LIM=16384,CL=2048;
W trace(const T&t){
 array<unsigned char,2*LIM+5> tape{};unsigned char* a=tape.data()+LIM+2;I l=0,r=0;int q=0,h=0;
 vector<C> hist;hist.reserve(CL);unordered_map<K,vector<int>,H> left,right;left.reserve(CL);right.reserve(CL);
 for(int n=0;n<=LIM;n++){
  int slot=2*q+a[h],v=t[slot];if(v<=0)return {v<0?'b':'h',n,0,0,0,slot};
  if(n<CL){
   auto &rs=right[K{q,r}],&ls=left[K{q,l}];
   for(auto it=rs.rbegin();it!=rs.rend();++it){int j=*it;if(hist[j].l==l){int dir=h>=hist[j].h,b=h;for(int k=j;k<n;k++)b=dir?min(b,hist[k].h):max(b,hist[k].h);return {'c',j,n-j,dir,b,0};}}
   for(auto it=rs.rbegin();it!=rs.rend();++it){int j=*it,oh=hist[j].h;if(h<=oh)continue;int lo=h;for(int k=j;k<n;k++)lo=min(lo,hist[k].h);if(((l^hist[j].l)&((I(1)<<(oh-lo))-1))==0)return {'s',j,n-j,1,lo,0};}
   for(auto it=ls.rbegin();it!=ls.rend();++it){int j=*it,oh=hist[j].h;if(h>=oh)continue;int hi=h;for(int k=j;k<n;k++)hi=max(hi,hist[k].h);if(((r^hist[j].r)&((I(1)<<(hi-oh+1))-1))==0)return {'s',j,n-j,0,hi,0};}
   hist.push_back({q,h,l,r});rs.push_back(n);ls.push_back(n);
   if(rs.size()>4)rs.erase(rs.begin());if(ls.size()>4)ls.erase(ls.begin());
   int x=v-1,w=x/2%2;if(x%2){l=(l<<1)|w;r>>=1;}else{r=(((r>>1)<<1)|w)<<1|(l&1);l>>=1;}
  }
  if(n==LIM)return {'o',n};
  int x=v-1;a[h]=x/2%2;h+=(x%2?1:-1);q=x/4;
 }
 return {'o',LIM};
}
void row(ostream&o,const T&t){o<<'[';for(int i=0;i<12;i++){if(i)o<<',';o<<t[i];}o<<']';}
int main(int argc,char**argv){if(argc!=2)return 2;int target=atoi(argv[1]);string z=to_string(target);ifstream in("rlehard"+z+".txt");ofstream out("late"+z+".json"),open("wide-start"+z+".txt");if(!in||!out||!open)return 3;vector<T> pending;T t;while(in>>t[0]){for(int i=1;i<12;i++)in>>t[i];pending.push_back(t);}int cnt=0,holes=0,halts=0,cycles=0,res=0,mx=0;bool first=true;out<<'[';auto start=chrono::steady_clock::now();
 while(!pending.empty()){t=pending.back();pending.pop_back();auto w=trace(t);cnt++;if(w.kind=='o'){for(int v:t)open<<v<<' ';open<<'\n';res++;continue;}if(!first)out<<',';first=false;out<<'[';row(out,t);out<<",[";
 if(w.kind=='b'){holes++;out<<"\"hole\","<<w.slot;int lo=w.slot==target?0:1,hi=w.slot==target?0:24;for(int v=lo;v<=hi;v++){T u=t;u[w.slot]=v;pending.push_back(u);}}
 else if(w.kind=='h'){halts++;mx=max(mx,w.n+1);out<<"\"halt\","<<w.n<<','<<w.slot;}
 else{cycles++;out<<(w.kind=='c'?"\"cycle\",":"\"side\",")<<w.n<<','<<w.p<<','<<(w.dir?"true":"false")<<','<<w.boundary;}
 out<<"]]";
 }out<<"]\n";cout<<target<<" traces "<<cnt<<" holes "<<holes<<" halts "<<halts<<" cycles "<<cycles<<" open "<<res<<" max "<<mx<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
