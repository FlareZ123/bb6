// Prefix-only delayed cover: no terminal endpoint sets between blocks.
// Reverse blocks use the source-proved wider quotient window 2^(k+1) <= F.
// g++ -O3 -std=c++17 prefix_only.cpp -o prefix_only
// ./prefix_only n cap block [checkpoint] [maxBlocks]
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <omp.h>
#include "block_reverse.hpp"
using namespace std;
using U=uint64_t;
struct Entry{int c,id;};
struct Prefix{string y;int c,r;};
struct DSU{vector<int>p;explicit DSU(int n):p(n,-1){}int find(int x){int r=x;while(p[r]>=0)r=p[r];while(x!=r){int y=p[x];p[x]=r;x=y;}return r;}int unite(int a,int b){a=find(a);b=find(b);if(a==b)return a;if(p[a]>p[b])swap(a,b);p[a]+=p[b];p[b]=a;return a;}};
// Exact broad fixed-target live set, initially jumped by a modular subset sum.
template<class Bit>vector<Entry>live(int q0,int F,Bit y,U&work){
 int r=min(22,F-q0),q=F-r;uint32_t M=1u<<r,mask=M-1,Y=0;
 for(int j=0;j<r;j++)Y|=uint32_t(y(q+j))<<j;
 vector<uint8_t>seen(M);vector<uint32_t>res{Y};seen[Y]=1;
 for(int j=0;j<r;j++){uint32_t shift=uint32_t((U(q+j)<<j)&mask),count=res.size();for(uint32_t i=0;i<count;i++){uint32_t c=(res[i]-shift)&mask;if(!seen[c]){seen[c]=1;res.push_back(c);}}}
 sort(res.begin(),res.end());vector<Entry>a,b;
 for(U base=0;base<U(q);base+=M)for(auto x:res){U c=base+x;if(c>=U(q))break;a.push_back({int(c),0});}
 while(q>q0&&!a.empty()){
  int k=fit(q,q-q0),p=q-k;U bits=0;for(int j=0;j<k;j++)bits|=U(y(p+j))<<j;
  work+=a.size();size_t w=0;for(auto e:a){int c=blockParent(p,k,e.c,bits,false);if(c>=0)a[w++]={c,0};}a.resize(w);radix(a,b);
  a.erase(unique(a.begin(),a.end(),[](Entry a,Entry b){return a.c==b.c;}),a.end());q=p;
 }
 return a;
}
// Which mid-window endpoints rewind to this prefix's original carry?
// Only the tiny already-rewound mid set needs endpoint labels.
template<class Bit>vector<int>filter(int q0,int F,Bit y,int root,vector<Entry>a,U&work){
 vector<int>ends;ends.reserve(a.size());for(int i=0;i<(int)a.size();i++){ends.push_back(a[i].c);a[i].id=i;}
 DSU d(a.size());vector<Entry>b;
 while(F>q0&&!a.empty()){
  int k=fit(F,F-q0),p=F-k;U bits=0;for(int j=0;j<k;j++)bits|=U(y(p+j))<<j;
  work+=a.size();size_t w=0;for(auto e:a){int c=blockParent(p,k,e.c,bits,false);if(c>=0)a[w++]={c,e.id};}a.resize(w);radix(a,b);w=0;
  for(auto e:a){if(w&&a[w-1].c==e.c)a[w-1].id=d.unite(a[w-1].id,e.id);else a[w++]=e;}a.resize(w);F=p;
 }
 auto it=lower_bound(a.begin(),a.end(),root,[](Entry a,int r){return a.c<r;});if(it==a.end()||it->c!=root)return {};
 int label=d.find(it->id);vector<int>out;for(int i=0;i<(int)ends.size();i++)if(d.find(i)==label)out.push_back(ends[i]);return out;
}
void save(const string&p,int n,int s,const vector<Prefix>&gs,U work,U filterWork,int maxgap){if(p.empty())return;ofstream o(p+".tmp",ios::binary);auto w=[&](auto x){o.write(reinterpret_cast<const char*>(&x),sizeof(x));};w(n);w(s);w(work);w(filterWork);w(maxgap);U m=gs.size();w(m);for(const auto&g:gs){w(g.c);w(g.r);o.write(g.y.data(),s);}o.close();if(!o||rename((p+".tmp").c_str(),p.c_str()))throw runtime_error("checkpoint write");}
bool load(const string&p,int n,int&s,vector<Prefix>&gs,U&work,U&filterWork,int&maxgap){if(p.empty())return false;ifstream i(p,ios::binary);if(!i)return false;auto r=[&](auto&x){i.read(reinterpret_cast<char*>(&x),sizeof(x));};int nn;r(nn);if(nn!=n)throw runtime_error("checkpoint n");r(s);r(work);r(filterWork);r(maxgap);U m;r(m);gs.resize(m);for(auto&g:gs){r(g.c);r(g.r);g.y.resize(s);i.read(g.y.data(),s);}if(!i)throw runtime_error("checkpoint read");return true;}
int main(int argc,char**argv){
 if(argc<4||argc>6)return 2;int n=stoi(argv[1]),K=stoi(argv[2]),block=stoi(argv[3]);string p=argc>=5?argv[4]:"";int maxBlocks=argc>=6?stoi(argv[5]):-1;
 if(n<14||n%2||K<=n||n>100000000||K>100000000||block<1||block>n)return 2;
 U A=U(n)+K+2,L=2*(U(n)+3*U(K)+10)+6,prod=A*L;auto safe=[&](int g){int e=n-g;return e>=62||(e>=0&&(U(6)<<e)>prod);};if((n<63&&A>(U(1)<<n))||!safe(0)||!safe(1))return 3;
 auto t=chrono::steady_clock::now();auto sec=[&](){return chrono::duration<double>(chrono::steady_clock::now()-t).count();};
 int s=1,maxgap=1;U work=0,filterWork=0;vector<Prefix>gs={{"1",(n+2)/2,3}};load(p,n,s,gs,work,filterWork,maxgap);
 if(gs.empty()){cout<<"END "<<n<<" "<<n+s<<endl;return 0;}
 for(int blocks=0;s+n<=K;blocks++){
  // h may be chosen independently of the prior blocks. At this stage only
  // the original lookahead n at s is used to obtain the new prefixes.
  int h=min(block,n);vector<Prefix>next;size_t midTotal=0;
  struct Part{vector<Prefix>next;U work=0,filterWork=0;size_t mids=0;int maxgap=0;};
  vector<Part>parts(gs.size());
  #pragma omp parallel for schedule(dynamic)
  for(int gi=0;gi<(int)gs.size();gi++){const auto&g=gs[gi];auto &part=parts[gi];auto y=[&](int q){int i=q-n-3;return i<n?0:g.y[i-n]-'0';};
   auto mids=live(n+s+h+3,2*n+s+3,y,part.work);part.mids=mids.size();
   auto good=filter(n+s+3,n+s+h+3,y,g.c,move(mids),part.filterWork);
   for(int a:good){int c=a;string extra(h,'0');for(int i=s+h-1;i>=s;i--){int q=n+i+3,v=2*c+y(q);if(v>=2*q)throw runtime_error("bad rewind");if(v>=q){extra[i-s]='1';v-=q;}c=v;}if(c!=g.c)throw runtime_error("wrong root");
    Prefix g2={g.y,a,g.r};int last=g2.y.back()-'0',run=0;for(int k=s-1;k>=0&&g2.y[k]==g2.y.back();k--)run++;
    for(int j=0;j<h;j++){int v=g2.r+7*(extra[j]-'0'),bit=v%2;g2.r=v/2;g2.y+=char('0'+bit);run=bit==last?run+1:1;last=bit;int gap=min(s+j+1,run+1);part.maxgap=max(part.maxgap,gap);if(!safe(gap))throw runtime_error("margin");}
    part.next.push_back(move(g2));
   }
  }
  for(auto &part:parts){work+=part.work;filterWork+=part.filterWork;midTotal+=part.mids;maxgap=max(maxgap,part.maxgap);for(auto &g:part.next)next.push_back(move(g));}
  cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<midTotal<<" next="<<next.size()<<" work="<<work<<" filter="<<filterWork<<" gap="<<maxgap<<" sec="<<sec()<<endl;
  if(next.empty()){gs.clear();save(p,n,s,gs,work,filterWork,maxgap);cout<<"END "<<n<<" "<<n+s<<endl;return 0;}
  if(s+h+n>K)break;s+=h;gs=move(next);save(p,n,s,gs,work,filterWork,maxgap);if(blocks+1==maxBlocks)break;
 }
 cout<<"END "<<n<<" 0"<<endl;return 1;
}
