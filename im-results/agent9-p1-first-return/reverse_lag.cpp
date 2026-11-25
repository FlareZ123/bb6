// Exact reverse-forest image propagation for Agent45's delayed-bit model.
// g++ -O3 -std=c++17 reverse_lag.cpp -o reverse_lag
// Usage: ./reverse_lag n cap [block]; positive END is a safe extinction horizon.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
using U=uint64_t;
struct DSU {
 vector<int> p;
 explicit DSU(int n):p(n,-1){}
 int find(int x){int r=x;while(p[r]>=0)r=p[r];while(x!=r){int y=p[x];p[x]=r;x=y;}return r;}
 void unite(int x,int y){x=find(x);y=find(y);if(x==y)return;if(p[x]>p[y])swap(x,y);p[x]+=p[y];p[y]=x;}
};
struct Entry{int c,id;};
struct Forest {
 DSU d; vector<Entry> a,b; U visits=0;
 explicit Forest(int n):d(n){a.reserve(n);b.reserve((n+1)/2);}
 void step(int q,int y){
  visits+=a.size();b.clear();
  // Both valid affine branches are individually sorted and injective.
  // An endpoint c>=q has 2*c+y>=2*q and no legal predecessor.
  size_t split=lower_bound(a.begin(),a.end(),(q-y+1)/2,[](Entry a,int x){return a.c<x;})-a.begin();
  size_t hi=lower_bound(a.begin(),a.end(),q,[](Entry a,int x){return a.c<x;})-a.begin();
  size_t i=0,j=split;
  while(i<split||j<hi){
   int l=i<split?2*a[i].c+y:INT32_MAX;
   int r=j<hi?2*a[j].c+y-q:INT32_MAX;
   if(l<r){b.push_back({l,a[i++].id});}
   else if(r<l){b.push_back({r,a[j++].id});}
   else{d.unite(a[i].id,a[j].id);b.push_back({l,a[i++].id});j++;}
  }
  a.swap(b);
 }
};
// Exact endpoints of a fixed-target block, by rewinding all possible
// endpoints to their unique predecessor and grouping common ancestors.
template<class Bit> vector<int> image(int n,int s,int h,const vector<int>&starts,Bit y,U&work){
 int F=n+s+h+3;
 Forest f(F);
 for(int c=0;c<F;c++)f.a.push_back({c,c});
 for(int i=s+h-1;i>=s&&!f.a.empty();i--)f.step(n+i+3,y(i));
 work+=f.visits;
 vector<uint8_t> keep(F);auto it=starts.begin();
 for(auto e:f.a){it=lower_bound(it,starts.end(),e.c);if(it!=starts.end()&&*it==e.c)keep[f.d.find(e.id)]=1;}
 vector<int> out;for(int c=0;c<F;c++)if(keep[f.d.find(c)])out.push_back(c);
 return out;
}
struct Group{string y;int c,r;vector<int> ends;};
int run(int n,int K,int block){
 if(n<14||n%2||K<=n||block<1||n>100000000||K>100000000)return -1;
 U A=U(n)+K+2,L=2*(U(n)+3*U(K)+10)+6,prod=A*L;
 auto safe=[&](int g){int e=n-g;return e>=62||(e>=0&&(U(6)<<e)>prod);};
 if((n<63&&A>(U(1)<<n))||!safe(0)||!safe(1))return -3;
 auto t=chrono::steady_clock::now();auto sec=[&](){return chrono::duration<double>(chrono::steady_clock::now()-t).count();};
 U reverse=0,images=0,groups=0;int peak=1,maxgap=1;
 auto first=image(n,1,n,{(n+2)/2},[&](int i){return int(i==n);},images);
 cout<<"n="<<n<<" width(n+1)="<<first.size()<<" image_visits="<<images<<" sec="<<sec()<<endl;
 if(first.empty())return n+1;
 vector<Group> live={{"1",(n+2)/2,3,move(first)}};
 for(int s=1;s<K-n;){
  int h=min({block,n,K-n-s});vector<Group> next;
  for(auto &g:live){
   auto &ends=g.ends; Forest f(ends.size());
   for(int j=0;j<(int)ends.size();j++)f.a.push_back({ends[j],j});
   auto bit=[&](int i){return i<n?0:g.y[i-n]-'0';};
   for(int i=n+s-1;i>=s+h;i--)f.step(n+i+3,bit(i));
   reverse+=f.visits;groups+=f.a.size();
   vector<int> index(ends.size(),-1);
   vector<vector<int>> parts(f.a.size());
   for(int j=0;j<(int)f.a.size();j++)index[f.d.find(f.a[j].id)]=j;
   for(int j=0;j<(int)ends.size();j++){
    int k=index[f.d.find(j)];if(k<0)return -4;parts[k].push_back(ends[j]);
   }
   for(int j=0;j<(int)f.a.size();j++){
    int aend=f.a[j].c,c=aend;string extra(h,'0');
    for(int i=s+h-1;i>=s;i--){int C=n+i+3,t=2*c+bit(i);if(t>=2*C)return -4;if(t>=C){extra[i-s]='1';t-=C;}c=t;}
    if(c!=g.c)return -5;
    string y=g.y;int r=g.r,last=y.back()-'0',run=0;for(int k=s-1;k>=0&&y[k]==y.back();k--)run++;
    // Check the whole block, even if its endpoint set will be empty.
    for(int k=0;k<h;k++){int t=r+7*(extra[k]-'0'),v=t%2;r=t/2;y+=char('0'+v);run=v==last?run+1:1;last=v;int gap=min(s+k+1,run+1);maxgap=max(maxgap,gap);if(!safe(gap))return -3;}
    auto out=image(n,n+s,h,parts[j],[&](int i){return y[i-n]-'0';},images);
    if(!out.empty())next.push_back({move(y),aend,r,move(out)});
   }
  }
  s+=h;live=move(next);peak=max(peak,int(live.size()));
  cout<<"s="<<s<<" live="<<live.size()<<" peak="<<peak<<" groups="<<groups<<" reverse="<<reverse<<" image_visits="<<images<<" gap="<<maxgap<<" sec="<<sec()<<endl;
  if(live.empty())return n+s;
 }
 return 0;
}
int main(int argc,char**argv){if(argc<3||argc>4)return 2;int n=stoi(argv[1]),K=stoi(argv[2]),b=argc>3?stoi(argv[3]):max(1,n/8);int r=run(n,K,b);cout<<"END "<<n<<" "<<r<<endl;return r>0?0:1;}
