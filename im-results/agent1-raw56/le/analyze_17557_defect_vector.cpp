#include <bits/stdc++.h>
using namespace std;

// Derived-macro closure test for the next obstruction beyond the single-defect
// prefix of Raw56 leaf 17557.
//
// It starts from the exact epoch-18 macro checkpoint, replays the reachable
// low orbit to the rank-8 defect episode start k=3280*3^8, constructs the
// high partner using the proposed rho relation, and then checks one whole
// sigma^8(BA) episode.  The A/B rewrites are the exact triad formulas from
// 17557-triad-rewrite.md; this is not a primitive-machine/source theorem.
//
// Reproduction:
//   g++ -O3 -std=c++20 analyze_17557_defect_vector.cpp -o /tmp/dv
//   /tmp/dv
//
// Expected decisive observations:
//   offset 3280: a pre-existing 8-cell defect becomes 16 cells;
//   offset 9841: two separate 8-cell defects coexist;
//   full 13122-macro episode: vector relation closes back to no defects,
//   max defective zero-runs = 2, max weight = 2, right rho stays exact.

struct Run { int b; long long n; };
struct Z { vector<Run> L, R; };
static inline bool inf(long long n){ return n < 0; }
static inline long long subn(long long n,long long k){ return inf(n) ? -1 : n-k; }
static inline bool geq(long long n,long long k){ return inf(n) || n>=k; }
void add(vector<Run>&o,int b,long long n){
  if(n==0)return;
  if(!o.empty()&&o.back().b==b){
    if(inf(o.back().n)||inf(n))o.back().n=-1; else o.back().n+=n;
  } else o.push_back({b,n});
}
Z checkpoint(int n){
  long long a=(1LL<<n)-2,b=(1LL<<(n+1))-3,c=(1LL<<(n+1))-1;
  return {{{0,-1}},{{1,a},{0,1},{1,b},{0,1},{1,c},{0,-1}}};
}
void macro(Z&z,char lab){
  auto L=z.L,R=z.R;
  if(lab=='A'){
    if(R.size()<6||R[0].b!=1||R[1].b||R[2].b!=1||R[3].b||R[4].b!=1||R[5].b)
      throw runtime_error("A shape");
    auto a=R[0].n,s1=R[1].n,b=R[2].n,s2=R[3].n,c=R[4].n,zz=R[5].n;
    if(s1!=1||s2!=1||b<5||c<1||!geq(zz,2))throw runtime_error("A guard");
    vector<Run> tail(R.begin()+6,R.end());
    if(b>=6){
      vector<Run> nl; add(nl,0,b-6); add(nl,1,a+2); for(auto x:L)add(nl,x.b,x.n); z.L=move(nl);
      vector<Run> nr; add(nr,1,2); add(nr,0,1); add(nr,1,c+5); add(nr,0,subn(zz,2));
      for(auto x:tail)add(nr,x.b,x.n); z.R=move(nr);
    }else{
      long long d=0,ell; size_t pos;
      if(!L[0].b){ell=L[0].n;pos=1;}
      else{if(L.size()<2||L[1].b)throw runtime_error("carry shape");d=L[0].n;ell=L[1].n;pos=2;}
      if(!geq(ell,1))throw runtime_error("carry ell");
      vector<Run> nl; add(nl,0,subn(ell,1)); for(size_t i=pos;i<L.size();i++)add(nl,L[i].b,L[i].n); z.L=move(nl);
      vector<Run> nr; add(nr,1,d+a+4); add(nr,0,1); add(nr,1,c+5); add(nr,0,subn(zz,2));
      for(auto x:tail)add(nr,x.b,x.n); z.R=move(nr);
    }
  }else{
    if(L.empty()||L[0].b||!geq(L[0].n,7)||R.size()<4)throw runtime_error("B shape");
    auto ell=L[0].n,a=R[0].n,s=R[1].n,b=R[2].n,zz=R[3].n;
    if(a<2||s!=1||b<1||!geq(zz,2))throw runtime_error("B guard");
    vector<Run> nl; add(nl,0,subn(ell,7)); for(size_t i=1;i<L.size();i++)add(nl,L[i].b,L[i].n); z.L=move(nl);
    vector<Run> nr; add(nr,1,2); add(nr,0,1); add(nr,1,5); add(nr,0,a-1); add(nr,1,b+3);
    add(nr,0,subn(zz,2)); for(size_t i=4;i<R.size();i++)add(nr,R[i].b,R[i].n); z.R=move(nr);
  }
}
long long rho0(long long z){
  if(inf(z))return -1;
  auto q=z/8,r=z%8; return 16*q+(r==7?15:r);
}
vector<Run> rhoL(const vector<Run>&L){
  vector<Run>o; for(auto x:L)add(o,x.b,inf(x.n)?-1:(x.b?2*x.n:rho0(x.n))); return o;
}
vector<Run> rhoR(const vector<Run>&R){
  vector<Run>core(R.begin(),R.end()-1); int m=(core.size()+1)/2; vector<Run>o;
  for(int i=0;i<(int)core.size();i++){
    auto x=core[i]; long long y;
    if(x.b){
      int j=i/2+1;
      if(j==1)y=2*x.n+2; else if(j==2&&m==2)y=2*x.n+4;
      else if(j==2)y=2*x.n+3; else if(j==m)y=2*x.n+1; else y=2*x.n;
    }else{
      int j=(i+1)/2; y=j<=2?2*x.n-1:2*x.n+1;
    }
    add(o,x.b,y);
  }
  add(o,0,-1); return o;
}
bool same(const vector<Run>&a,const vector<Run>&b){
  if(a.size()!=b.size())return false;
  for(size_t i=0;i<a.size();i++)if(a[i].b!=b[i].b||a[i].n!=b[i].n)return false;
  return true;
}
// Each entry is (zero-run index, positive deficit from rhoZero).
vector<pair<int,long long>> defects(const vector<Run>&lo,const vector<Run>&hi){
  auto p=rhoL(lo); if(p.size()!=hi.size())throw runtime_error("run count");
  vector<pair<int,long long>>d; int zi=0;
  for(size_t i=0;i<p.size();i++){
    if(p[i].b!=hi[i].b)throw runtime_error("run bits");
    if(inf(p[i].n)||inf(hi[i].n)){
      if(p[i].n!=hi[i].n)throw runtime_error("infinite tail");
    }else if(p[i].n!=hi[i].n){
      if(p[i].b||p[i].n<=hi[i].n)throw runtime_error("non-defect mismatch");
      d.push_back({zi,p[i].n-hi[i].n});
    }
    if(!p[i].b&&!inf(p[i].n))zi++;
  }
  return d;
}
string sigmaWord(string w){
  string o; o.reserve(w.size()*3);
  for(char c:w)o += c=='A' ? "ABA" : "BBA";
  return o;
}
string prefixW(int n,size_t need){
  string w="ABBA";
  for(int lev=3;lev<=n;lev++){
    string v; v.reserve(min(need,w.size()*3));
    for(char c:w){
      if(v.size()>=need)break; v.push_back(c);
      if(v.size()>=need)break; v.push_back('B');
      if(v.size()>=need)break; v.push_back('A');
    }
    w.swap(v);
  }
  return w;
}
int main(){
  const long long start=3280LL*6561LL; // epoch 18, rank-8 episode
  string prefix=prefixW(18,start+1);
  Z base=checkpoint(18);
  for(long long i=0;i<start;i++)macro(base,prefix[i]);

  string episode="BA";
  for(int i=0;i<8;i++)episode=sigmaWord(episode);

  for(int rank=8;rank<=13;rank++){
    Z lowStart=base;
    Z highStart{rhoL(base.L),rhoR(base.R)};
    Z lo=lowStart, hi=highStart;
    if(!defects(lo.L,hi.L).empty()||!same(rhoR(lo.R),hi.R))return 2;

    int maxDefs=0,maxWeight=0;
    for(int j=0;j<(int)episode.size();j++){
      char c=episode[j];
      macro(lo,c);
      string sc=c=='A'?"ABA":"BBA";
      for(char d:sc)macro(hi,d);
      auto ds=defects(lo.L,hi.L);
      if(!same(rhoR(lo.R),hi.R))return 3;
      for(auto [idx,delta]:ds){
        if(delta<=0||delta%8)return 4;
        maxWeight=max(maxWeight,(int)(delta/8));
      }
      maxDefs=max(maxDefs,(int)ds.size());

      if(rank==8&&j==3280){
        if(ds.size()!=1||ds[0].first!=0||ds[0].second!=16)return 5;
        cerr<<"rank8 offset 3280: front defect weight 2 (16 cells)\n";
      }
      if(rank==8&&j==9841){
        if(ds.size()!=2||ds[0].second!=8||ds[1].second!=8)return 6;
        cerr<<"rank8 offset 9841: two 8-cell defects coexist\n";
      }
    }
    auto end=defects(lo.L,hi.L);
    cerr<<"PASS rank "<<rank<<" len="<<episode.size()
        <<" maxDefs="<<maxDefs<<" maxWeight="<<maxWeight
        <<" endDefs="<<end.size()<<"\n";
    if(!end.empty()||maxDefs!=2||maxWeight!=2)return 7;

    // The next substituted episode starts at the high partner of the current
    // episode start.  This is a local closure stress test of the relation,
    // not a claim that the high partner has been independently primitive-run.
    base=highStart;
    episode=sigmaWord(episode);
  }
  return 0;
}
