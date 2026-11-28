// Exact long-period side-cycle discovery for the 671 Raw54 E1=1RD residuals.
// Untrusted discovery; every emitted candidate is intended for Lean replay.
#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <unordered_map>
#include <algorithm>
#include <cstdint>
#include <cassert>
using namespace std;

constexpr int L=39447;
constexpr int W=16384;
constexpr int O=W/2;
constexpr int MAXPERIOD=16384;
using Tape=array<uint64_t,W/64>;
using Table=array<int,12>;

struct Cfg{int q,h;Tape t;uint64_t left=0,right=0;};
struct Res{int typ,n,s,e,k,dir,b;}; // 0 open, 1 unknown, 2 cycle

uint64_t word(const Tape&t,int i){return i>=0&&i<W/64?t[i]:0;}
uint64_t window(const Tape&t,int x){
  int i=x/64,j=x%64;
  if(j<0){i--;j+=64;}
  return j?(word(t,i)>>j)|(word(t,i+1)<<(64-j)):word(t,i);
}
int read(const Cfg&c){
  assert(c.h>=0&&c.h<W);
  return (c.t[c.h/64]>>(c.h%64))&1;
}
void move(Cfg&c,int a){
  assert(c.h>=0&&c.h<W);
  uint64_t m=uint64_t(1)<<(c.h%64);
  auto &v=c.t[c.h/64];
  if(a/12)v|=m;else v&=~m;
  c.h+=a%12>=6?1:-1;c.q=a%6;
  assert(c.h>64&&c.h<W-64);
}
void sig(Cfg&c){c.left=window(c.t,c.h-63);c.right=window(c.t,c.h);}
bool eqR(const Cfg&a,const Cfg&b,int low,int d){
  for(int i=low;i<W;i+=64)if(window(a.t,i)!=window(b.t,i+d))return false;
  return true;
}
bool eqL(const Cfg&a,const Cfg&b,int high,int d){
  for(int i=high-63;i>=-63;i-=64)if(window(a.t,i)!=window(b.t,i+d))return false;
  return true;
}
uint64_t key(int q,uint64_t x){
  return x ^ (0x9e3779b97f4a7c15ULL*uint64_t(q+1));
}

int encode(char w,char r,char q){return (w-'0')*12+(r=='R')*6+(q-'A');}
string decode(int a){if(a<0)return a==-1?"---":"HHH";return string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
Table parse(string str){
  str.erase(remove(str.begin(),str.end(),'_'),str.end());
  assert(str.size()==36);Table p;
  for(int i=0;i<12;i++)p[i]=str[3*i]=='-'?-1:encode(str[3*i],str[3*i+1],str[3*i+2]);
  return p;
}
string show(const Table&p){
  string s;for(int i=0;i<12;i++){if(i&&i%2==0)s+="_";s+=decode(p[i]);}return s;
}

Res classify(const Table&p){
  vector<Cfg> tr; tr.reserve(L+1);
  unordered_map<uint64_t,vector<int>> rightSeen,leftSeen;
  rightSeen.reserve(L);leftSeen.reserve(L);
  Cfg c{0,O,{}};
  for(int n=0;n<=L;n++){
    int s=2*c.q+read(c);
    if(p[s]<0)return {1,n,s,0,0,0,0};
    sig(c);
    uint64_t kr=key(c.q,c.right), kl=key(c.q,c.left);

    if(auto it=rightSeen.find(kr);it!=rightSeen.end()){
      auto &v=it->second;
      for(auto z=v.rbegin();z!=v.rend();++z){
        int j=*z;if(n-j>MAXPERIOD)break;
        int d=c.h-tr[j].h;if(d<0)continue;
        int low=c.h;for(int x=j;x<n;x++)low=min(low,tr[x].h);
        if(eqR(tr[j],c,low,d))return {2,0,0,j,n-j,1,low-O};
      }
    }
    if(auto it=leftSeen.find(kl);it!=leftSeen.end()){
      auto &v=it->second;
      for(auto z=v.rbegin();z!=v.rend();++z){
        int j=*z;if(n-j>MAXPERIOD)break;
        int d=c.h-tr[j].h;if(d>0)continue;
        int high=c.h;for(int x=j;x<n;x++)high=max(high,tr[x].h);
        if(eqL(tr[j],c,high,d))return {2,0,0,j,n-j,0,high-O};
      }
    }
    tr.push_back(c);
    rightSeen[kr].push_back(n);leftSeen[kl].push_back(n);
    move(c,p[s]);
  }
  return {0,0,0,0,0,0,0};
}

int main(int argc,char**argv){
  if(argc!=3){cerr<<"usage: oneRD_residual_lasso OPEN OUT\n";return 2;}
  ifstream in(argv[1]);ofstream out(argv[2]);
  string code;long long open=0,hit=0,cyc=0;int maxPeriod=0,maxEntry=0,maxHit=0;
  while(in>>code){
    Table p=parse(code);Res r=classify(p);
    out<<code<<"\t";
    if(r.typ==2){
      cyc++;maxPeriod=max(maxPeriod,r.k);maxEntry=max(maxEntry,r.e);
      out<<"[\"cycle\","<<r.e<<","<<r.k<<","<<(r.dir?"true":"false")<<","<<r.b<<"]";
    }else if(r.typ==1){
      hit++;maxHit=max(maxHit,r.n);
      out<<"[\"lastCandidate\","<<r.n<<","<<r.s<<"]";
    }else{
      open++;out<<"[\"open\"]";
    }
    out<<"\n";
  }
  cout<<"cycle="<<cyc<<" hit="<<hit<<" open="<<open<<" total="<<(cyc+hit+open)
      <<" max_period="<<maxPeriod<<" max_entry="<<maxEntry<<" max_hit="<<maxHit<<"\n";
  assert(cyc+hit+open==671);
}
