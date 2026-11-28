// Raw54 E1=1RD: deterministic one-edge mutations of source FAR DFA bank.
// Untrusted discovery only: every claim needs FAR.Data.fastValid proof replay.
// Invariant: dfa[0] == 0, the blank zero-tail start state. Mutating that edge
// creates unsound false positives and is deliberately forbidden.
// Usage: oneRD_mutant_bank BANK_CODES LASSO_TSV OUTPUT_TSV
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using U = unsigned __int128;
using Table = array<int,12>;
using Dfa = vector<int>;
struct Rule {int dst,src,off;};
struct Entry {bool rev;Dfa dfa;};

static U compose(U mask,const U* rows) {
  U v=0;
  while(mask) {
    uint64_t lo=(uint64_t)mask;
    int j=lo?__builtin_ctzll(lo):64+__builtin_ctzll((uint64_t)(mask>>64));
    v|=rows[j];
    mask&=mask-1;
  }
  return v;
}
static bool far(const Table& m,const Dfa& dfa,bool rev) {
  int d=(int)dfa.size()/2,N=6*d+1,H=N-1;
  assert(0<d && d<=20 && (int)dfa.size()==2*d && dfa[0]==0);
  U T[254]{};Rule rules[10000];int nr=0;
  U halt=U(1)<<H;
  T[H]=T[N+H]=halt;
  for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++) {
    int v=m[2*q+a],x=v<0?-1:4*(v%6)+2*(v/12)+((v%12)>=6);
    int i=a*N+6*l+q;
    if(x<0){T[i]=halt;continue;}
    int w=(x>>1)&1,n=x/4;
    if(bool(x&1)!=rev)T[i]=U(1)<<(6*dfa[2*l+w]+n);
    else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l) {
      assert(nr<10000);
      rules[nr++]={i,b*N+6*j+n,w*N};
    }
  }
  for(int iter=0;iter<500;iter++) {
    U cur=1,seen=0;
    while(cur) {
      seen|=cur;
      if(seen&halt)return false;
      cur=compose(cur,T)&~seen;
    }
    bool changed=false;
    for(int j=0;j<nr;j++) {
      auto [dst,src,off]=rules[j];
      U x=T[dst]|compose(T[src],T+off);
      if(x!=T[dst]){T[dst]=x;changed=true;}
    }
    if(!changed)return true;
  }
  return false;
}
static int encode(char w,char r,char q) {
  return (w-'0')*12+(r=='R')*6+(q-'A');
}
static Table parse(string s) {
  string t;
  for(char c:s)if(c!='_')t+=c;
  assert(t.size()==36);
  Table p;
  for(int i=0;i<12;i++)
    p[i]=t[3*i]=='-'?-1:encode(t[3*i],t[3*i+1],t[3*i+2]);
  return p;
}
static int digit(char c){return c>='a'?c-'a'+10:c-'0';}
static char outputDigit(int x){return x<10?'0'+x:'a'+x-10;}
int main(int argc,char**argv) {
  if(argc!=4) {
    cerr<<"usage: oneRD_mutant_bank BANK_CODES LASSO_TSV OUT_TSV\n";
    return 2;
  }
  vector<Entry> bank;
  {ifstream in(argv[1]);string code;
    while(in>>code) {
      assert(code[0]=='0'||code[0]=='1');
      Dfa dfa;
      for(size_t i=1;i<code.size();i++)dfa.push_back(digit(code[i]));
      int d=(int)dfa.size()/2;
      assert(d>0 && d<=20 && (int)dfa.size()==2*d && dfa[0]==0);
      for(int n:dfa)assert(0<=n&&n<d);
      bank.push_back({code[0]=='1',dfa});
    }
  }
  assert(bank.size()==169);
  ifstream in(argv[2]);ofstream out(argv[3]);
  string line;int roots=0,found=0;long long trials=0,mass=0;
  while(getline(in,line)) {
    size_t tab=line.find('\t');
    if(tab==string::npos || line.substr(tab+1)!=R"(["open"])")continue;
    string code=line.substr(0,tab);
    Table p=parse(code);
    roots++;
    bool okay=false;
    for(int i=0;i<(int)bank.size()&&!okay;i++) {
      auto &[rev,dfa]=bank[i];int d=(int)dfa.size()/2;
      for(int k=1;k<2*d&&!okay;k++) {
        int saved=dfa[k];
        for(int v=0;v<d;v++) {
          if(v==saved)continue;
          dfa[k]=v;trials++;
          if(far(p,dfa,rev)) {
            okay=true;found++;
            out<<code<<'\t'<<(rev?1:0)<<'\t'<<d<<'\t';
            for(int n:dfa)out<<outputDigit(n);
            out<<"\tsource=bank"<<i<<" edge="<<k<<" old="<<saved<<" new="<<v<<'\n';
            int holes=0;for(int x:p)if(x<0)holes++;
            long long weight=1;for(int j=0;j<holes;j++)weight*=25;
            mass+=weight;
            break;
          }
        }
        dfa[k]=saved;
      }
    }
  }
  cerr<<"roots="<<roots<<" found="<<found<<" mass="<<mass
      <<" trials="<<trials<<" bank="<<bank.size()<<'\n';
  if(roots!=628)return 3;
  return 0;
}
