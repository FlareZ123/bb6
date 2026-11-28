// Second-order anchored FAR DFA exploration for surviving Raw54 E1=1RD
// one-hole cylinders. Untrusted discovery; all positive outputs must be
// rechecked as literal FAR.Data.fastValid witnesses in original-source Lean.
// Input: deduplicated prior certificate ledger (385 rows), residual open TSV.
// Only seeds with the same unknown transition slot are compared.
#define main raw54_first_round_unused_main
#include "oneRD_mutant_bank.cpp"
#undef main
#include <set>
#include <algorithm>
#include <chrono>
#include <utility>
#include <sstream>
#include <tuple>

struct Seed2 {bool rev; Dfa dfa; Table table; string code;};

int main(int argc,char**argv) {
  if(argc!=4){cerr<<"usage: two_edge MASTER385 REMAIN242 OUTPUT\n";return 2;}
  vector<Seed2> pool;string line;
  {ifstream in(argv[1]);
   while(getline(in,line)){
    istringstream f(line);vector<string> a;string s;
    while(getline(f,s,'\t'))a.push_back(s);
    if(a.size()<4)continue;
    Seed2 p;p.rev=a[1]=="1";p.table=parse(a[0]);p.code=a[0];
    for(char c:a[3])p.dfa.push_back(digit(c));
    assert(p.dfa[0]==0);pool.push_back(move(p));
   }}
  cerr<<"seed="<<pool.size()<<'\n';
  ifstream in(argv[2]);ofstream out(argv[3]);
  int n=0,found=0;long long attempts=0;
  auto t0=chrono::steady_clock::now();
  while(getline(in,line)){
    size_t ix=line.find('\t');
    if(ix==string::npos)continue;
    string code=line.substr(0,ix);Table p=parse(code);
    int hole=-1;for(int j=0;j<12;j++)if(p[j]<0)hole=j;
    vector<tuple<int,int,int>> choices;
    for(int i=0;i<(int)pool.size();i++){
      auto &sp=pool[i];if(sp.table[hole]>=0)continue;
      int dist=0;for(int j=0;j<12;j++)dist+=(sp.table[j]!=p[j]);
      choices.emplace_back(dist,(int)sp.dfa.size()/2,i);
    }
    sort(choices.begin(),choices.end());
    set<string> seen;bool ok=false;long long per=0;int cand=0;
    int minDist=get<0>(choices[0]);
    for(auto [dist,dim,idx]:choices) {
      if(ok || dist>minDist+1 || cand++>=16 || per>90000)break;
      auto &seed=pool[idx];Dfa &dfa=seed.dfa;int d=(int)dfa.size()/2;
      string key=string(seed.rev?"1":"0")+":";
      for(int v:dfa)key+=outputDigit(v);
      if(!seen.insert(key).second)continue;
      for(int k=1;k<2*d && !ok && per<90000;k++){
        int old=dfa[k];
        for(int v=0;v<d && !ok && per<90000;v++){
          if(v==old)continue;dfa[k]=v;
          for(int j=k+1;j<2*d && !ok && per<90000;j++){
            int old2=dfa[j];
            for(int w=0;w<d && per<90000;w++){
              if(w==old2)continue;
              dfa[j]=w;per++;attempts++;
              if(far(p,dfa,seed.rev)){
                ok=true;found++;
                out<<code<<'\t'<<(seed.rev?1:0)<<'\t'<<d<<'\t';
                for(int u:dfa)out<<outputDigit(u);
                out<<"\tseed="<<idx<<" hamming="<<dist<<" edge1="<<k<<" edge2="<<j<<'\n';
                break;
              }
            }
            dfa[j]=old2;
          }
        }
        dfa[k]=old;
      }
    }
    n++;
    if(n%10==0)cerr<<"n="<<n<<" found="<<found<<" trials="<<attempts
      <<" elapsed="<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<'\n';
  }
  cerr<<"TOTAL n="<<n<<" found="<<found<<" trials="<<attempts
    <<" elapsed="<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<'\n';
}
