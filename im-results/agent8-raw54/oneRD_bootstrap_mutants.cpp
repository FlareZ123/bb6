// Iterated FAR DFA one-edge mutations: bootstrap from previously source-verifiable
// DFA witnesses.  Discovery only; FAR.Data.fastValid must replay in Lean.
#define main raw54_first_round_unused_main
#include "oneRD_mutant_bank.cpp"
#undef main
#include <set>
#include <sstream>

int main(int argc,char**argv) {
  if(argc!=4) {
    cerr<<"usage: oneRD_bootstrap_mutants OPEN_TSV PRIOR_TSV OUT_TSV\n";return 2;
  }
  struct Seed {bool rev;Dfa dfa;string origin;};
  vector<Seed> bank;
  set<string> uniqueDfa,solved;
  {ifstream in(argv[2]);string line;
   while(getline(in,line)) {
    istringstream f(line);string code,dir,dim,raw;
    if(!getline(f,code,'\t')||!getline(f,dir,'\t')||
       !getline(f,dim,'\t')||!getline(f,raw,'\t'))continue;
    solved.insert(code);
    const string key=dir+":"+raw;
    if(!uniqueDfa.insert(key).second)continue;
    Dfa dfa;
    for(char c:raw)dfa.push_back(digit(c));
    const int d=(int)dfa.size()/2;
    assert(0<d && d<=20 && (int)dfa.size()==2*d && dfa[0]==0);
    for(int x:dfa)assert(x>=0 && x<d);
    bank.push_back({dir=="1",dfa,key});
   }}
  cerr<<"seed-dfas="<<bank.size()<<" solved="<<solved.size()<<'\n';
  ifstream in(argv[1]);ofstream out(argv[3]);
  int unresolved=0,found=0;
  long long attempts=0,mass=0;
  string line;
  while(getline(in,line)) {
    auto tab=line.find('\t');
    if(tab==string::npos||line.substr(tab+1)!=R"(["open"])")continue;
    const string code=line.substr(0,tab);
    if(solved.count(code))continue;
    unresolved++;
    Table p=parse(code);bool foundCurrent=false;
    for(auto &e:bank) {
      if(foundCurrent)break;
      Dfa &dfa=e.dfa;
      int d=(int)dfa.size()/2;
      for(int k=1;k<2*d && !foundCurrent;k++) {
        int old=dfa[k];
        for(int v=0;v<d;v++) {
          if(v==old)continue;
          dfa[k]=v;attempts++;
          if(far(p,dfa,e.rev)) {
            foundCurrent=true;found++;
            out<<code<<'\t'<<(e.rev?1:0)<<'\t'<<d<<'\t';
            for(int x:dfa)out<<outputDigit(x);
            out<<"\tsource="<<e.origin<<" edge="<<k<<" old="<<old<<" new="<<v<<'\n';
            int holes=0;for(int x:p)holes+=(x<0);
            long long weight=1;while(holes--)weight*=25;
            mass+=weight;
            break;
          }
        }
        dfa[k]=old;
      }
    }
  }
  cerr<<"TOTAL unsolved="<<unresolved<<" found="<<found<<" mass="<<mass
      <<" attempts="<<attempts<<" seed="<<bank.size()<<'\n';
}
