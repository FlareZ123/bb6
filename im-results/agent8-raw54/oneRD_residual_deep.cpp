// Deep residual-only Raw54 E1=1RD discovery.
// Untrusted discovery: emitted FAR/last/split candidates must be replayed by Lean.
// Reads the 671 source-generated open partial tables and re-applies the exact
// FAR bank, then simulates first-unknown queries from blank to bound B.
#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <unordered_set>
#include <map>
#include <algorithm>
#include <cstdint>
#include <cassert>
#include <sstream>
using namespace std;

using Table=array<int,12>;
using D=vector<int>;
using U=unsigned __int128;
struct Rule {int dst,src,off;};
struct Hit {bool found; int n,s;};

U compose(U mask,const U* rows){
  U v=0;
  while(mask){
    uint64_t lo=(uint64_t)mask;
    int j=lo?__builtin_ctzll(lo):64+__builtin_ctzll((uint64_t)(mask>>64));
    v|=rows[j]; mask&=mask-1;
  }
  return v;
}
bool far(const Table& m,const D& dfa,bool rev){
  int d=int(dfa.size()/2),N=6*d+1,H=N-1;
  U T[254]{}; Rule rules[504]; int nr=0; U halt=U(1)<<H;
  T[H]=T[N+H]=halt;
  for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
    int v=m[2*q+a],x=v<0?-1:4*(v%6)+2*(v/12)+((v%12)>=6),i=a*N+6*l+q;
    if(x<0){T[i]=halt;continue;}
    int w=(x>>1)&1,n=x/4;
    if(bool(x&1)!=rev) T[i]=U(1)<<(6*dfa[2*l+w]+n);
    else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l)
      rules[nr++]={i,b*N+6*j+n,w*N};
  }
  for(;;){
    U cur=1,seen=0;
    while(cur){seen|=cur;if(seen&halt)return false;cur=compose(cur,T)&~seen;}
    bool changed=false;
    for(int j=0;j<nr;j++){
      auto [dst,src,off]=rules[j];
      U x=T[dst]|compose(T[src],T+off);
      if(x!=T[dst]){T[dst]=x;changed=true;}
    }
    if(!changed)return true;
  }
}

int encode(char w,char r,char q){return (w-'0')*12+(r=='R')*6+(q-'A');}
string decode(int a){if(a<0)return a==-1?"---":"HHH";return string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
Table parse(string str){
  str.erase(remove(str.begin(),str.end(),'_'),str.end());
  assert(str.size()==36); Table p;
  for(int i=0;i<12;i++) p[i]=str[3*i]=='-'?-1:encode(str[3*i],str[3*i+1],str[3*i+2]);
  return p;
}
string show(const Table& p){
  string s;
  for(int i=0;i<12;i++){if(i&&i%2==0)s+="_";s+=decode(p[i]);}
  return s;
}
long long pow25(int k){long long r=1;while(k--)r*=25;return r;}

int maxDelay(const Table& p,int state=0,int seen=1){
  int out=0;
  for(int q=0;q<6;q++) if(!(seen>>q&1)){
    int a=p[2*q];
    if(a==-1||(a>=0&&a/12==0&&a%6==state))
      out=max(out,1+maxDelay(p,q,seen|(1<<q)));
  }
  return out;
}

Hit firstUnknown(const Table& p,int B){
  int q=0; long long h=0;
  unordered_set<long long> ones;
  ones.reserve(4096);
  for(int n=0;n<=B;n++){
    int a=ones.count(h)?1:0;
    int s=2*q+a, v=p[s];
    if(v==-1) return {true,n,s};
    if(v==-2) return {false,n,s}; // not expected for residual inputs
    if(v/12) ones.insert(h); else ones.erase(h);
    h += (v%12>=6)?1:-1;
    q=v%6;
  }
  return {false,B+1,-1};
}

vector<pair<D,bool>> bank;
int BOUND=39447;
map<string,long long> nodes;
long long initialMass=0,residualMass=0;
int maxScore=-1,maxHit=-1;
string maxScoreCode,maxHitCode;
vector<pair<int,string>> lateOrOpen;

string solve(Table p){
  int holes=count(p.begin(),p.end(),-1);
  for(size_t i=0;i<bank.size();i++){
    if(far(p,bank[i].first,bank[i].second)){
      nodes["far"]++;
      return string("[\"far\",")+to_string(i)+"]";
    }
  }
  Hit h=firstUnknown(p,BOUND);
  if(!h.found){
    nodes["open"]++; residualMass+=pow25(holes);
    lateOrOpen.push_back({h.n,show(p)});
    return string("[\"open\",\"")+show(p)+"\"]";
  }
  maxHit=max(maxHit,h.n);
  if(h.n==maxHit) maxHitCode=show(p);
  Table ph=p; ph[h.s]=-2;
  int d=maxDelay(ph), score=h.n+1+d;
  if(score>maxScore){maxScore=score;maxScoreCode=show(ph);}
  if(score>BOUND){
    nodes["late"]++; residualMass+=pow25(holes);
    lateOrOpen.push_back({score,show(p)});
    return string("[\"open\",\"")+show(p)+"\"]";
  }
  if(holes==1){
    nodes["last"]++;
    return string("[\"last\",")+to_string(h.n)+","+to_string(h.s)+"]";
  }
  nodes["split"]++;
  ostringstream o; o<<"[\"split\","<<h.n<<","<<h.s<<",[";
  for(int i=0;i<24;i++){
    if(i)o<<",";
    Table c=p;c[h.s]=i;o<<solve(c);
  }
  o<<"]]";
  return o.str();
}

int main(int argc,char**argv){
  if(argc!=5){
    cerr<<"usage: oneRD_residual_deep BANK OPEN OUT BOUND\n";return 2;
  }
  BOUND=stoi(argv[4]);
  {ifstream in(argv[1]);string s;while(in>>s){
    D d;for(int i=1;i<(int)s.size();i++){char c=s[i];d.push_back(c>='a'?c-'a'+10:c-'0');}
    bank.push_back({d,s[0]=='1'});
  }}
  assert(bank.size()==169);
  ifstream in(argv[2]); ofstream out(argv[3]);
  string code; int roots=0;
  while(in>>code){
    Table p=parse(code);
    int holes=count(p.begin(),p.end(),-1);
    initialMass+=pow25(holes); roots++;
    out<<code<<"\t"<<solve(p)<<"\n";
  }
  assert(roots==671);
  cout<<"roots="<<roots<<" bank="<<bank.size()<<" bound="<<BOUND
      <<" initial_mass="<<initialMass<<" residual_mass="<<residualMass<<"\n";
  for(auto [k,v]:nodes)cout<<k<<":"<<v<<" ";
  cout<<"\nmax_hit="<<maxHit<<" code="<<maxHitCode
      <<"\nmax_score="<<maxScore<<" code="<<maxScoreCode<<"\n";
  sort(lateOrOpen.begin(),lateOrOpen.end(),greater<>());
  cout<<"residual_roots="<<lateOrOpen.size()<<"\n";
  for(size_t i=0;i<min<size_t>(lateOrOpen.size(),30);i++)
    cout<<"residual "<<lateOrOpen[i].first<<" "<<lateOrOpen[i].second<<"\n";
}
