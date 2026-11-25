// Candidate-only generator: reuse the existing raw99 bounded classifier.
// An unresolved classification is always retained, never pronounced safe.
#define main raw99_main
#include "../agent2-tnf-raw99/enumerate.cpp"
#undef main
#include <set>
const set<string> chosen={
 "1RB---_1RC1LC_0RD---_1LD1RE_0LB0LD_------",
 "1RB---_1RC---_0RD---_1LD1RE_0RF0LD_---0RD",
 "1RB---_1RC1LC_0RD---_1LD1RE_1LB0LD_------",
 "1RB---_1RC---_0RD---_1LD1RE_1LF0LD_---0RF"
};
map<string,long long> cutstats;
long long unresolvedMass=0;
int cutMaxScore=0;
set<string> checked;
void emitCut(Table p,int depth){
 int holes=count(p.begin(),p.end(),-1);
 if(chosen.count(show(p))){
  if(!checked.insert(show(p)).second)throw runtime_error("duplicate selected cylinder");
  cutstats["complete"]++;
  tree<<"[\"closed\",";build(p);tree<<']';
  return;
 }
 Res a=classify(p);
 if(a.typ==2){
  cutstats["cycle"]++;
  tree<<"[\"closed\",[\"cycle\","<<a.e<<','<<a.k<<','<<(a.dir?"true":"false")<<','<<a.b<<"]]";
  return;
 }
 if(a.typ!=1||depth==0){
  cutstats["unresolved"]++;unresolvedMass+=pow25(holes);
  tree<<"[\"unresolved\"]";return;
 }
 p[a.s]=-2;
 cutMaxScore=max(cutMaxScore,a.n+1+maxDelay(p));
 cutstats["split"]++;
 tree<<"[\"split\","<<a.n<<','<<a.s<<",[";
 for(int i=0;i<24;i++){if(i)tree<<',';p[a.s]=i;emitCut(p,depth-1);}
 tree<<"]]";
}
int main(){
 for(int i=0;i<W;i++){if(i)below[i]=below[i-1];below[i].set(i);}
 for(int i=W-1;i>=0;i--){if(i<W-1)above[i]=above[i+1];above[i].set(i);}
 tree.open("cut.json");op.open("unexpected-open.txt");
 emitCut(parse("1RB---_1RC---_0RD---_1LD1RE_---0LD_------"),2);
 tree<<'\n';
 if(checked!=chosen||stats["open"]!=0)throw runtime_error("selected certificate incomplete");
 for(auto [s,n]:cutstats)cout<<s<<":"<<n<<" ";
 cout<<"unresolvedMass="<<unresolvedMass<<" total="<<pow25(6)<<" splitBound="<<cutMaxScore<<" completeBound="<<maxscore<<"\n";
 for(auto [s,n]:stats)cout<<s<<":"<<n<<" ";
 cout<<"\n";
}
