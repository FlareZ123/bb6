#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <map>
#include <algorithm>
#include <unordered_map>
#include <cstdint>
using namespace std;
using Table=array<int,12>;
struct Res{int typ,n,s,e,k,dir,b;};
int encode(char w,char r,char q){return (w-'0')*12+(r=='R')*6+(q-'A');}
string decode(int a){if(a<0)return a==-1?"---":"HHH";return string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
Table parse(string str){str.erase(remove(str.begin(),str.end(),'_'),str.end());Table p;for(int i=0;i<12;i++)p[i]=str[3*i]=='-'?-1:encode(str[3*i],str[3*i+1],str[3*i+2]);return p;}
string show(const Table& p){string s;for(int i=0;i<12;i++){if(i&&i%2==0)s+='_';s+=decode(p[i]);}return s;}
int limit=200000;
Res classify(const Table& p){
 vector<uint8_t> tape(2*limit+3);int O=limit+1,h=O,q=0,lo=O,hi=O;
 // Exact normalized configurations on small support detect sound translated cycles.
 struct Seen{int n,h,lo,hi;};unordered_map<string,Seen> seen;
 for(int n=0;n<=limit;n++){
  int s=2*q+tape[h];if(p[s]<0)return {1,n,s,0,0,0,0};
  if(n<20000 && hi-lo<=128){
   string key;key.reserve(133);key.push_back(char(q));int rel=h-lo;
   for(int i=0;i<4;i++)key.push_back(char(uint32_t(rel)>>(8*i)));
   for(int x=lo;x<=hi;x++)key.push_back(char(tape[x]));
   auto [it,fresh]=seen.emplace(key,Seen{n,h,lo,hi});
   if(!fresh){auto a=it->second;int d=h-a.h; // Whole tape equality under translation. Choose a bound covering all visited cells.
     // A sufficiently wide anchor is safe for both sides, including any intermediate head positions.
     return {2,0,0,a.n,n-a.n,d>=0?1:0,d>=0?-n:n};
   }
  }
  if(n==limit)break;
  int a=p[s];tape[h]=a/12;
  if(tape[h]){lo=min(lo,h);hi=max(hi,h);}else{while(lo<hi&&!tape[lo])lo++;while(hi>lo&&!tape[hi])hi--;if(lo==hi&&!tape[lo])lo=hi=h;}
  h+=(a%12>=6?1:-1);q=a%6;
 }
 return {0,0,0,0,0,0,0};
}
int maxDelay(const Table& p,int state=0,int seen=1){int out=0;for(int q=0;q<6;q++)if(!(seen>>q&1)){int a=p[2*q];if(a==-1||(a>=0&&a/12==0&&a%6==state))out=max(out,1+maxDelay(p,q,seen|(1<<q)));}return out;}
map<string,long long> stats;long long maxscore=-1;string maxcode;int maxn,maxd;ofstream tree,op;
int support(const Table&p){int c=2;for(int i=0;i<12;i++)if(p[i]>=0)c=max(c,max(i/2,p[i]%6)+1);return c;}
void build(Table p){int holes=count(p.begin(),p.end(),-1);Res a=classify(p);
 if(a.typ==0){stats["open"]++;string s=show(p);op<<s<<'\n';tree<<"[\"open\",\""<<s<<"\"]";return;}
 if(a.typ==2){stats["cycle"]++;tree<<"[\"cycle\","<<a.e<<','<<a.k<<','<<(a.dir?"true":"false")<<','<<a.b<<']';return;}
 p[a.s]=-2;int d=maxDelay(p),score=a.n+1+d;if(score>maxscore){maxscore=score;maxcode=show(p);maxn=a.n;maxd=d;}
 if(holes==1){stats["last"]++;tree<<"[\"last\","<<a.n<<','<<a.s<<']';return;}
 stats["split"]++;tree<<"[\"split\","<<a.n<<','<<a.s<<",[";int cut=support(p);for(int i=0;i<24;i++){if(i)tree<<',';p[a.s]=i;if(i%6>cut)tree<<"[\"alias\"]";else build(p);}tree<<"]]";
}
int main(int argc,char**argv){if(argc<2)return 1;if(argc>2)limit=stoi(argv[2]);tree.open("tree.json");op.open("open.txt");build(parse(argv[1]));tree<<'\n';for(auto [s,n]:stats)cout<<s<<":"<<n<<' ';cout<<"\nmaxscore="<<maxscore<<" n="<<maxn<<" delay="<<maxd<<" table="<<maxcode<<endl;}
