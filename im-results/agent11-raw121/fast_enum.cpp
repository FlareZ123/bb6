// Candidate generation only; all leaves are checked by Lean.
#include <array>
#include <bitset>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <map>
#include <algorithm>
#include <cstdint>
using namespace std;
constexpr int L=1000,W=2048,O=W/2;
using Tape=bitset<W>;using Table=array<int,12>;
using U=uint64_t;
constexpr U BASE=0x9e3779b97f4a7c15ULL;
constexpr U inv(U a){U x=1;for(int i=0;i<6;i++)x*=2-a*x;return x;}
constexpr U INV=inv(BASE);
static_assert(BASE*INV==1);
// Head-relative polynomial fingerprints only reject impossible matches;
// the exact tape comparison remains authoritative.
struct Cfg{int q,h;Tape t;U l=0,r=0;};
struct Res{int typ,n,s,e,k,dir,b;};
array<Tape,W> above,below;
int encode(char w,char r,char q){return (w-'0')*12+(r=='R')*6+(q-'A');}
string decode(int a){if(a<0)return a==-1?"---":"HHH";return string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
Table parse(string str){str.erase(remove(str.begin(),str.end(),'_'),str.end());Table p;for(int i=0;i<12;i++)p[i]=str[3*i]=='-'?-1:encode(str[3*i],str[3*i+1],str[3*i+2]);return p;}
string show(const Table& p){string s;for(int i=0;i<12;i++){if(i&&i%2==0)s+='_';s+=decode(p[i]);}return s;}
Res classify(const Table& p){
 Cfg c{0,O,{}}; vector<Cfg> tr;tr.reserve(L+1);array<vector<int>,6> prev;
 for(int n=0;n<=L;n++){
  int s=2*c.q+c.t[c.h];if(p[s]<0)return {1,n,s,0,0,0,0};
  int low=c.h,high=c.h,i=n-1;
  for(auto it=prev[c.q].rbegin();it!=prev[c.q].rend();it++){
   int j=*it;if(n-j>256)break;
   int d=c.h-tr[j].h;
   bool right=d>=0 && tr[j].r==c.r, left=d<=0 && tr[j].l==c.l;
   if(!right && !left)continue;
   while(i>=j){low=min(low,tr[i].h);high=max(high,tr[i].h);i--;}
   if(right && ((tr[j].t^(c.t>>d))&above[low]).none())return {2,0,0,j,n-j,1,low-O};
   if(left && ((tr[j].t^(c.t<<(-d)))&below[high]).none())return {2,0,0,j,n-j,0,high-O};
  }
  tr.push_back(c);prev[c.q].push_back(n);int a=p[s],w=a/12,old=c.t[c.h];c.l+=U(w)-U(old);c.r+=U(w)-U(old);c.t[c.h]=w;
  if(a%12>=6){c.h++;c.r=(c.r-U(w))*INV;c.l=U(c.t[c.h])+BASE*c.l;}else{c.h--;c.l=(c.l-U(w))*INV;c.r=U(c.t[c.h])+BASE*c.r;}c.q=a%6;
 }
 return {0,0,0,0,0,0,0};
}
long long pow25(int k){long long r=1;while(k--)r*=25;return r;}
int maxDelay(const Table& p,int state=0,int seen=1){int out=0;for(int q=0;q<6;q++)if(!(seen>>q&1)){int a=p[2*q];if(a==-1||(a>=0&&a/12==0&&a%6==state))out=max(out,1+maxDelay(p,q,seen|(1<<q)));}return out;}
map<string,long long> stats,mass;long long maxscore=-1;string maxcode;int maxn,maxd;ofstream tree,op;
void build(Table p){int holes=std::count(p.begin(),p.end(),-1);Res a=classify(p);
 if(a.typ==0){stats["open"]++;mass["open"]+=pow25(holes);string s=show(p);op<<s<<'\n';tree<<"[\"open\",\""<<s<<"\"]";return;}
 if(a.typ==2){stats["cycle"]++;mass["cycle"]+=pow25(holes);tree<<"[\"cycle\","<<a.e<<','<<a.k<<','<<(a.dir?"true":"false")<<','<<a.b<<']';return;}
 p[a.s]=-2;int d=maxDelay(p),score=a.n+1+d;if(score>maxscore){maxscore=score;maxcode=show(p);maxn=a.n;maxd=d;}mass["halt"]+=pow25(holes-1);
 if(holes==1){stats["last"]++;mass["total"]+=24;tree<<"[\"last\","<<a.n<<','<<a.s<<']';return;}
 stats["split"]++;tree<<"[\"split\","<<a.n<<','<<a.s<<",[";for(int i=0;i<24;i++){if(i)tree<<',';p[a.s]=i;build(p);}tree<<"]]";
}
int main(int argc,char**argv){for(int i=0;i<W;i++){if(i)below[i]=below[i-1];below[i].set(i);}for(int i=W-1;i>=0;i--){if(i<W-1)above[i]=above[i+1];above[i].set(i);}string p=argc>1?argv[1]:"1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RE";tree.open("tree.json");op.open("open.txt");build(parse(p));tree<<'\n';for(auto [s,n]:stats)cout<<s<<":"<<n<<' ';cout<<'\n';long long tot=0;for(auto [s,n]:mass){cout<<s<<":"<<n<<' ';tot+=n;}cout<<" total="<<tot<<"\nmaxscore="<<maxscore<<" n="<<maxn<<" delay="<<maxd<<" table="<<maxcode<<endl;}
