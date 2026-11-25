// Deterministic first-hole audit generator: exact side-cycle comparison,
// shared known prefixes, and sound rejection filters. Untrusted discovery.
#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <map>
#include <algorithm>
#include <cstdint>
#include <cassert>
using namespace std;
constexpr int L=1000,W=2048,O=W/2;
using Tape=array<uint64_t,W/64>;using Table=array<int,12>;
struct Cfg{int q,h;Tape t;uint64_t left=0,right=0;};
struct Res{int typ,n,s,e,k,dir,b;};
uint64_t word(const Tape&t,int i){return i>=0&&i<W/64?t[i]:0;}
uint64_t window(const Tape&t,int x){int i=x/64,j=x%64;if(j<0){i--;j+=64;}return j?(word(t,i)>>j)|(word(t,i+1)<<(64-j)):word(t,i);}
int read(const Cfg&c){return (c.t[c.h/64]>>(c.h%64))&1;}
void move(Cfg&c,int a){uint64_t m=uint64_t(1)<<(c.h%64);auto &v=c.t[c.h/64];if(a/12)v|=m;else v&=~m;c.h+=a%12>=6?1:-1;c.q=a%6;}
void sig(Cfg&c){c.left=window(c.t,c.h-63);c.right=window(c.t,c.h);}
bool eqR(const Cfg&a,const Cfg&b,int low,int d){for(int i=low;i<W;i+=64)if(window(a.t,i)!=window(b.t,i+d))return false;return true;}
bool eqL(const Cfg&a,const Cfg&b,int high,int d){for(int i=high-63;i>=-63;i-=64)if(window(a.t,i)!=window(b.t,i+d))return false;return true;}
int encode(char w,char r,char q){return (w-'0')*12+(r=='R')*6+(q-'A');}
string decode(int a){if(a<0)return a==-1?"---":"HHH";return string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
Table parse(string str){str.erase(remove(str.begin(),str.end(),'_'),str.end());assert(str.size()==36);Table p;for(int i=0;i<12;i++)p[i]=str[3*i]=='-'?-1:encode(str[3*i],str[3*i+1],str[3*i+2]);return p;}
string show(const Table& p){string s;for(int i=0;i<12;i++){if(i&&i%2==0)s+='_';s+=decode(p[i]);}return s;}
vector<Cfg> tr;array<vector<int>,6> previous;
void restore(size_t k){while(tr.size()>k){int q=tr.back().q;assert(previous[q].back()==int(tr.size()-1));previous[q].pop_back();tr.pop_back();}}
Res classify(const Table& p,Cfg&c){
 for(int n=tr.size();n<=L;n++){
  int s=2*c.q+read(c);if(p[s]<0)return {1,n,s,0,0,0,0};
  sig(c);int low=c.h,high=c.h,i=n-1;
  for(auto it=previous[c.q].rbegin();it!=previous[c.q].rend();it++){
   int j=*it;if(n-j>256)break;while(i>=j){low=min(low,tr[i].h);high=max(high,tr[i].h);i--;}
   int d=c.h-tr[j].h;
   if(d>=0&&tr[j].right==c.right&&eqR(tr[j],c,low,d))return {2,0,0,j,n-j,1,low-O};
   if(d<=0&&tr[j].left==c.left&&eqL(tr[j],c,high,d))return {2,0,0,j,n-j,0,high-O};
  }
  tr.push_back(c);previous[c.q].push_back(n);move(c,p[s]);
 }
 return {0,0,0,0,0,0,0};
}
long long pow25(int k){long long r=1;while(k--)r*=25;return r;}
int maxDelay(const Table& p,int state=0,int seen=1){int out=0;for(int q=0;q<6;q++)if(!(seen>>q&1)){int a=p[2*q];if(a==-1||(a>=0&&a/12==0&&a%6==state))out=max(out,1+maxDelay(p,q,seen|(1<<q)));}return out;}
map<string,long long> stats,mass;long long maxscore=-1;string maxcode;int maxn,maxd;ofstream tree,op;
void build(Table p,Cfg c){size_t prefix=tr.size();int holes=count(p.begin(),p.end(),-1);Res a=classify(p,c);
 if(a.typ==0){stats["open"]++;mass["open"]+=pow25(holes);string s=show(p);op<<s<<'\n';tree<<"[\"open\",\""<<s<<"\"]";restore(prefix);return;}
 if(a.typ==2){stats["cycle"]++;mass["cycle"]+=pow25(holes);tree<<"[\"cycle\","<<a.e<<','<<a.k<<','<<(a.dir?"true":"false")<<','<<a.b<<']';restore(prefix);return;}
 p[a.s]=-2;int d=maxDelay(p),score=a.n+1+d;if(score>maxscore){maxscore=score;maxcode=show(p);maxn=a.n;maxd=d;}mass["halt"]+=pow25(holes-1);
 if(holes==1){stats["last"]++;mass["total"]+=24;tree<<"[\"last\","<<a.n<<','<<a.s<<']';restore(prefix);return;}
 stats["split"]++;tree<<"[\"split\","<<a.n<<','<<a.s<<",[";for(int i=0;i<24;i++){if(i)tree<<',';p[a.s]=i;build(p,c);}tree<<"]]";restore(prefix);
}
int main(int argc,char**argv){if(argc!=2)return 2;tr.reserve(L+1);tree.open("tree.json");op.open("open.txt");build(parse(argv[1]),Cfg{0,O,{}});tree<<'\n';assert(tr.empty());for(auto [s,n]:stats)cout<<s<<":"<<n<<' ';cout<<'\n';long long tot=0;for(auto [s,n]:mass){cout<<s<<":"<<n<<' ';tot+=n;}cout<<" total="<<tot<<"\nmaxscore="<<maxscore<<" n="<<maxn<<" delay="<<maxd<<" table="<<maxcode<<endl;}
