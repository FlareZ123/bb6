// Exact candidate discovery. Hashes select candidates; direct versioned tape
// comparison checks translated side witnesses. Final Lean audit is separate.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using U=uint64_t;
constexpr U P=0x9e3779b97f4a7c15ULL;
using Table=array<int,12>;
struct Cell{vector<pair<int,bool>> v;bool get(int t) const {auto i=upper_bound(v.begin(),v.end(),pair<int,bool>{t,true});return i==v.begin()?false:prev(i)->second;}bool now()const{return !v.empty()&&v.back().second;}};
struct Tape{vector<Cell> p,m;Cell& cell(int x){auto &v=x>=0?p:m;size_t i=x>=0?x:-x-1;if(i>=v.size())v.resize(i+1);return v[i];}const Cell* at(int x)const{const auto &v=x>=0?p:m;size_t i=x>=0?x:-x-1;return i<v.size()?&v[i]:nullptr;}bool now(int x)const{auto c=at(x);return c&&c->now();}bool get(int x,int t)const{auto c=at(x);return c&&c->get(t);}void write(int x,int t,bool b){if(now(x)!=b)cell(x).v.emplace_back(t,b);}};
struct Key{U hash;int q;bool operator==(const Key&)const=default;};struct Hash{size_t operator()(const Key&k)const{return k.hash^(U(k.q)*P);}};
struct Frame{int h,pl,pr;};
struct Result{int type,n,s,entry,period,dir,boundary;};
int cap=10000,lookback=128;
Result classify(const Table&p){
 Tape t; vector<Frame> tr;unordered_map<Key,int,Hash> left,right;int q=0,h=0,lo=0,hi=0;U lh=0,rh=0,pinv=1;for(int k=0;k<6;k++)pinv*=2-P*pinv;
 for(int n=0;n<=cap;n++){
  int a=t.now(h),s=2*q+a,m=p[s];if(m<0)return {1,n,s};
  auto getLast=[](auto &mp,Key k){auto it=mp.find(k);return it==mp.end()?-1:it->second;};
  Key kl{lh,q},kr{rh,s};int pl=getLast(left,kl),pr=getLast(right,kr);
  for(int dir:{1,0}){int j=dir?pr:pl,ext=h,k=n-1;
   for(int tried=0;j>=0&&tried<lookback;tried++,j=dir?tr[j].pr:tr[j].pl){
    int d=h-tr[j].h;if((dir&&d<0)||(!dir&&d>0))continue;
    while(k>=j){ext=dir?min(ext,tr[k].h):max(ext,tr[k].h);--k;}
    bool ok=true;
    if(dir){for(int x=ext;x<=hi;x++)if(t.get(x,j)!=t.now(x+d)){ok=false;break;}}
    else {for(int x=ext;x>=lo;x--)if(t.get(x,j)!=t.now(x+d)){ok=false;break;}}
    if(ok)return {2,0,0,j,n-j,dir,ext};
   }
  }
  tr.push_back({h,pl,pr});left[kl]=n;right[kr]=n;
  int w=m/12;bool r=m%12>=6;q=m%6;
  t.write(h,n+1,w);
  if(r){int b=t.now(h+1);lh=b+P*(w+lh-a);rh=(rh-b)*pinv;++h;}
  else{lh=(lh-a)*pinv;rh=w+P*rh;--h;}
  lo=min(lo,h);hi=max(hi,h);
 }
 return {0};
}
string decode(int a){if(a<0)return a==-1?"---":"HHH";return string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
string show(const Table&p){string s;for(int i=0;i<12;i++){if(i&&i%2==0)s+='_';s+=decode(p[i]);}return s;}
Table parse(string s){s.erase(remove(s.begin(),s.end(),'_'),s.end());assert(s.size()==36);Table p;for(int i=0;i<12;i++){char a=s[3*i],d=s[3*i+1],q=s[3*i+2];assert(a=='-'||(a=='0'||a=='1'));p[i]=a=='-'?-1:(a-'0')*12+(d=='R')*6+(q-'A');}return p;}
long long pow25(int k){long long v=1;while(k--)v*=25;return v;}
long long mass[3]={},counts[4]={};int maxQuery=0,maxCycle=0;ofstream tree,opens;
void build(Table p){int holes=count(p.begin(),p.end(),-1);auto a=classify(p);
 if(a.type==0){++counts[0];mass[0]+=pow25(holes);opens<<show(p)<<'\n';tree<<"[\"open\",\""<<show(p)<<"\"]";return;}
 if(a.type==2){++counts[1];mass[1]+=pow25(holes);maxCycle=max(maxCycle,a.entry+a.period);tree<<"[\"cycle\","<<a.entry<<','<<a.period<<','<<a.dir<<','<<a.boundary<<']';return;}
 maxQuery=max(maxQuery,a.n);mass[2]+=pow25(holes-1);
 if(holes==1){++counts[2];mass[2]+=24;tree<<"[\"last\","<<a.n<<','<<a.s<<']';return;}
 ++counts[3];tree<<"[\"split\","<<a.n<<','<<a.s<<",[";for(int i=0;i<24;i++){if(i)tree<<',';p[a.s]=i;build(p);}tree<<"]]";
}
int main(int argc,char**argv){if(argc!=5){cerr<<"Usage: fast_partition TABLE CAP LOOKBACK PREFIX\n";return 1;}cap=stoi(argv[2]);lookback=stoi(argv[3]);auto p=parse(argv[1]);tree.open(string(argv[4])+".json");opens.open(string(argv[4])+".open");build(p);tree<<'\n';long long total=mass[0]+mass[1]+mass[2];assert(total==pow25(count(p.begin(),p.end(),-1)));cout<<"open="<<counts[0]<<" cycle="<<counts[1]<<" last="<<counts[2]<<" split="<<counts[3]<<" open_mass="<<mass[0]<<" cycle_mass="<<mass[1]<<" bounded_mass="<<mass[2]<<" total="<<total<<" max_query="<<maxQuery<<" max_cycle_end="<<maxCycle<<endl;}
