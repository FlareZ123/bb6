// Exact run-compressed F421 principal two-return map.
// C++20, no dependencies. Each pair run costs O(1) because all repeated
// same-symbol transitions reach fixed points; no tape-length expansion.
#include <array>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <tuple>
#include <limits>
using namespace std;
using U=uint64_t; using Big=unsigned __int128;
// Symbol numbers are the natural binary codes: Z=0, Q=1, P=2, R=3.
struct Run {int p; U n;};
using Word=vector<Run>;
void push(Word& w,int p,U n=1){if(!n)return;if(!w.empty()&&w.back().p==p)w.back().n+=n;else w.push_back({p,n});}
string bits(int p){return string{char('0'+(p>>1)),char('0'+(p&1))};}
string decimal(Big n){string s;do{s+=char('0'+n%10);n/=10;}while(n);reverse(s.begin(),s.end());return s;}
string expand(const Word& w){string s;for(auto [p,n]:w)for(U i=0;i<n;++i)s+=bits(p);while(!s.empty()&&s.back()=='0')s.pop_back();return s;}
Word pack(string s){Word w;if(s.size()%2)s+='0';for(size_t i=0;i<s.size();i+=2)push(w,2*(s[i]-'0')+s[i+1]-'0');if(!w.empty()&&w.back().p==0)w.pop_back();return w;}
// Parser states represent the proper prefix of a continuing/terminal block.
const array<string,5> prefix={"","01","11","1","0"};
int pstate(const string&s){for(int i=0;i<5;++i)if(prefix[i]==s)return i;return -1;}
string replacement(const string&s){if(s=="10")return "01";if(s=="110")return "011";if(s=="010")return "101";return "";}
struct ScanEdge{int dst,kind,used;}; // kind: 0 continuing, 1 d, 2 e, 3 bad
array<array<ScanEdge,4>,5> scan_table(){array<array<ScanEdge,4>,5> tab{};for(int i=0;i<5;++i)for(int p=0;p<4;++p){string s=prefix[i];int n=0;bool stop=false;for(char b:bits(p)){++n;s+=b;if(s=="00"||s=="011"||s=="111"){tab[i][p]={-1,s=="00"?1:s=="011"?2:3,n};stop=true;break;}if(!replacement(s).empty())s="";}if(!stop){assert(pstate(s)>=0);tab[i][p]={pstate(s),0,2};}}return tab;}
const auto SCAN=scan_table();
struct Scan {U L;int kind;};
Scan scan(const Word&w){U n=0;int s=0;for(size_t i=0;i<=w.size();++i){Run r=i<w.size()?w[i]:Run{0,3};while(r.n){auto e=SCAN[s][r.p];if(e.kind)return {n+U(e.used),e.kind};if(e.dst==s){n+=2*r.n;break;}s=e.dst;n+=2;--r.n;}}assert(false);return {};}
// Transducer state: left parser prefix, pending single X bit, delayed X pair.
struct State {string p,b,last;bool operator<(const State&o)const{return tie(p,b,last)<tie(o.p,o.b,o.last);}};
struct Edge{int dst;string out;}; // -1 infeasible parity or bad, -2 copied suffix
string fpair(const string&s){assert(s=="10"||s=="01"||s=="11");return s=="11"?"00":s;}
// For a fixed parity, X begins with one pending bit for even L; for odd L
// the leading 1 is discarded. The last full X pair is delayed until the
// terminal, when it is replaced by Q for d or P for e.
vector<array<Edge,4>> build(bool odd){vector<State> ss{{"",odd?"":"1",""}};map<State,int> idx{{ss[0],0}};vector<array<Edge,4>> result;
 for(size_t i=0;i<ss.size();++i){array<Edge,4> row;for(int p=0;p<4;++p){State s=ss[i];string out;int dst=0;auto feed=[&](const string&x){for(char c:x){if(s.b.empty())s.b=c;else{if(!s.last.empty())out+=fpair(s.last);s.last=s.b+c;s.b="";}}};
  auto bb=bits(p);bool terminal=false;for(int j=0;j<2;++j){s.p+=bb[j];if(s.p=="111"){dst=-1;terminal=true;break;}auto r=replacement(s.p);if(!r.empty()){feed(r);s.p="";continue;}if(s.p=="00"||s.p=="011"){bool d=s.p=="00";feed(d?"1":"10");if(!s.b.empty()){dst=-1;terminal=true;break;}assert(s.last==(d?"11":"10"));out+=d?"01":"10";if(j==0)out+=bb[1];dst=-2;terminal=true;break;}assert(pstate(s.p)>=0);}
  if(!terminal){auto [it,fresh]=idx.emplace(s,int(ss.size()));if(fresh)ss.push_back(s);dst=it->second;}
  row[p]={dst,out};}result.push_back(row);}return result;}
const array<vector<array<Edge,4>>,2> TRANS={build(false),build(true)};
struct Output {
 Word w;int pending=-1;bool replaced=false;U leadingP=0;U qcount=0;
 void pair(int p,U n=1,bool count=true){if(!n)return;if(count&&p==1)qcount+=n;
  if(!replaced){if(p==2){leadingP+=n;push(w,p,n);return;}assert(p==0);push(w,2);push(w,1);replaced=true;--n;}push(w,p,n);}
 void bit(int b,bool count=true){if(pending<0)pending=b;else{pair(2*pending+b,1,count);pending=-1;}}
 void stream(const string&s){for(char b:s)bit(b-'0');}
 void repeat(const string&s,U n){if(s.empty()||!n)return;assert(s.size()==2&&pending<0);pair(2*(s[0]-'0')+s[1]-'0',n);}
 void tail(int p,U n){if(!n)return;if(pending<0){pair(p,n,false);return;}pair(2*pending+(p>>1),1,false);if(n>1)pair(2*(p&1)+(p>>1),n-1,false);pending=p&1;}
};
struct Result {bool bad; U firstL; int kind; U firstQ; U secondL; Big steps; U dx;};
Result advance(Word& w){auto r=scan(w);if(r.kind==3)return {true,r.L,r.kind,0,0,Big(r.L-1),0};bool odd=r.L%2;
 assert(w.size()>=2&&w[0].p==2&&w[1].p==1);Output o;o.pair(odd?0:2);int s=0;bool done=false;
 for(size_t i=0;i<=w.size();++i){Run rr=i<w.size()?w[i]:Run{0,3};if(done){o.tail(rr.p,rr.n);continue;}
  while(rr.n){auto&e=TRANS[odd][s][rr.p];assert(e.dst!=-1);if(e.dst==s){o.repeat(e.out,rr.n);break;}o.stream(e.out);--rr.n;if(e.dst==-2){done=true;o.tail(rr.p,rr.n);break;}s=e.dst;}
 }
 assert(done&&o.replaced);if(o.pending>=0)o.bit(0,false);if(!o.w.empty()&&o.w.back().p==0)o.w.pop_back();assert(o.w.size()>=2&&o.w[0].p==2&&o.w[1].p==1);
 U b=o.qcount-(r.kind==1);U L2=2*(o.leadingP+1);Big cost=Big(r.L)+2*(r.L/2)+4*Big(b)+2+2*Big(L2)+2;w.swap(o.w);return {false,r.L,r.kind,b,L2,cost,odd?3u:4u};
}
int main(int argc,char**argv){if(argc>1&&string(argv[1])=="--one"){string s;while(cin>>s){auto w=pack(s);auto r=advance(w);if(r.bad)cout<<"BAD "<<r.firstL<<" "<<decimal(r.steps)<<"\n";else cout<<expand(w)<<" "<<r.firstL<<" "<<r.kind<<" "<<r.firstQ<<" "<<r.secondL<<" "<<decimal(r.steps)<<" "<<r.dx<<"\n";}return 0;}
 U N=argc>1?stoull(argv[1]):1000000;bool verbose=argc>2&&string(argv[2])=="--verbose";bool oddlog=argc>2&&string(argv[2])=="--odd";Word w=pack("10010101");Big time=24;U head=4,odd=0,maxruns=0;for(U i=0;i<N;++i){auto r=advance(w);time+=r.steps;head+=r.dx;if(r.bad){cout<<"F1 after macro "<<i<<" at primitive step "<<decimal(time)<<"\n";return 2;}maxruns=max(maxruns,U(w.size()));if(r.firstL%2){++odd;if(oddlog)cout<<i<<" "<<head<<" "<<r.firstL<<" "<<r.kind<<" "<<w.size()<<"\n";}if(verbose)cout<<i+1<<" "<<decimal(time)<<" "<<head<<" "<<expand(w)<<"\n";if(!verbose&&!oddlog&&(i+1)%10000000==0)cerr<<i+1<<" macros; steps="<<decimal(time)<<"; runs="<<w.size()<<"; odd="<<odd<<"\n";}
 cout<<"macros="<<N<<" steps="<<decimal(time)<<" head="<<head<<" odd="<<odd<<" runs="<<w.size()<<" maxruns="<<maxruns<<"\n";for(auto [p,n]:w)cout<<"ZQPR"[p]<<n<<" ";cout<<"\n";}
