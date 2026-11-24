#include <array>
#include <bitset>
#include <string>
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <stdexcept>
#include <map>
using namespace std;
constexpr int C=2000,S=2*C+1;
using T=array<int,12>;
struct Config{int h,lo,hi; bitset<S> tape;};
int cap=1000,window=256, maxn=0;
map<string,long long> stats;
ofstream out,op;
T parse(string s){s.erase(remove(s.begin(),s.end(),'_'),s.end());if(s.size()!=36)throw runtime_error("bad code");T t;for(int i=0;i<12;i++){string a=s.substr(3*i,3);t[i]=a=="---"?24:4*(a[2]-'A')+2*(a[0]=='1')+(a[1]=='R');}return t;}
string show(T t){string s;for(int i=0;i<12;i++){if(i&&i%2==0)s+='_';int a=t[i];if(a==24)s+="---";else{s+=char('0'+(a/2%2));s+=a%2?'R':'L';s+=char('A'+a/4);}}return s;}
bool eqHalf(const Config&a,const Config&b,int delta,int bound,bool right){int lo,hi;if(right){lo=bound;hi=max(a.hi,b.hi-delta);}else{lo=min(a.lo,b.lo-delta);hi=bound;}for(int x=lo;x<=hi;x++)if(a.tape[x+C]!=b.tape[x+delta+C])return false;return true;}
struct R{int typ,n,s,k,b;bool r;};
R classify(T t){int q=0;Config c{0,0,0,{}};vector<Config> trace;array<vector<int>,6> prev;trace.reserve(cap+1);for(int n=0;n<=cap;n++){
 int a=t[2*q+c.tape[c.h+C]];if(a==24)return {0,n,2*q+int(c.tape[c.h+C]),0,0,false};
 int lo=c.h,hi=c.h,i=n-1;for(auto j=prev[q].rbegin();j!=prev[q].rend()&&n-*j<=window;j++){
 while(i>=*j){lo=min(lo,trace[i].h);hi=max(hi,trace[i].h);i--;}
 auto &p=trace[*j];int d=c.h-p.h;
 if(d>=0&&eqHalf(p,c,d,lo,true))return {1,*j,0,n-*j,lo,true};
 if(d<=0&&eqHalf(p,c,d,hi,false))return {1,*j,0,n-*j,hi,false};
 }
 trace.push_back(c);prev[q].push_back(n);c.tape[c.h+C]=(a&2)!=0;c.h+=a&1?1:-1;q=a/4;c.lo=min(c.lo,c.h);c.hi=max(c.hi,c.h);
 }return {2,0,0,0,0,false};}
void build(T t){auto r=classify(t);if(r.typ==1){stats["cycle"]++;out<<"C "<<r.n<<' '<<r.k<<' '<<r.r<<' '<<r.b<<'\n';return;}if(r.typ==2){stats["open"]++;string s=show(t);out<<"O "<<s<<'\n';op<<s<<'\n';stats["holes"+to_string(count(t.begin(),t.end(),24))]++;return;}maxn=max(maxn,r.n);if(count(t.begin(),t.end(),24)==1){stats["last"]++;out<<"L "<<r.n<<' '<<r.s<<'\n';return;}stats["split"]++;out<<"S "<<r.n<<' '<<r.s<<'\n';for(int a=0;a<24;a++){T c=t;c[r.s]=a;build(c);}}
int main(int argc,char**argv){if(argc<3)return 1;if(argc>=4)cap=stoi(argv[3]);if(cap>=C/2)return 2;out.open(string(argv[2])+".tree");op.open(string(argv[2])+".open");build(parse(argv[1]));for(auto [k,v]:stats)cerr<<k<<"="<<v<<" ";cerr<<"maxn="<<maxn<<endl;}
