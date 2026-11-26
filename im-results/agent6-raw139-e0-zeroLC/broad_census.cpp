// Untrusted candidate census. Proof generator must kernel-check every closure.
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <vector>
#include <chrono>
using namespace std;
using Table=array<int,12>;
constexpr int SHIFT=512,N=1024,UNKNOWN=24;
using Tape=bitset<N>;
struct Config{int q,h; Tape t;};
struct Witness{int type,n,s,period,dir,b;};
int cap=250,periodCap=120;
Witness scan(const Table &p){
 int q=0,h=0; Tape t; vector<Config> hist;hist.reserve(cap+1);
 for(int n=0;n<=cap;n++){
   int s=2*q+t[h+SHIFT],v=p[s];
   if(v==UNKNOWN)return {1,n,s,0,0,0};
   int lo=h,hi=h;
   for(int i=n-1;i>=max(0,n-periodCap);--i){
     const auto &o=hist[i];lo=min(lo,o.h);hi=max(hi,o.h);
     if(o.q!=q)continue;
     int d=h-o.h;
     if(d>=0 && (o.t>>(lo+SHIFT))==(t>>(lo+SHIFT+d)))return {0,i,0,n-i,1,lo};
     if(d<=0 && (o.t<<(N-1-hi-SHIFT))==(t<<(N-1-hi-SHIFT-d)))return {0,i,0,n-i,0,hi};
   }
   if(n==cap)break;
   hist.push_back({q,h,t});t[h+SHIFT]=(v>>1)&1;h+=(v&1)?1:-1;q=v>>2;
 }
 return {2,0,0,0,0,0};
}
bool far(const Table&p,int d,int rev,const vector<int>&D){
 int N=6*d+1; uint64_t T[40]={}; uint64_t H=1ull<<(N-1); T[N-1]=T[2*N-1]=H;
 struct Rule{int dst,src,off;};vector<Rule> rules;
 for(int b=0;b<2;b++)for(int l=0;l<d;l++)for(int q=0;q<6;q++){int a=p[2*q+b],dst=b*N+6*l+q;if(a==24){T[dst]=H;continue;}int n=a>>2,w=(a>>1)&1,r=a&1;if(r!=rev)T[dst]=1ull<<(6*D[2*l+w]+n);else for(int j=0;j<d;j++)for(int x=0;x<2;x++)if(D[2*j+x]==l)rules.push_back({dst,x*N+6*j+n,w*N});}
 for(bool changed=true;changed;){changed=false;for(auto [dst,src,off]:rules){uint64_t v=T[src],nw=T[dst];while(v){int i=__builtin_ctzll(v);v&=v-1;nw|=T[off+i];}if(nw!=T[dst]){T[dst]=nw;changed=true;}}}
 uint64_t z=H;for(;;){auto old=z;for(int i=0;i<N;i++)if(T[i]&z)z|=1ull<<i;if(old==z)break;}return !(z&1);
}
bool findfar(const Table&p){for(int d=1;d<=2;d++){int n=1;for(int k=1;k<2*d;k++)n*=d;for(int i=0;i<n;i++){int j=i;vector<int>D(2*d,0);for(int k=1;k<2*d;k++){D[k]=j%d;j/=d;}for(int rev=0;rev<2;rev++)if(far(p,d,rev,D))return true;}}return false;}
struct Stat{long long split=0,cyc=0,last=0,open=0,far=0;int maxquery=0;};
int cut(const Table&p){int c=1;for(int i=0;i<12;i++)if(p[i]!=UNKNOWN)c=max({c,i/2+1,p[i]/4+1});return c;}
long long nodes=0;
vector<pair<Table,Witness>> leaves;
void search(Table &p,Stat&st){
 ++nodes;
 auto w=scan(p);
 if(w.type==0){st.cyc++;return;}
 if(w.type==2){if(findfar(p)){st.far++;return;}st.open++;leaves.push_back({p,w});return;}
 st.maxquery=max(st.maxquery,w.n);
 if(count(p.begin(),p.end(),UNKNOWN)==1){st.last++;return;}
 st.split++;
 int c=cut(p);for(int m=0;m<4*min(c+1,6);m++){p[w.s]=m;search(p,st);}p[w.s]=UNKNOWN;
}
string name(int v){return string{char('0'+((v>>1)&1)),(v&1)?'R':'L',char('A'+v/4)};}
void printTable(ostream&o,const Table&p){for(int i=0;i<12;i++)o<<p[i]<<(i==11?'\n':',');}
int main(int argc,char**argv){
 Table p={7,24,11,24,14,24,24,16,8,11,24,24};
 vector<int> cs={0,1,2,3,5,6,7,11,20,21,22,23};
 if(argc>1)cs={atoi(argv[1])};
 for(int v:cs){p[6]=v;nodes=0;leaves.clear();Stat st;search(p,st);cout<<name(v)<<" nodes="<<nodes<<" split="<<st.split<<" cycle="<<st.cyc<<" last="<<st.last<<" far="<<st.far<<" open="<<st.open<<" maxq="<<st.maxquery<<endl;
 ofstream f("raw139_e0_0LC_"+name(v)+"_leaves.txt");for(auto&[p,w]:leaves){f<<w.type<<' '<<w.n<<' '<<w.s<<' ';printTable(f,p);}}
}
