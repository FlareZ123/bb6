#include <bits/stdc++.h>
using namespace std;

// Derived-macro defect scan for Raw56 leaf 17557.
// This program assumes the exact A/B triad rewrites from 17557-triad-rewrite.md;
// it is not a primitive-machine proof. It streams low W_n against high sigma(W_n)
// and checks the repaired relation without materializing either boundary orbit.
// Reproduction: g++ -O3 -std=c++20 analyze_17557_defect_stream.cpp -o /tmp/d && /tmp/d 15
struct Run{int b; long long n;}; // n=-1 means infinite blank-zero tail
struct Z{vector<Run>L,R;};
static inline bool inf(long long n){return n<0;}
static inline long long subn(long long n,long long k){return inf(n)?-1:n-k;}
static inline bool geq(long long n,long long k){return inf(n)||n>=k;}
void add(vector<Run>&o,int b,long long n){if(n==0)return;if(!o.empty()&&o.back().b==b){if(inf(o.back().n)||inf(n))o.back().n=-1;else o.back().n+=n;}else o.push_back({b,n});}
Z checkpoint(int n){long long a=(1LL<<n)-2,b=(1LL<<(n+1))-3,c=(1LL<<(n+1))-1;return {{{0,-1}},{{1,a},{0,1},{1,b},{0,1},{1,c},{0,-1}}};}
void macro(Z&z,char lab){auto L=z.L,R=z.R;if(lab=='A'){
 if(R.size()<6||R[0].b!=1||R[1].b!=0||R[2].b!=1||R[3].b!=0||R[4].b!=1||R[5].b!=0) throw runtime_error("A shape");
 auto a=R[0].n,s1=R[1].n,b=R[2].n,s2=R[3].n,c=R[4].n,zz=R[5].n;if(s1!=1||s2!=1||b<5||c<1||!geq(zz,2))throw runtime_error("A guards");vector<Run>tail(R.begin()+6,R.end());
 if(b>=6){vector<Run>nl;add(nl,0,b-6);add(nl,1,a+2);for(auto x:L)add(nl,x.b,x.n);z.L=move(nl);vector<Run>nr;add(nr,1,2);add(nr,0,1);add(nr,1,c+5);add(nr,0,subn(zz,2));for(auto x:tail)add(nr,x.b,x.n);z.R=move(nr);}else{
 long long d=0,ell;size_t pos;if(L[0].b==0){ell=L[0].n;pos=1;}else{if(L.size()<2||L[1].b!=0)throw runtime_error("carry left");d=L[0].n;ell=L[1].n;pos=2;}if(!geq(ell,1))throw runtime_error("carry ell");vector<Run>nl;add(nl,0,subn(ell,1));for(size_t i=pos;i<L.size();i++)add(nl,L[i].b,L[i].n);z.L=move(nl);vector<Run>nr;add(nr,1,d+a+4);add(nr,0,1);add(nr,1,c+5);add(nr,0,subn(zz,2));for(auto x:tail)add(nr,x.b,x.n);z.R=move(nr);}
 }else if(lab=='B'){
 if(L.empty()||L[0].b!=0||!geq(L[0].n,7)||R.size()<4||R[0].b!=1||R[1].b!=0||R[2].b!=1||R[3].b!=0)throw runtime_error("B shape");auto ell=L[0].n,a=R[0].n,s=R[1].n,b=R[2].n,zz=R[3].n;if(a<2||s!=1||b<1||!geq(zz,2))throw runtime_error("B guards");vector<Run>nl;add(nl,0,subn(ell,7));for(size_t i=1;i<L.size();i++)add(nl,L[i].b,L[i].n);z.L=move(nl);vector<Run>nr;add(nr,1,2);add(nr,0,1);add(nr,1,5);add(nr,0,a-1);add(nr,1,b+3);add(nr,0,subn(zz,2));for(size_t i=4;i<R.size();i++)add(nr,R[i].b,R[i].n);z.R=move(nr);
 }else throw runtime_error("label");}
long long rho0(long long z){if(inf(z))return -1;auto q=z/8,r=z%8;return 16*q+(r==7?15:r);}
vector<Run> rhoL(const vector<Run>&L){vector<Run>o;for(auto x:L)add(o,x.b,inf(x.n)?-1:(x.b?2*x.n:rho0(x.n)));return o;}
vector<Run> rhoR(const vector<Run>&R){if(R.size()<3||R.size()%2!=0||R.front().b!=1||R.back().b!=0)throw runtime_error("rhoR tail shape");vector<Run>core(R.begin(),R.end()-1);int m=(core.size()+1)/2;vector<Run>o;for(int i=0;i<(int)core.size();i++){auto x=core[i];long long y;if(x.b){int j=i/2+1;if(j==1)y=2*x.n+2;else if(j==2&&m==2)y=2*x.n+4;else if(j==2)y=2*x.n+3;else if(j==m)y=2*x.n+1;else y=2*x.n;}else{int j=(i+1)/2;y=j<=2?2*x.n-1:2*x.n+1;}add(o,x.b,y);}add(o,0,-1);return o;}
bool same(const vector<Run>&a,const vector<Run>&b){if(a.size()!=b.size())return false;for(size_t i=0;i<a.size();i++)if(a[i].b!=b[i].b||a[i].n!=b[i].n)return false;return true;}
vector<int> marks(const vector<Run>&lo,const vector<Run>&hi){auto p=rhoL(lo);if(p.size()!=hi.size())return {-99};vector<int>ms;int zi=0;for(size_t i=0;i<p.size();i++){if(p[i].b!=hi[i].b)return {-98};if(inf(p[i].n)||inf(hi[i].n)){if(p[i].n!=hi[i].n)return {-97};}else if(p[i].n!=hi[i].n){if(!p[i].b&&hi[i].n==p[i].n-8)ms.push_back(zi);else return {-96};}if(!p[i].b&&!inf(p[i].n))zi++;}return ms;}
string sigma(string w){string o;o.reserve(w.size()*3);for(char c:w)o+=c=='A'?"ABA":"BBA";return o;}
int main(int argc,char**argv){int maxn=argc>1?atoi(argv[1]):15;string w="ABBA";for(int n=2;n<=maxn;n++){
 Z lo=checkpoint(n),hi=checkpoint(n+1);map<string,long long>dist;long long multi=0,bad=0,rightBad=0;int maxmark=-1;
 for(size_t k=0;k<=w.size();k++){
   auto ms=marks(lo.L,hi.L);if(!ms.empty()&&ms[0]<-90){bad++;}else{if(ms.size()>1)multi++;for(int m:ms)maxmark=max(maxmark,m);string key=ms.empty()?"none":"";for(int m:ms){if(!key.empty())key+=",";key+=to_string(m);}dist[key]++;}
   if(!same(rhoR(lo.R),hi.R))rightBad++;
   if(k==w.size())break;char c=w[k];macro(lo,c);string s=c=='A'?"ABA":"BBA";for(char d:s)macro(hi,d);
 }
 if(!same(lo.L,checkpoint(n+1).L)||!same(lo.R,checkpoint(n+1).R)||!same(hi.L,checkpoint(n+2).L)||!same(hi.R,checkpoint(n+2).R)){cerr<<"checkpoint fail n="<<n<<"\n";return 3;}
 cout<<"n="<<n<<" boundaries="<<w.size()+1<<" rightBad="<<rightBad<<" relationBad="<<bad<<" multi="<<multi<<" maxmark="<<maxmark;for(auto [k,v]:dist)cout<<" "<<k<<"="<<v;cout<<"\n";
 if(rightBad||bad||multi){cerr<<"relation violation at n="<<n<<"\n";return 4;}
 if(n>=10&&n<=15){
   static const vector<map<string,long long>>expected={
    {{"none",26243},{"0",2}},
    {{"none",78703},{"0",28},{"1",2}},
    {{"none",235947},{"0",216},{"1",34}},
    {{"none",707047},{"0",1224},{"1",314},{"2",4}},
    {{"none",2117863},{"0",5724},{"1",2098},{"2",80}},
    {{"none",6341515},{"0",23520},{"1",11390},{"2",860},{"3",8}}};
   if(dist!=expected[n-10]){cerr<<"unexpected defect census at n="<<n<<"\n";return 5;}
 }
 w=sigma(w);
 }}
