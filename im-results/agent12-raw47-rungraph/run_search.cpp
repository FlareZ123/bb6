#include <bits/stdc++.h>
using namespace std;
using U=uint64_t;
struct Params { int lag,k,t,m; bool pair; };
struct Dfa {
 Params p; vector<vector<int>> ws; map<vector<int>,int> ids; vector<array<int,2>> d;
 Dfa(Params P):p(P){ vector<int>w={0,0}; if(p.pair)w.push_back(0); ws.push_back(w);ids[w]=0;d.push_back({-1,-1}); }
 int inc(int n){return n+1>=p.t+p.m?p.t:n+1;}
 int push(int s,int b){int old=d[s][b];if(old>=0)return old;auto w=ws[s];int a=b;if(p.lag){a^=(w[0]>>(p.lag-1))&1;w[0]=((w[0]<<1)|b)&((1<<p.lag)-1);}
 if(p.pair){
  if(a==0){if(w[2])w[1]=inc(w[1]);}
  else if(!w[1])w[2]=inc(w[2]);
  else {if(w.size()>=6&&w[3]==w[1]&&w[4]==w[2])w[5]=inc(w[5]);else {w.insert(w.begin()+3,{w[1],w[2],1});if(w.size()>size_t(3+3*p.k))w.resize(3+3*p.k);}w[1]=0;w[2]=1;}
 } else {
  if(w.size()==2){if(a){w[1]=a;w.push_back(1);}}
  else if(w[1]==a)w[2]=inc(w[2]);
  else {w[1]=a;w.insert(w.begin()+2,1);if(w.size()>size_t(2+p.k))w.resize(2+p.k);}
 }
 auto [it,added]=ids.emplace(w,ws.size());int y=it->second;if(added){ws.push_back(w);d.push_back({-1,-1});}d[s][b]=y;return y;}
};
struct S{int q,l,r;};
struct Solver{
 Dfa d[2]; vector<vector<pair<int,int>>> E[2]; vector<vector<int>> W[2]; vector<S> states; unordered_set<U> seen; int tab[12],cap; bool fail=false;
 Solver(string t,Params a,Params b,int c):d{Dfa(a),Dfa(b)},cap(c){for(int i=0;i<12;i++)tab[i]=t[i*3]=='-'?-1:(t[i*3]-'0')*12+(t[i*3+1]=='R')*6+t[i*3+2]-'A';for(int i=0;i<2;i++){E[i].resize(1);E[i][0].push_back({0,0});W[i].resize(1);}}
 void add(int q,int l,int r){U k=(U(q)<<48)|(U(l)<<24)|U(r);if(seen.insert(k).second){states.push_back({q,l,r});if(tab[q]<0||states.size()>size_t(cap))fail=true;}}
 void pop(S st,int b,int src){int t=tab[st.q],w=t/12,q=2*(t%6)+b;if(t%12>=6)add(q,d[0].push(st.l,w),src);else add(q,src,d[1].push(st.r,w));}
 void grow(int side,int i){if(E[side].size()<=size_t(i)){E[side].resize(i+1);W[side].resize(i+1);}}
 bool run(){add(0,0,0);for(int i=0;i<(int)states.size()&&!fail;i++){auto st=states[i];int t=tab[st.q],dr=t%12>=6,side=1-dr,w=t/12,src=dr?st.l:st.r,dst=d[side].push(src,w);grow(side,dst);grow(side,src);auto &es=E[side][dst];if(find(es.begin(),es.end(),make_pair(w,src))==es.end()){es.push_back({w,src});for(int j:W[side][dst]){pop(states[j],w,src);if(fail)break;}}if(fail)break;int v=dr?st.r:st.l;grow(dr,v);W[dr][v].push_back(i);for(auto[b,pr]:E[dr][v]){pop(st,b,pr);if(fail)break;}}return !fail;}
};
int main(int argc,char**argv){int id;string t;
 if(argc>1&&string(argv[1])=="asym") {
  int maxtry=argc>2?atoi(argv[2]):5000,cap=argc>3?atoi(argv[3]):50000;
  vector<Params> p;for(int lag:{0,1,2,3,4,5,6,7,8,9,10,12})for(int k:{1,2,3,4,5,6,8,10,12,16})for(int m:{1,2,3,4,6,8})for(int t:{2,4,8,16})for(int pair:{0,1})if(k<=6||!pair)p.push_back({lag,k,t,m,bool(pair)});
  auto size=[](Params p){return p.k*(p.t+p.m)*(p.pair?2:1)+3*p.lag;};stable_sort(p.begin(),p.end(),[&](Params a,Params b){return size(a)<size(b);});
  while(cin>>id>>t){mt19937 rng(123456+id);bool yes=false;for(int i=0;i<maxtry;i++){int ix,iy; if(i<400){ix=i/20;iy=i%20;}else {int bound=i<2000?400:(i<5000?1200:p.size());ix=rng()%bound;iy=rng()%bound;}auto x=p[ix],y=p[iy];Solver s(t,x,y,cap);if(s.run()){cout<<id<<' '<<t<<' '<<x.lag<<' '<<x.k<<' '<<x.t<<' '<<x.m<<' '<<x.pair<<' '<<y.lag<<' '<<y.k<<' '<<y.t<<' '<<y.m<<' '<<y.pair<<' '<<s.states.size()<<' '<<s.d[0].ws.size()<<' '<<s.d[1].ws.size()<<endl;yes=true;break;}}if(!yes)cerr<<id<<' '<<t<<endl;}return 0;}
 if(argc>1&&string(argv[1])=="emit") {string line;while(getline(cin,line)){if(line.empty())continue;istringstream in(line);in>>id>>t;vector<int> v;int x;while(in>>x)v.push_back(x);if(v.size()!=8&&v.size()!=13)return 2;Params p{v[0],v[1],v[2],v[3],bool(v[4])};Params r=p;int k=5;if(v.size()==13){r={v[5],v[6],v[7],v[8],bool(v[9])};k=10;}int ns=v[k],nl=v[k+1],nr=v[k+2];Solver s(t,p,r,ns+1);if(!s.run()||s.states.size()!=size_t(ns)||s.d[0].ws.size()!=size_t(nl)||s.d[1].ws.size()!=size_t(nr))return 1;cout<<id<<' '<<t<<'\n';for(int j=0;j<2;j++){int n=s.d[j].ws.size();cout<<n<<'\n';for(int i=0;i<n;i++){cout<<max(0,s.d[j].d[i][0])<<' '<<max(0,s.d[j].d[i][1]);if(i<(int)s.E[j].size())for(auto[b,v]:s.E[j][i])cout<<' '<<b<<' '<<v;cout<<'\n';}}cout<<ns<<'\n';for(auto st:s.states)cout<<st.q<<' '<<st.l<<' '<<st.r<<'\n';}return 0;}
vector<Params> ps;for(int lag:{0,1,2,3,4,5,6,7,8,9,10})for(int k:{2,3,4,5,6,8,10,12,16})for(int p:{1,2,3,4,6})for(int a:{2,4,8})ps.push_back({lag,k,a,p,false});for(int lag:{0,1,2,3,4,5,6})for(int k:{1,2,3,4,5,6})for(int p:{1,2,3,4})for(int a:{2,4,8})ps.push_back({lag,k,a,p,true});stable_sort(ps.begin(),ps.end(),[](Params a,Params b){return a.k*(a.t+a.m)*(a.pair?2:1)+3*a.lag < b.k*(b.t+b.m)*(b.pair?2:1)+3*b.lag;});int cap=argc>1?atoi(argv[1]):15000;int tries=argc>2?atoi(argv[2]):ps.size();while(cin>>id>>t){bool yes=false;for(int i=0;i<min(tries,(int)ps.size());i++){auto p=ps[i];Solver s(t,p,p,cap);if(s.run()){cout<<id<<' '<<t<<' '<<p.lag<<' '<<p.k<<' '<<p.t<<' '<<p.m<<' '<<p.pair<<' '<<s.states.size()<<' '<<s.d[0].ws.size()<<' '<<s.d[1].ws.size()<<endl;yes=true;break;}}if(!yes)cerr<<id<<' '<<t<<endl;}}
