#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <map>
#include <tuple>
#include <cstdint>
#include <chrono>
#include <boost/multiprecision/cpp_int.hpp>
using namespace std; using U=boost::multiprecision::uint1024_t;
using Dfa=vector<array<int,2>>;vector<Dfa> bank;vector<pair<int,int>> pairs;
Dfa ngram(int n){Dfa d(1<<n);for(int j=0;j<(1<<n);j++)for(int b=0;b<2;b++)d[j][b]=((j*2)|b)&((1<<n)-1);return d;}
Dfa runDfa(int cap,int mod,int depth){using Run=array<int,3>;using R=vector<Run>;vector<R> states(1);map<R,int> ids{{{},0}};Dfa d;for(size_t i=0;i<states.size();i++){array<int,2> z;for(int b=0;b<2;b++){R r=states[i];if(r.empty()&&!b){}else if(!r.empty()&&r[0][0]==b){r[0][1]=min(cap,r[0][1]+1);r[0][2]=(r[0][2]+1)%mod;}else{r.insert(r.begin(),{b,1,1%mod});if(int(r.size())>depth)r.resize(depth);}auto [it,neww]=ids.emplace(r,states.size());if(neww)states.push_back(r);z[b]=it->second;}d.push_back(z);}return d;}
void init(){for(int n=1;n<=6;n++)bank.push_back(ngram(n));for(int c=1;c<=3;c++)for(int m=1;m<=4;m++)for(int d=1;d<=2;d++)if(c*m*d<=12)bank.push_back(runDfa(c,m,d));for(int i=0;i<(int)bank.size();i++)for(int j=0;j<(int)bank.size();j++)if(bank[i].size()*bank[j].size()<=4096)pairs.push_back({i,j});stable_sort(pairs.begin(),pairs.end(),[](auto x,auto y){return bank[x.first].size()*bank[x.second].size()<bank[y.first].size()*bank[y.second].size();});}
struct Row{int q,b,l,r;};
bool mitm(const array<int,12>& a,const Dfa& L,const Dfa& R){int N=L.size(),M=R.size();vector<vector<int>> E[2]={vector<vector<int>>(N),vector<vector<int>>(M)},W[2]={vector<vector<int>>(N),vector<vector<int>>(M)};vector<uint8_t> seen(12*N*M);vector<Row> Q;Q.reserve(100);auto add=[&](int q,int b,int l,int r){int k=((2*q+b)*N+l)*M+r;if(!seen[k]){seen[k]=1;Q.push_back({q,b,l,r});}};auto pop=[&](int index,int edge){Row x=Q[index];int m=a[2*x.q+x.b],w=m%4/2,n=m/4,b=edge%2,src=edge/2;if(m%2)add(n,b,L[x.l][w],src);else add(n,b,src,R[x.r][w]);};E[0][0].push_back(0);E[1][0].push_back(0);add(0,0,0,0);for(size_t i=0;i<Q.size();i++){Row x=Q[i];int m=a[2*x.q+x.b];if(m<0)return false;int w=m%4/2,d=m%2,old=d?x.l:x.r,dest=d?L[old][w]:R[old][w],edge=2*old+w;auto& es=E[1-d][dest];if(find(es.begin(),es.end(),edge)==es.end()){es.push_back(edge);for(int index:W[1-d][dest])pop(index,edge);}int t=d?x.r:x.l;W[d][t].push_back(i);for(int e:E[d][t])pop(i,e);}return true;}
struct S{U l,r;int q,h;};
struct Scan{array<int,12>a;vector<S>s;uint64_t nodes=0,side=0,halt=0,open=0,split=0,aut=0,cap;int maxn=0,lim;bool stopped=false;ostream* trace=nullptr;vector<string>unknown;
string tab(){string t;for(int i=0;i<12;i++){if(i&&i%2==0)t+='_';int m=a[i];if(m<0)t+="---";else {t+=char('0'+(m%4)/2);t+=m%2?'R':'L';t+=char('A'+m/4);}}return t;}
void dfs(int n,int f,int holes){if(++nodes>cap){stopped=true;return;}int start=n;bool tried=false;for(;n<=lim;n++){S& x=s[n];int mn=x.h,mx=x.h;for(int e=n-1;e>=0;e--){S& y=s[e];mn=min(mn,y.h);mx=max(mx,y.h);if(x.q!=y.q)continue;int b=y.h-mn;if(x.r==y.r&&x.h>=y.h&&b<1024&&((x.l^y.l)&((U(1)<<b)-1))==0){side++;if(trace)*trace<<"S "<<e<<' '<<n-e<<" 1 "<<y.h-b<<'\n';return;}b=mx-y.h;if(x.l==y.l&&(x.r&1)==(y.r&1)&&x.h<=y.h&&b<1024&&(((x.r^y.r)>>1)&((U(1)<<b)-1))==0){side++;if(trace)*trace<<"S "<<e<<' '<<n-e<<" 0 "<<y.h+b<<'\n';return;}}
int slot=2*x.q+int(x.r&1),m=a[slot];if(m<0){maxn=max(maxn,n);if(holes==1){halt++;if(trace)*trace<<"H "<<n<<' '<<slot<<'\n';return;}split++;if(trace)*trace<<"B "<<n<<' '<<slot<<' '<<f<<'\n';for(int j=0;j<4*min(f+1,6);j++){a[slot]=j;dfs(n,max(f,j/4+1),holes-1);if(stopped)break;}a[slot]=-1;return;}
if(n>=96&&!tried){tried=true;for(auto [i,j]:pairs){if(mitm(a,bank[i],bank[j])){aut++;if(trace)*trace<<"A "<<i<<' '<<j<<'\n';return;}}}
if(n==lim)break;int w=m%4/2,d=m%2;S& y=s[n+1];y.q=m/4;y.h=x.h+(d?1:-1);if(d){if((x.l>>1023)!=0)break;y.l=(x.l<<1)|w;y.r=x.r>>1;}else{if((x.r>>1023)!=0)break;y.l=x.l>>1;y.r=((x.r>>1)<<2)|(U(w)<<1)|(x.l&1);}}
open++;unknown.push_back(tab());if(trace)*trace<<"U "<<tab()<<'\n';}
void run(string t,uint64_t c,int l){cap=c;lim=l;s.resize(l+1);t.erase(remove(t.begin(),t.end(),'_'),t.end());int f=1,h=0;for(int i=0;i<12;i++){if(t[3*i]=='-'){a[i]=-1;h++;}else{a[i]=4*(t[3*i+2]-'A')+2*(t[3*i]-'0')+(t[3*i+1]=='R');f=max(f,a[i]/4+1);}}s[0]={0,0,0,0};dfs(0,f,h);}
};
int main(int argc,char**argv){init();uint64_t cap=argc>1?stoull(argv[1]):1000000;int lim=argc>2?stoi(argv[2]):512;string t;int id=0;while(cin>>t){Scan s;ofstream file;if(argc>3){file.open(string(argv[3])+to_string(id)+".tree");s.trace=&file;}auto st=chrono::steady_clock::now();s.run(t,cap,lim);cout<<t<<" nodes="<<s.nodes<<" side="<<s.side<<" split="<<s.split<<" halt="<<s.halt<<" auto="<<s.aut<<" open="<<s.open<<" max="<<s.maxn<<" capped="<<s.stopped<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-st).count()<<endl;for(auto&u:s.unknown)cout<<"OPEN "<<u<<'\n';cout.flush();id++;}}
