// Phase-aware sparse BiDFA candidate search. Output must be checked by the Lean BiDFA checker.
#include <bits/stdc++.h>
using namespace std;using U=uint64_t;
struct DFA {int k,m,p,mode,mm; U mask; vector<array<int,2>> d; unordered_map<U,int> ids;vector<U> codes;
 DFA(int kk,int md,int pp,int mo,int m2):k(kk),m(md),p(pp),mode(mo),mm(m2),mask((1ULL<<kk)-1){intern(0);}
 int intern(U x){auto [it,ins]=ids.emplace(x,ids.size());if(ins){d.push_back({-1,-1});codes.push_back(x);}return it->second;}
 int push(int i,int b){if(d[i][b]>=0)return d[i][b];U x=codes[i],y; if(!x&&!b)y=0;else{U tail=x&mask,head=(x>>k)&((1ULL<<p)-1),plen=(x>>(k+p))&31,mod=(x>>(k+p+5))&255,mod2=(x>>(k+p+13))&63;if(!x){head=p?1:0;plen=min(1,p);mod=1%m;mod2=1%mm;}else{if(plen<p){head=(head<<1)|b;plen++;}mod2=(mod2+1)%mm;int reset=0;if(mode>=3&&mode<7)reset=(((tail<<1)|b)&3)==mode-3;else if(mode>=7&&mode<15)reset=(((tail<<1)|b)&7)==mode-7;mod=reset?0:(mod+(mode==1?b:mode==2?1-b:1))%m;}y=(U(1)<<(k+p+19))|(mod2<<(k+p+13))|(mod<<(k+p+5))|(plen<<(k+p))|(head<<k)|((tail<<1|b)&mask);}
 int a=intern(y);d[i][b]=a;return a;}
};
struct S {int q,a,l,r;};
struct Run {DFA d[2]; vector<vector<pair<int,int>>> edges[2]; vector<vector<int>> waiting[2]; vector<S> todo;unordered_set<U> seen;int tr[12],cap;bool fail=false,lim=false;
 Run(string s,int kl,int kr,int ml,int mr,int pl,int pr,int sl,int sr,int ml2,int mr2,int c):d{DFA(kl,ml,pl,sl,ml2),DFA(kr,mr,pr,sr,mr2)},cap(c){for(int i=0;i<12;i++){auto x=s.substr(3*i,3);tr[i]=x=="---"?-1:12*(x[0]-'0')+6*(x[1]=='R')+x[2]-'A';}ensure(0,0);ensure(1,0);edges[0][0].push_back({0,0});edges[1][0].push_back({0,0});add(0,0,0,0);}
 void ensure(int side,int i){if((int)edges[side].size()<=i){edges[side].resize(i+1);waiting[side].resize(i+1);}}
 void add(int q,int a,int l,int r){U key=(((U(q*2+a)<<28)|l)<<28)|r;if(!seen.insert(key).second)return;todo.push_back({q,a,l,r});if(tr[q*2+a]<0)fail=true;if((int)todo.size()>cap)lim=true;}
 void pop(S s,int b,int src){int m=tr[s.q*2+s.a],q=m%6,w=m/12;bool R=m%12>=6;if(R)add(q,b,d[0].push(s.l,w),src);else add(q,b,src,d[1].push(s.r,w));}
 bool check(){for(size_t i=0;i<todo.size()&&!fail&&!lim;i++){S s=todo[i];int m=tr[2*s.q+s.a],w=m/12;bool R=m%12>=6;int pushd=R?0:1,popd=1-pushd,push=R?s.l:s.r,popx=R?s.r:s.l;int dst=d[pushd].push(push,w);ensure(pushd,dst);auto &e=edges[pushd][dst];if(find(e.begin(),e.end(),make_pair(w,push))==e.end()){e.push_back({w,push});for(int j:waiting[pushd][dst]){pop(todo[j],w,push);if(fail||lim)break;}}if(fail||lim)break;ensure(popd,popx);waiting[popd][popx].push_back(i);for(auto [b,src]:edges[popd][popx]){pop(s,b,src);if(fail||lim)break;}}return !fail&&!lim;}
 void print(){cout<<todo.size()<<" ";for(auto &a:d){cout<<a.d.size()<<":";for(auto x:a.d)cout<<max(0,x[0])<<","<<max(0,x[1])<<",";cout<<" ";}cout<<endl;}
};
struct Param{int k,m,p,s,m2;};
int cost(Param x){return x.k+int(ceil(log2(x.m)))+int(ceil(log2(x.m2)))+x.p+(x.s!=0);}
int main(int argc,char**argv){int id;string s;int cap=argc>1?atoi(argv[1]):20000;vector<Param> ps;for(int k=2;k<=12;k++)for(int m:{1,2,3,4,5,6,7,8,10,12,16,20})for(int p:{0,1,2,3,4,5})for(int mode=0;mode<15;mode++)for(int m2:{1,2,3,4}){if(m==1&&mode!=0)continue;if(mode==0&&m2!=1)continue;if(p>0&&mode!=0)continue;if(m2>1&&p>0)continue;Param a{k,m,p,mode,m2};if(cost(a)<=16)ps.push_back(a);}
 while(cin>>id>>s){s.erase(remove(s.begin(),s.end(),'_'),s.end());bool ok=false;vector<Param> left,right;for(auto p:ps){if(p.p==0&&p.s==0&&p.m2==1&&p.k<=8&&p.m<=8)left.push_back(p);right.push_back(p);}
 mt19937 rng(id);shuffle(left.begin(),left.end(),rng);shuffle(right.begin(),right.end(),rng);stable_sort(left.begin(),left.end(),[](auto a,auto b){return cost(a)<cost(b);});stable_sort(right.begin(),right.end(),[](auto a,auto b){return cost(a)<cost(b);});
 for(int pass=0;pass<2&&!ok;pass++){
   auto& L=pass==0?left:right;auto& R=pass==0?right:left;
   for(int target=5;target<=24&&!ok;target++)for(auto l:L){if(cost(l)>=target)break;for(auto r:R){int c=cost(l)+cost(r);if(c>target)break;if(c!=target)continue;Run a(s,l.k,r.k,l.m,r.m,l.p,r.p,l.s,r.s,l.m2,r.m2,cap);if(a.check()){cout<<id<<" "<<l.k<<" "<<r.k<<" "<<l.m<<" "<<r.m<<" "<<l.p<<" "<<r.p<<" "<<l.s<<" "<<r.s<<" "<<l.m2<<" "<<r.m2<<" ";a.print();ok=true;break;}}if(ok)break;}
 }
 if(!ok)cerr<<id<<" NO\n";
 }}
