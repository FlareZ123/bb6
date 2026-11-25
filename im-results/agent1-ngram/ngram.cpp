// Candidate generator only. Every accepted output must pass NGramCertificate.check.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct NGram {
 int k,M,mask;array<int,12> tr;vector<uint8_t> seen;vector<uint32_t> todo;array<vector<uint8_t>,2> edges;array<vector<vector<uint32_t>>,2> waiting;
 bool fail=false;
 NGram(string s,int n):k(n),M(1<<k),mask(M-1),seen(12*M*M){for(int j=0;j<12;j++)tr[j]=s[3*j]=='-'?-1:12*(s[3*j]-'0')+6*(s[3*j+1]=='R')+s[3*j+2]-'A';for(int d=0;d<2;d++){edges[d].resize(M);waiting[d].resize(M);edges[d][0]=1;}add(0,0,0,0);}
 void add(int q,int a,int l,int r){uint32_t id=((q*2+a)*M+l)*M+r;if(!seen[id]){seen[id]=1;todo.push_back(id);if(tr[2*q+a]<0)fail=true;}}
 void decode(uint32_t id,int &s,int &l,int&r){r=id&mask;id>>=k;l=id&mask;s=id>>k;}
 void pop(uint32_t id,int e){int s,l,r;decode(id,s,l,r);int m=tr[s],q=m%6,w=m/12;bool R=m%12>=6;if(R)add(q,r&1,((l<<1)|w)&mask,(r>>1)|(e<<(k-1)));else add(q,l&1,(l>>1)|(e<<(k-1)),((r<<1)|w)&mask);}
 void edge(int d,int x,int e){if(edges[d][x]&(1<<e))return;edges[d][x]|=1<<e;for(auto id:waiting[d][x])pop(id,e);}
 bool check(){for(size_t i=0;i<todo.size()&&!fail;i++){int s,l,r;decode(todo[i],s,l,r);int m=tr[s],q=m%6,w=m/12;bool R=m%12>=6;int push=R?l:r,popx=R?r:l;edge(R?0:1,((push<<1)|w)&mask,push>>(k-1));int d=R?1:0;waiting[d][popx].push_back(todo[i]);for(int e=0;e<2;e++)if(edges[d][popx]&(1<<e))pop(todo[i],e);}return !fail;}
 void dump(int id){cout<<id<<' '<<k<<' '<<todo.size()<<' ';for(int d=0;d<2;d++){for(auto e:edges[d])cout<<int(e);cout<<' ';}sort(todo.begin(),todo.end());for(auto s:todo)cout<<s<<',';cout<<'\n';}
};
int main(int argc,char**argv){int maxk=argc>1?stoi(argv[1]):8;if(maxk<1||maxk>12)return 2;int i;string s;while(cin>>i>>s){s.erase(remove(s.begin(),s.end(),'_'),s.end());if(s.size()!=36)return 2;bool ok=false;for(int k=1;k<=maxk;k++){NGram a(s,k);if(a.check()){a.dump(i);ok=true;break;}}if(!ok)cerr<<i<<' '<<s<<'\n';}}
