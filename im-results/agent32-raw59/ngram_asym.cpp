// Sparse unequal-width n-gram closure, based on Agent47's sparse checker.
// Search output is untrusted; the Lean checker verifies every rule.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>
using namespace std;using U=uint64_t;
struct NGram{
 int k[2];U M[2],mask[2];array<int,12>tr;unordered_set<U>seen;vector<U>todo;array<unordered_map<U,uint8_t>,2>edges;array<unordered_map<U,vector<U>>,2>waiting;bool fail=false,limit=false;size_t cap;
 NGram(string s,int l,int r,size_t c):k{l,r},M{1ULL<<l,1ULL<<r},mask{M[0]-1,M[1]-1},cap(c){for(int j=0;j<12;j++)tr[j]=s[3*j]=='-'?-1:12*(s[3*j]-'0')+6*(s[3*j+1]=='R')+s[3*j+2]-'A';edges[0][0]=edges[1][0]=1;add(0,0,0,0);}
 void add(int q,int a,U l,U r){U id=(U(q*2+a)*M[0]+l)*M[1]+r;if(!seen.insert(id).second)return;todo.push_back(id);if(tr[2*q+a]<0)fail=true;if(todo.size()>cap)limit=true;}
 void decode(U id,int&s,U&l,U&r){r=id&mask[1];id>>=k[1];l=id&mask[0];s=id>>k[0];}
 void pop(U id,int e){int s;U l,r;decode(id,s,l,r);int m=tr[s],q=m%6,w=m/12;bool R=m%12>=6;if(R)add(q,r&1,((l<<1)|w)&mask[0],(r>>1)|(U(e)<<(k[1]-1)));else add(q,l&1,(l>>1)|(U(e)<<(k[0]-1)),((r<<1)|w)&mask[1]);}
 void edge(int d,U x,int e){auto&v=edges[d][x];if(v&(1<<e))return;v|=1<<e;auto it=waiting[d].find(x);if(it!=waiting[d].end())for(auto id:it->second){pop(id,e);if(fail||limit)break;}}
 bool check(){for(size_t i=0;i<todo.size()&&!fail&&!limit;i++){int s;U l,r;decode(todo[i],s,l,r);int m=tr[s],w=m/12;bool R=m%12>=6;int pushd=R?0:1,popd=1-pushd;U push=R?l:r,popx=R?r:l;edge(pushd,((push<<1)|w)&mask[pushd],push>>(k[pushd]-1));if(fail||limit)break;waiting[popd][popx].push_back(todo[i]);auto it=edges[popd].find(popx);if(it!=edges[popd].end())for(int e=0;e<2;e++)if(it->second&(1<<e))pop(todo[i],e);}return !fail&&!limit;}
 void dump(int id){cout<<id<<' '<<k[0]<<' '<<k[1]<<' '<<todo.size()<<' ';for(int d=0;d<2;d++){vector<pair<U,uint8_t>>a(edges[d].begin(),edges[d].end());sort(a.begin(),a.end());for(auto [x,v]:a)if(v)cout<<x<<':'<<int(v)<<',';cout<<' ';}sort(todo.begin(),todo.end());for(auto v:todo)cout<<v<<',';cout<<'\n';}
};
int main(){int id,l,r;string s;while(cin>>id>>s>>l>>r){s.erase(remove(s.begin(),s.end(),'_'),s.end());if(s.size()!=36||l<1||r<1||l+r>60)return 2;NGram a(s,l,r,1000000);if(!a.check()){cerr<<id<<" no certificate "<<a.todo.size()<<'\n';return 1;}a.dump(id);} }
