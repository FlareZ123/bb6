// Sparse exact n-gram fixed point. Search output is untrusted; Lean checks closure.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>
using namespace std;
using U=uint64_t;
struct NGram {
 int k; U M,mask; array<int,12> tr; unordered_set<U> seen; vector<U> todo;
 array<unordered_map<U,uint8_t>,2> edges;
 array<unordered_map<U,vector<U>>,2> waiting;
 bool fail=false,limit=false;
 NGram(string s,int n):k(n),M(1ULL<<k),mask(M-1){
  for(int j=0;j<12;j++)tr[j]=s[3*j]=='-'?-1:12*(s[3*j]-'0')+6*(s[3*j+1]=='R')+s[3*j+2]-'A';
  for(int d=0;d<2;d++)edges[d][0]=1;
  add(0,0,0,0);
 }
 void add(int q,int a,U l,U r){
  U id=((U(q*2+a)*M+l)*M+r);
  if(!seen.insert(id).second)return;
  todo.push_back(id);if(tr[2*q+a]<0)fail=true;if(todo.size()>2000000)limit=true;
 }
 void decode(U id,int &s,U &l,U&r){r=id&mask;id>>=k;l=id&mask;s=id>>k;}
 void pop(U id,int e){
  int s;U l,r;decode(id,s,l,r);int m=tr[s],q=m%6,w=m/12;bool R=m%12>=6;
  if(R)add(q,r&1,((l<<1)|w)&mask,(r>>1)|(U(e)<<(k-1)));
  else add(q,l&1,(l>>1)|(U(e)<<(k-1)),((r<<1)|w)&mask);
 }
 void edge(int d,U x,int e){
  auto &v=edges[d][x];if(v&(1<<e))return;v|=1<<e;
  auto it=waiting[d].find(x);
  if(it!=waiting[d].end())for(auto id:it->second){pop(id,e);if(fail||limit)break;}
 }
 bool check(){
  for(size_t i=0;i<todo.size()&&!fail&&!limit;i++){
   int s;U l,r;decode(todo[i],s,l,r);int m=tr[s],q=m%6,w=m/12;bool R=m%12>=6;
   U push=R?l:r,popx=R?r:l;
   edge(R?0:1,((push<<1)|w)&mask,push>>(k-1));if(fail||limit)break;
   int d=R?1:0;waiting[d][popx].push_back(todo[i]);
   auto it=edges[d].find(popx);
   if(it!=edges[d].end())for(int e=0;e<2;e++)if(it->second&(1<<e))pop(todo[i],e);
  }
  return !fail&&!limit;
 }
 void dump(int id){
  cout<<id<<' '<<k<<' '<<todo.size()<<' ';
  for(int d=0;d<2;d++){
   vector<pair<U,uint8_t>> s(edges[d].begin(),edges[d].end());sort(s.begin(),s.end());
   for(auto [x,v]:s)if(v)cout<<x<<':'<<int(v)<<',';
   cout<<' ';
  }
  sort(todo.begin(),todo.end());for(auto s:todo)cout<<s<<',';cout<<'\n';
 }
};
int main(int argc,char**argv){
 if(argc!=2)return 2;
 int k=stoi(argv[1]);if(k<1||k>29)return 2;
 int id;string s;
 while(cin>>id>>s){s.erase(remove(s.begin(),s.end(),'_'),s.end());if(s.size()!=36)return 2;
  NGram a(s,k);if(!a.check()){cerr<<id<<' '<<a.todo.size()<<" no certificate\n";return 1;}a.dump(id);
 }
}
