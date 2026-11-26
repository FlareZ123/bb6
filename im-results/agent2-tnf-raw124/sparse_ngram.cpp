#include <array>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <string>
using namespace std;
struct NGram {
 int k[2];uint64_t mask[2];array<int,12> tr;unordered_set<uint64_t> seen;vector<uint64_t> todo;array<unordered_map<uint64_t,uint8_t>,2> edges;array<unordered_map<uint64_t,vector<uint64_t>>,2> waiting;bool fail=false,capfail=false;size_t cap;
 NGram(string s,int n,int m,size_t c):k{n,m},mask{(1ull<<n)-1,(1ull<<m)-1},cap(c){for(int j=0;j<12;j++)tr[j]=s[3*j]=='-'?-1:12*(s[3*j]-'0')+6*(s[3*j+1]=='R')+s[3*j+2]-'A';for(int d=0;d<2;d++)edges[d][0]=1;add(0,0,0,0);}
 void add(int q,int a,uint64_t l,uint64_t r){uint64_t id=(((uint64_t)(q*2+a)<<k[0])|l)<<k[1]|r;if(seen.insert(id).second){todo.push_back(id);if(tr[2*q+a]<0)fail=true;if(todo.size()>cap)capfail=true;}}
 void decode(uint64_t id,int &s,uint64_t &l,uint64_t&r){r=id&mask[1];id>>=k[1];l=id&mask[0];s=id>>k[0];}
 void pop(uint64_t id,int e){int s;uint64_t l,r;decode(id,s,l,r);int m=tr[s],q=m%6,w=m/12;bool R=m%12>=6;if(R)add(q,r&1,((l<<1)|w)&mask[0],(r>>1)|((uint64_t)e<<(k[1]-1)));else add(q,l&1,(l>>1)|((uint64_t)e<<(k[0]-1)),((r<<1)|w)&mask[1]);}
 void edge(int d,uint64_t x,int e){if(edges[d][x]&(1<<e))return;edges[d][x]|=1<<e;auto it=waiting[d].find(x);if(it!=waiting[d].end())for(auto id:it->second)pop(id,e);}
 bool check(){for(size_t i=0;i<todo.size()&&!fail&&!capfail;i++){int s;uint64_t l,r;decode(todo[i],s,l,r);int m=tr[s],w=m/12;bool R=m%12>=6;int d=R?1:0,dp=1-d;uint64_t push=R?l:r,popx=R?r:l;edge(dp,((push<<1)|w)&mask[dp],push>>(k[dp]-1));waiting[d][popx].push_back(todo[i]);for(int e=0;e<2;e++)if(edges[d][popx]&(1<<e))pop(todo[i],e);}return !fail&&!capfail;}
 void dump(ostream& o){o<<k[0]<<' '<<k[1]<<' '<<todo.size()<<'\n';for(int d=0;d<2;d++){vector<pair<uint64_t,uint8_t>> es(edges[d].begin(),edges[d].end());sort(es.begin(),es.end());for(auto [x,b]:es)if(b)o<<x<<':'<<int(b)<<',';o<<'\n';}sort(todo.begin(),todo.end());for(auto s:todo)o<<s<<',';o<<'\n';}
};
int main(int argc,char**argv){if(argc<3||argc>4)return 1;int n=stoi(argv[1]),m=stoi(argv[2]);if(n<1||m<1||n+m>60)return 1;size_t cap=argc>3?stoull(argv[3]):2000000;string s;int rid;while(cin>>rid>>s){s.erase(remove(s.begin(),s.end(),'_'),s.end());NGram a(s,n,m,cap);bool ok=a.check();cerr<<rid<<' '<<n<<','<<m<<' '<<a.todo.size()<<' '<<(ok?"OK":a.capfail?"CAP":"FAIL")<<'\n';if(ok){cout<<rid<<'\n';a.dump(cout);}}}
