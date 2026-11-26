#include <array>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <string>
using namespace std;
struct Params {int k;int tz,to,pz,po;};
struct Dfa {
 Params p; uint64_t mask;unordered_map<uint64_t,uint32_t> ids;vector<uint64_t> words;vector<array<int,2>> transitions;
 Dfa(Params a):p(a),mask((1ull<<(8*a.k))-1){add(0);}
 uint32_t add(uint64_t x){auto [it,b]=ids.emplace(x,words.size());if(b){words.push_back(x);transitions.push_back({-1,-1});}return it->second;}
 int push(uint32_t i,int b){int old=transitions[i][b];if(old>=0)return old;uint64_t v=words[i],x=v>>1;int last=v&1,n=x&255;uint64_t y;
 if(v==0 && b==0)y=0;
 else if(b!=last || !v)y=(((x<<8)|1)&mask)*2+b;
 else {int t=b?p.to:p.tz,m=b?p.po:p.pz;int z=n<t+m-1?n+1:t;y=((x&~255ull)|z)*2+b;}
 int j=add(y);transitions[i][b]=j;return j;}
};
struct Search {
 Dfa d[2];array<int,12> tr;unordered_set<uint64_t> seen;vector<uint64_t> todo;array<unordered_map<int,vector<pair<int,int>>>,2> edges;array<unordered_map<int,vector<uint64_t>>,2> waiting;size_t cap;bool fail=false,capfail=false;
 Search(string s,Params a,Params b,size_t c):d{Dfa(a),Dfa(b)},cap(c){for(int j=0;j<12;j++)tr[j]=s[3*j]=='-'?-1:12*(s[3*j]-'0')+6*(s[3*j+1]=='R')+s[3*j+2]-'A';for(int i=0;i<2;i++)edges[i][0].push_back({0,0});add(0,0,0,0);}
 void add(int q,int a,int l,int r){uint64_t id=((uint64_t)(q*2+a)<<60)|((uint64_t)l<<30)|r;if(seen.insert(id).second){todo.push_back(id);if(tr[2*q+a]<0)fail=true;if(todo.size()>cap)capfail=true;}}
 void decode(uint64_t id,int &s,int &l,int&r){r=id&((1u<<30)-1);l=(id>>30)&((1u<<30)-1);s=id>>60;}
 void pop(uint64_t id,int a,int x){int s,l,r;decode(id,s,l,r);int m=tr[s],q=m%6,w=m/12;bool R=m%12>=6;if(R)add(q,a,d[0].push(l,w),x);else add(q,a,x,d[1].push(r,w));}
 bool check(){for(size_t i=0;i<todo.size()&&!fail&&!capfail;i++){int s,l,r;decode(todo[i],s,l,r);int m=tr[s],w=m/12;bool R=m%12>=6;int side=R?1:0,dp=1-side;int src=R?l:r,popx=R?r:l,dst=d[dp].push(src,w);auto& es=edges[dp][dst];pair<int,int> edge={w,src};if(find(es.begin(),es.end(),edge)==es.end()){es.push_back(edge);auto it=waiting[dp].find(dst);if(it!=waiting[dp].end())for(auto id:it->second)pop(id,w,src);}waiting[side][popx].push_back(todo[i]);for(auto [a,y]:edges[side][popx])pop(todo[i],a,y);}return !fail&&!capfail;}
 void dump(ostream& o){o<<"[";for(int i=0;i<2;i++){if(i)o<<',';o<<'[';bool first=true;for(auto x:d[i].transitions)for(int y:x){if(!first)o<<',';first=false;o<<max(0,y);}o<<']';}o<<"]\n";}
};
int main(int argc,char**argv){if(argc!=12)return 1;Params a{stoi(argv[1]),stoi(argv[2]),stoi(argv[3]),stoi(argv[4]),stoi(argv[5])},b{stoi(argv[6]),stoi(argv[7]),stoi(argv[8]),stoi(argv[9]),stoi(argv[10])};for(auto p:{a,b})if(p.k<1||p.k>7||min({p.tz,p.to,p.pz,p.po})<1||p.tz+p.pz>256||p.to+p.po>256)return 1;size_t cap=stoull(argv[11]);string s;int rid;while(cin>>rid>>s){s.erase(remove(s.begin(),s.end(),'_'),s.end());Search x(s,a,b,cap);bool ok=x.check();cerr<<rid<<' '<<x.todo.size()<<' '<<x.d[0].words.size()<<','<<x.d[1].words.size()<<' '<<(ok?"OK":x.capfail?"CAP":"FAIL")<<'\n';if(ok){cout<<rid<<' ';x.dump(cout);}}}
