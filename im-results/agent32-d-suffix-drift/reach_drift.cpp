#include <array>
#include <algorithm>
#include <string>
#include <vector>
#include <unordered_set>
#include <iostream>
#include <cassert>
#include <optional>
#include <chrono>
using namespace std;
struct Move {int w,d,q;};
constexpr Move T[6][2]={{{1,1,1},{0,1,4}},{{1,-1,2},{0,1,0}},{{1,-1,0},{1,-1,3}},{{1,-1,2},{1,-1,5}},{{0,-1,2},{0,-1,1}},{{1,-1,4},{0,0,-1}}};
struct Ret {int n;string s;};
optional<Ret> raw(int n,const string& s){
    vector<unsigned char> tape(2*(n+s.size()+512),0); int h=n+s.size()+512, q=5,lo=h+1,hi=h+n; for(int i=1;i<=n;++i)tape[h+i]=1;for(size_t i=0;i<s.size();++i)if(s[i]=='1'){tape[h+n+1+i]=1;hi=h+n+1+i;}
    for(int t=0;t<2000000;++t){auto m=T[q][tape[h]];if(m.q<0)return nullopt; tape[h]=m.w;if(m.w){lo=min(lo,h);hi=max(hi,h);}else{if(h==lo)while(lo<=hi&&!tape[lo])++lo;if(h==hi)while(hi>=lo&&!tape[hi])--hi;}
        h+=m.d;q=m.q;if(h<0||h>=int(tape.size()))throw runtime_error("tape bound");
        if(q==5&&!tape[h]&&h<lo&&lo<=hi){int j=h+1;while(j<=hi&&tape[j])++j;string u;for(int i=j;i<=hi;++i)u+=tape[i]?'1':'0';return Ret{j-h-1,u};}
    }throw runtime_error("step bound");
}
int w(int a){return a==0?2:a==1?5:a%3==2?13:6;}
int V(const string&s){int ret=0,a=-1;for(char c:s){if(c=='0'){if(a>=0)ret+=w(a);a=0;}else ++a;}if(a>=0)ret+=w(a);return ret;}
int main(int argc,char**argv){int limit=argc>1?stoi(argv[1]):110; bool cross=argc>2; unordered_set<string>seen{ "" };vector<string>front{ "" };int worst=-1000000;long long screened=0,haltedges=0;for(int depth=0;depth<limit;++depth){vector<string>next;for(auto&s:front){int v=V(s),sum=0;array<optional<Ret>,3>out;for(int b=0;b<3;++b){auto r=raw(12+b,s);out[b]=r;if(cross){auto r2=raw(15+b,s);if(bool(r)!=bool(r2)||(r&& (r2->n!=r->n+8||r2->s!=r->s))){cerr<<"nonaffine "<<depth<<" "<<s<<" branch "<<b<<"\n";return 3;}}if(!r){++haltedges;continue;}sum+=V(r->s);if(seen.insert(r->s).second)next.push_back(r->s);}
        ++screened;if(!s.empty()&&sum-3*v>worst){worst=sum-3*v;cerr<<"worst="<<worst<<" depth="<<depth<<" s="<<s<<" A/E/B=";for(auto&r:out)cerr<<(r?r->s:"HALT")<<",";cerr<<"\n";if(worst>=0)return 2;}}
        front=move(next);if(depth%5==4||depth==limit-1)cerr<<"depth="<<depth+1<<" seen="<<seen.size()<<" screened="<<screened<<" frontier="<<front.size()<<" haltEdges="<<haltedges<<" worst="<<worst<<"\n";
    }}
