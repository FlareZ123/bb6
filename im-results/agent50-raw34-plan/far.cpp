#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <vector>
using namespace std;
using U=uint64_t;
using Table=array<int,12>;
using Dfa=vector<int>;
vector<Dfa> dfs[11];
void enumerate(int d, Dfa& p, int mx) {
    if((int)p.size()==2*d){if(mx+1==d)dfs[d].push_back(p);return;}
    if((int)p.size()/2>mx)return;
    for(int x=0;x<=min(d-1,mx+1);x++){p.push_back(x);enumerate(d,p,max(mx,x));p.pop_back();}
}
struct Rule { int dst,src,off; };
struct Cert { vector<U> rows; U z; };
U zeroClosure(const vector<U>& rows,int n) {
    U z=U(1)<<(n-1);
    while(true){U old=z;for(int i=0;i<n;i++)if(rows[i]&z)z|=U(1)<<i;if(z==old)return z;}
}
bool synth(const Table& p, const Dfa& dfa, bool reflect, Cert& out){
    int d=dfa.size()/2,n=6*d+1,H=n-1;U halt=U(1)<<H;
    vector<U> rows(2*n);vector<Rule> rules;rules.reserve(6*d*4);
    rows[H]=rows[n+H]=halt;
    for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
        int dst=a*n+6*l+q,v=p[2*q+a];
        if(v<2){rows[dst]=halt;continue;}
        v-=2;int w=v/12,r=(v/6)%2,next=v%6;
        if(reflect)r^=1;
        if(r)rows[dst]=U(1)<<(6*dfa[2*l+w]+next);
        else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l)rules.push_back({dst,b*n+6*j+next,w*n});
    }
    for(;;){U z=zeroClosure(rows,n);if(z&1)return false;
        bool change=false;
        for(auto [dst,src,off]:rules){U x=rows[dst],s=rows[src];while(s){int j=__builtin_ctzll(s);s&=s-1;x|=rows[off+j];}if(x!=rows[dst]){rows[dst]=x;change=true;}}
        if(!change){out={move(rows),z};return true;}
    }
}
void printVector(const Dfa& a){cout<<'[';for(int i=0;i<(int)a.size();i++){if(i)cout<<',';cout<<a[i];}cout<<']';}
void printRows(const vector<U>& a,int begin,int end){cout<<'[';for(int i=begin;i<end;i++){if(i!=begin)cout<<',';cout<<a[i];}cout<<']';}
int main(int argc,char**argv){int limit=argc>1?atoi(argv[1]):4;if(limit<1||limit>6)return 2;for(int d=1;d<=limit;d++){Dfa p={0};enumerate(d,p,0);cerr<<"DFA "<<d<<" "<<dfs[d].size()<<'\n';}int id;Table p;int count=0,success=0;while(cin>>id){for(auto&x:p)cin>>x;bool found=false;Cert c;for(int d=1;d<=limit&&!found;d++)for(int r=0;r<2&&!found;r++)for(const auto& a:dfs[d])if(synth(p,a,r,c)){cout<<"{\"id\":"<<id<<",\"d\":"<<d<<",\"reflect\":"<<(r?"true":"false")<<",\"dfa\":";printVector(a);cout<<",\"m0\":";printRows(c.rows,0,6*d+1);cout<<",\"m1\":";printRows(c.rows,6*d+1,12*d+2);cout<<",\"z\":"<<c.z<<"}\n";found=true;success++;break;}if(!found)cout<<"{\"id\":"<<id<<"}\n";count++;if(count%100==0)cerr<<count<<" / "<<success<<'\n';}cerr<<"Final "<<count<<" / "<<success<<'\n';}
