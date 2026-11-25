#include <array>
#include <vector>
#include <iostream>
#include <algorithm>
#include <cstdint>
using namespace std;using U=uint64_t; using M=array<int,12>;using D=vector<int>;
struct Rule{int dst,src,off;};struct Result{bool safe;int rounds;vector<U> rows;U z;};
U compose(U mask,const U* rows){U v=0;while(mask){int j=__builtin_ctzll(mask);v|=rows[j];mask&=mask-1;}return v;}
Result far(const M&m,const D&dfa,bool rev){int d=dfa.size()/2,N=6*d+1,H=N-1;U T[122]{};vector<Rule>rules;U halt=U(1)<<H;T[H]=T[N+H]=halt;for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){int x=m[2*q+a],i=a*N+6*l+q;if(x==24){T[i]=halt;continue;}int w=(x>>1)&1,n=x/4;if(bool(x&1)!=rev)T[i]=U(1)<<(6*dfa[2*l+w]+n);else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l)rules.push_back({i,b*N+6*j+n,w*N});}for(int round=1;;round++){U cur=1,seen=0;while(cur){seen|=cur;if(seen&halt)return{false,round,{},0};cur=compose(cur,T)&~seen;}bool changed=false;for(auto [dst,src,off]:rules){U x=T[dst]|compose(T[src],T+off);if(x!=T[dst]){T[dst]=x;changed=true;}}if(!changed){U z=halt;for(;;){U z1=z;for(int i=0;i<N;i++)if(T[i]&z)z1|=U(1)<<i;if(z==z1)break;z=z1;}return{true,round,vector<U>(T,T+2*N),z};}}}
void enumerate(int d,D&a,int mx,vector<D>&out){if(int(a.size())==2*d){if(mx==d-1)out.push_back(a);return;}if(int(a.size()/2)>mx)return;for(int j=0;j<=min(d-1,mx+1);j++){a.push_back(j);enumerate(d,a,max(j,mx),out);a.pop_back();}}
int main(int argc,char**argv){int maxd=argc>1?atoi(argv[1]):5;if(maxd<1||maxd>9)return 1;vector<D>ds;for(int d=1;d<=maxd;d++){D a{0};enumerate(d,a,0,ds);}cerr<<"dfas "<<ds.size()<<endl;int id;while(cin>>id){M m;for(auto &v:m)cin>>v;bool found=false;for(auto &d:ds){for(int rev=0;rev<2;rev++){auto r=far(m,d,rev);if(!r.safe)continue;cout<<id<<" "<<rev<<" "<<d.size()/2;for(int x:d)cout<<" "<<x;for(U x:r.rows)cout<<" "<<x;cout<<" "<<r.z<<endl;found=true;break;}if(found)break;}if(!found)cout<<id<<" -1"<<endl;}}
