#include <bits/stdc++.h>
using namespace std;
struct Snap{int q,h;bitset<512>ones;};struct Res{int kind,slot,t;vector<Snap>hist;};
bitset<512>Rm[512],Lm[512];
void init(){for(int b=0;b<512;b++)for(int i=0;i<512;i++){if(i>=b)Rm[b].set(i);if(i<=b)Lm[b].set(i);}}
Res trace(const array<int,12>&p){int q=0,h=0;bitset<512>o;vector<Snap>H;H.reserve(101);for(int t=0;t<=100;t++){H.push_back({q,h,o});int z=h+256,s=2*q+(o[z]?1:0),a=p[s];if(a<=1)return{a==0?0:1,s,t,move(H)};int v=a-2;o.set(z,v>=12);q=v%6;h+=v%12>=6?1:-1;}return{2,-1,101,move(H)};}
bool side(const vector<Snap>&H){int me=min<int>(H.size(),60);for(int e=0;e<me;e++){int rmin=INT_MAX,lmax=INT_MIN;for(int j=e+1;j<min<int>(H.size(),e+31);j++){int hp=H[j-1].h;rmin=min(rmin,hp);lmax=max(lmax,hp);auto&a=H[e];auto&b=H[j];int d=b.h-a.h;if(a.q!=b.q)continue;for(int rr=0;rr<2;rr++){bool right=rr==0;if(right?d<0:d>0)continue;int bd=right?rmin:lmax,bi=bd+256;auto sh=d>=0?(b.ones>>d):(b.ones<<(-d));if((((a.ones^sh)&(right?Rm[bi]:Lm[bi])).none()))return true;}}}return false;}
long long pw[9];
struct S{long long residual=0,nodes=0,cycle=0,halt=0,longc=0,open=0;};
void go(array<int,12>&p,int depth,S&st){st.nodes++;auto r=trace(p);if(side(r.hist)){st.cycle++;return;}if(r.kind==1){st.halt++;return;}if(r.kind==2){st.longc++;st.residual+=pw[8-depth];return;}if(depth>=6){st.open++;st.residual+=pw[8-depth];return;}int s=r.slot;for(int c=1;c<=25;c++){p[s]=c;go(p,depth+1,st);}p[s]=0;}
int main(){init();pw[0]=1;for(int i=1;i<=8;i++)pw[i]=pw[i-1]*25;vector<tuple<long long,int,int,S>>all;int ds[4]={7,19,13,25};
#pragma omp parallel for schedule(dynamic)
for(int ix=0;ix<100;ix++){int di=ix/25,f=ix%25+1;array<int,12>p={21,0,22,0,11,0,16,0,0,0,0,0};p[7]=ds[di];p[10]=f;S st;go(p,2,st);
#pragma omp critical
all.emplace_back(st.residual,ds[di],f,st);}
sort(all.begin(),all.end(),[](auto&a,auto&b){return get<0>(a)<get<0>(b);});
for(auto&[r,d,f,s]:all)cout<<r<<" d="<<d<<" f="<<f<<" nodes="<<s.nodes<<" cyc="<<s.cycle<<" halt="<<s.halt<<" long="<<s.longc<<" open="<<s.open<<"\n";
}
