// Build: g++ -O3 -std=c++17 -march=native laggroup.cpp -o laggroup
// Usage: ./laggroup n K [block]; positive END is a certified computational extinction horizon.
#define main lagblock_main
#include "lagblock.cpp"
#undef main
#include <numeric>
#include <map>
struct DSU{vector<int> p;DSU(int n):p(n){iota(p.begin(),p.end(),0);}int find(int x){while(p[x]!=x){p[x]=p[p[x]];x=p[x];}return x;}void unite(int x,int y){x=find(x);y=find(y);if(x!=y)p[y]=x;}};
vector<int> extract(const Bits&z){vector<int> out;for(int j=0;j<z.w;j++){U v=z.a[j];while(v){int b=__builtin_ctzll(v);out.push_back(j*64+b);v&=v-1;}}return out;}
void init(Bits&z,const vector<int>&cs){fill(z.a.begin(),z.a.end(),0);z.w=0;for(int v:cs){z.a[v/64]|=1ULL<<(v%64);z.w=max(z.w,v/64+1);}}
struct Group{string x,y;int c,r;vector<int> ends;};
struct Stats{long long reverse=0,forward=0,groups=0;int peak=1,maxgap=0;};
int runGroup(int n,int K,int block){
 if(n<14||n%2||K<=n||block<1||n>100000000||K>100000000)return -1;
 int S=K-n;
 auto start=chrono::steady_clock::now();auto sec=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 U A=n+K+2,L=2*(n+3*K+10)+6; // n,K <= 1e8 => A*L <= 1.6e17
 U prod=A*L;auto safe=[&](int g){int e=n-g;return e>=62||(e>=0&&(U(6)<<e)>prod);};
 if((n<63&&A>(U(1)<<n))||!safe(0))return -3;
 Bits z(n+K+200);z.init((n+2)/2);Stats st;
 for(int i=1;i<n+1;i++){st.forward++;if(!z.step(n+i+3,i==n?1:0))return i+1;}
 if(!safe(1))return -3;
 vector<Group> live={{"1","1",(n+2)/2,3,extract(z)}};
 cout<<"n="<<n<<" width(n+1)="<<live[0].ends.size()<<" first phase sec="<<sec()<<endl;
 int death=0;
 for(int s=1;s<S;){int h=min({block,n,S-s});vector<Group> next;
  for(auto &g:live){
   auto &ends=g.ends;DSU dsu(ends.size());vector<pair<int,int>> p,q,a,b;
   for(int i=0;i<(int)ends.size();i++)p.emplace_back(ends[i],i);
   auto bit=[&](int i){return i<n?0:g.y[i-n]-'0';};
   // Reverse merge to the split layer. Each terminal carry determines one predecessor.
   for(int i=n+s-1;i>=s+h;i--){int C=n+i+3,y=bit(i);a.clear();b.clear();q.clear();st.reverse+=p.size();
    for(auto [c,id]:p){int t=2*c+y;if(t>=2*C)return -4;if(t<C)a.emplace_back(t,id);else b.emplace_back(t-C,id);}
    auto l=a.begin(),r=b.begin();while(l!=a.end()||r!=b.end()){
     if(r==b.end()||(l!=a.end()&&l->first<r->first))q.push_back(*l++);
     else if(l==a.end()||r->first<l->first)q.push_back(*r++);
     else{dsu.unite(l->second,r->second);q.push_back(*l++);r++;}
    }
    p.swap(q);
   }
   map<int,vector<int>> parts;for(int j=0;j<(int)ends.size();j++)parts[dsu.find(j)].push_back(ends[j]);
   st.groups+=p.size();
   for(auto [aend,id]:p){int c=aend;string extra(h,'0');
    for(int i=s+h-1;i>=s;i--){int C=n+i+3,t=2*c+bit(i);if(t>=2*C)return -4;if(t>=C){extra[i-s]='1';t-=C;}c=t;}
    if(c!=g.c)return -5;
    init(z,parts[dsu.find(id)]);
    string y=g.y;int r=g.r,last=y.back()-'0',run=0;for(int j=s-1;j>=0&&g.y[j]==g.y.back();j--)run++;
    bool ok=true;for(int j=0;j<h;j++){int t=r+7*(extra[j]-'0'),v=t%2;r=t/2;y+=char('0'+v);run=v==last?run+1:1;last=v;int gap=min(s+j+1,run+1);st.maxgap=max(st.maxgap,gap);st.forward++;
     if(!z.step(2*n+s+j+3,v)){death=max(death,n+s+j+1);ok=false;break;}
     if(!safe(gap)){cerr<<"margin failed at "<<n+s+j+1<<endl;return -3;}
    }
    if(ok)next.push_back({g.x+extra,move(y),aend,r,extract(z)});
   }
  }
  s+=h;live=move(next);st.peak=max(st.peak,int(live.size()));
  cout<<"s="<<s<<" live="<<live.size()<<" peak="<<st.peak<<" groups="<<st.groups<<" reverse="<<st.reverse<<" forward="<<st.forward<<" gap="<<st.maxgap<<" sec="<<sec()<<endl;
  if(live.empty())return death;
 }
 return 0;
}
int main(int argc,char**argv){
 if(argc<3||argc>4){cerr<<"usage: laggroup n K [block]"<<endl;return 2;}
 int n=stoi(argv[1]),K=stoi(argv[2]),b=argc>3?stoi(argv[3]):max(1,n/8);
 int r=runGroup(n,K,b);cout<<"END "<<n<<" "<<r<<endl;return r>0?0:1;
}
