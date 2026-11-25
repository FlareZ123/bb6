// Candidate search: abstract failure cubes, independent FAR checking required.
#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include <cassert>
using U=unsigned __int128; using Mask=uint64_t; using M=std::array<int,12>; using D=std::vector<int>;
extern "C" {
using Z=void*; Z Z3_mk_config(); void Z3_del_config(Z); Z Z3_mk_context(Z); void Z3_del_context(Z); Z Z3_mk_solver(Z); void Z3_solver_inc_ref(Z,Z); void Z3_solver_dec_ref(Z,Z); Z Z3_mk_bool_sort(Z); Z Z3_mk_string_symbol(Z,const char*); Z Z3_mk_const(Z,Z,Z); Z Z3_mk_not(Z,Z); Z Z3_mk_or(Z,unsigned,Z const*); void Z3_solver_assert(Z,Z,Z); int Z3_solver_check(Z,Z); Z Z3_solver_get_model(Z,Z); void Z3_model_inc_ref(Z,Z); void Z3_model_dec_ref(Z,Z); bool Z3_model_eval(Z,Z,Z,bool,Z*); int Z3_get_bool_value(Z,Z);
}
int ctz(U x){uint64_t l=x;return l?__builtin_ctzll(l):64+__builtin_ctzll(uint64_t(x>>64));}
U compose(U mask,const U* rows){U v=0;while(mask){int j=ctz(mask);v|=rows[j];mask&=mask-1;}return v;}
struct Rule{int dst,src,off,dep;};struct Result{bool bad;Mask cube;int rounds;};
// Omitting a DFA entry drops every rule requiring it. A derived path to halt
// remains valid in every full DFA extending these entries.
Result far(const M&m,const D&dfa,bool rev,Mask enabled,bool track){
 int d=dfa.size()/2,N=6*d+1,H=N-1;
 U T[254]{}; Rule rules[1024];int nr=0;U halt=U(1)<<H;T[H]=T[N+H]=halt;
 Mask deps[254][127];
 if(track){deps[H][H]=deps[N+H][H]=0;}
 for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
  int x=m[2*q+a],i=a*N+6*l+q;
  if(x<0){T[i]=halt;if(track)deps[i][H]=0;continue;}
  int w=(x>>1)&1,n=x/4;
  if(bool(x&1)!=rev){int dep=2*l+w;if(!(enabled>>dep&1))continue;int to=6*dfa[dep]+n;T[i]=U(1)<<to;if(track)deps[i][to]=Mask(1)<<dep;}
  else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if((enabled>>(2*j+b)&1)&&dfa[2*j+b]==l)rules[nr++]={i,b*N+6*j+n,w*N,2*j+b};
 }
 for(int round=1;;round++){
  U cur=1,seen=0;Mask path[127]{};
  while(cur){seen|=cur;if(seen&halt)return{true,track?path[H]:0,round};
   if(!track){cur=compose(cur,T)&~seen;continue;}
   U next=0;
   while(cur){int j=ctz(cur);cur&=cur-1;U xs=T[j]&~seen;while(xs){int k=ctz(xs);xs&=xs-1;Mask dep=path[j]|deps[j][k];if(!(next>>k&1)||__builtin_popcountll(dep)<__builtin_popcountll(path[k]))path[k]=dep;next|=U(1)<<k;}}
   cur=next;
  }
  bool changed=false;
  for(int j=0;j<nr;j++){
   auto[dst,src,off,dep]=rules[j];U newbits=compose(T[src],T+off)&~T[dst];
   if(!newbits)continue;changed=true;
   if(track){U xs=T[src];U remaining=newbits;while(xs&&remaining){int v=ctz(xs);xs&=xs-1;U bs=T[off+v]&remaining;while(bs){int k=ctz(bs);bs&=bs-1;deps[dst][k]=deps[src][v]|deps[off+v][k]|(Mask(1)<<dep);remaining&=~(U(1)<<k);}}assert(!remaining);}
   T[dst]|=newbits;
  }
  if(!changed)return{false,0,round};
 }
}
M parse(std::string s){M m;std::string t;for(char c:s)if(c!='_')t+=c;assert(t.size()==36);for(int i=0;i<12;i++){auto p=t.data()+3*i;m[i]=p[0]=='-'?-1:4*(p[2]-'A')+2*(p[0]-'0')+(p[1]=='R');}return m;}
struct Solver {
 Z ctx,solver;int d;std::vector<std::vector<Z>> D;
 Solver(int d):d(d),D(2*d,std::vector<Z>(d)){
  Z cfg=Z3_mk_config();ctx=Z3_mk_context(cfg);Z3_del_config(cfg);solver=Z3_mk_solver(ctx);Z3_solver_inc_ref(ctx,solver);Z sort=Z3_mk_bool_sort(ctx);
  for(int i=0;i<2*d;i++)for(int j=0;j<d;j++)D[i][j]=Z3_mk_const(ctx,Z3_mk_string_symbol(ctx,("d"+std::to_string(i)+"_"+std::to_string(j)).c_str()),sort);
  for(int i=0;i<2*d;i++){
   clause(D[i]);for(int a=0;a<d;a++)for(int b=a+1;b<d;b++)clause({neg(D[i][a]),neg(D[i][b])});
   for(int j=1;j<d;j++){
    std::vector<Z> earlier{neg(D[i][j])};for(int k=0;k<i;k++)earlier.push_back(D[k][j-1]);clause(earlier);
   }
  }
  clause({D[0][0]});
  for(int j=1;j<d;j++){std::vector<Z> earlier;for(int k=0;k<2*j;k++)earlier.push_back(D[k][j]);clause(earlier);}
 }
 ~Solver(){Z3_solver_dec_ref(ctx,solver);Z3_del_context(ctx);}
 Z neg(Z z){return Z3_mk_not(ctx,z);}void clause(const std::vector<Z>&v){Z3_solver_assert(ctx,solver,Z3_mk_or(ctx,v.size(),v.data()));}
 int next(std::vector<int>&a){int st=Z3_solver_check(ctx,solver);if(st!=1)return st;Z model=Z3_solver_get_model(ctx,solver);Z3_model_inc_ref(ctx,model);a.assign(2*d,-1);for(int i=0;i<2*d;i++)for(int j=0;j<d;j++){Z v;assert(Z3_model_eval(ctx,model,D[i][j],true,&v));if(Z3_get_bool_value(ctx,v)==1){a[i]=j;break;}}Z3_model_dec_ref(ctx,model);return 1;}
 void block(const std::vector<int>&a,Mask cube){std::vector<Z> v;for(int i=1;i<2*d;i++)if(cube>>i&1)v.push_back(neg(D[i][a[i]]));clause(v);}
};
int main(int argc,char**argv){if(argc<5)return 2;auto m=parse(argv[1]);int d=atoi(argv[2]);bool rev=atoi(argv[3]);int seconds=atoi(argv[4]);assert(d>=1&&d<=20);auto end=std::chrono::steady_clock::now()+std::chrono::seconds(seconds);Solver sol(d);Mask all=(Mask(1)<<(2*d))-1;D a;long it=0,total=0;while(std::chrono::steady_clock::now()<end){int status=sol.next(a);if(status!=1){std::cerr<<(status==-1?"UNSAT":"UNKNOWN")<<" after "<<it<<" cubes\n";return status==-1?1:2;}auto r=far(m,a,rev,all,true);++it;if(!r.bad){assert(!far(m,a,rev,all,false).bad);std::cout<<rev;for(int x:a)std::cout<<"0123456789abcdefghijklmnopqrstuvwxyz"[x];std::cout<<"\n";std::cerr<<"HIT "<<it<<" cubes\n";return 0;}Mask cube=r.cube|1;assert(far(m,a,rev,cube,false).bad);for(int i=1;i<2*d;i++)if((cube>>i&1)&&far(m,a,rev,cube&~(Mask(1)<<i),false).bad)cube&=~(Mask(1)<<i);total+=__builtin_popcountll(cube);sol.block(a,cube);if(it%1000==0)std::cerr<<it<<" cubes avg "<<double(total)/it<<"\n";}std::cerr<<"TIMEOUT "<<it<<" cubes avg "<<(it?double(total)/it:0)<<"\n";return 2;}
