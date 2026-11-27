#include <bit>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <chrono>
using U=uint64_t;
struct State{U x,y,spent,depth;};
struct Report{bool ok; U count,req,depth,maxx,maxy; State last; const char *reason;};
Report check(U w,U limit){
  U z=1360+22155*w,budget=201+3360*w;
  std::vector<State> work{{44*z+211,42*z+211,0,0}};
  U steps=0, req=0, dep=0,maxx=0,maxy=0; State s{};
  while(!work.empty()){
    s=work.back();work.pop_back();
    auto [x,y,spent,d]=s;
    steps++;dep=std::max(dep,d);maxx=std::max(maxx,x);maxy=std::max(maxy,y);
    if(steps>limit)return {false,steps,req,dep,maxx,maxy,s,"limit"};
    U p=(x+y)%2,q=x+y-211*p;
    if(!x||!y||!q||x+y<211*p)return {false,steps,req,dep,maxx,maxy,s,"invalid"};
    U need=std::bit_width(212*(x+y+1688));
    req=std::max(req,need+spent);
    if(req>budget)return {false,steps,req,dep,maxx,maxy,s,"budget"};
    if(y%2&&((x+y)%4==1||(x+y)%4==2))continue;
    U v=std::countr_zero(q);
    req=std::max(req,v+1+spent);
    if(req>budget)return {false,steps,req,dep,maxx,maxy,s,"budget"};
    if(y%2==0)work.push_back({x+y+422,(y+422)/2,spent+1,d+1});
    for(U n=(x+1+p)%2;n+2<=v;n+=2){
      U a=(q>>(n+1))+211*(2+p), k=x+2*y+211*(7+3*n)-a;
      if(k%2)return {false,steps,req,dep,maxx,maxy,s,"bad parity"};
      work.push_back({a,k/2,spent+n+2,d+1});
    }
  }
  return {true,steps,req,dep,maxx,maxy,s,"ok"};
}
int main(int argc,char **argv){
  U limit=argc>1?strtoull(argv[1],nullptr,10):1000000000;
  std::vector<U> ws{3141,3361,4081,6097,6465};
  for(int i=2;i<argc;i++)ws.push_back(strtoull(argv[i],nullptr,10));
  for(auto w:ws){auto start=std::chrono::steady_clock::now();auto r=check(w,limit);printf("w=%llu %s nodes=%llu req=%llu depth=%llu max=(%llu,%llu) last=(%llu,%llu) sec=%.3f\n",(unsigned long long)w,r.reason,(unsigned long long)r.count,(unsigned long long)r.req,(unsigned long long)r.depth,(unsigned long long)r.maxx,(unsigned long long)r.maxy,(unsigned long long)r.last.x,(unsigned long long)r.last.y,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());fflush(stdout);}
}
