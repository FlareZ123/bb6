// Reproduce the finite mixed-modulus Machine C abstract-graph census.
// This is numerical experimentation, NOT a Lean-certified soundness proof.
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

struct Triple { int a, k, c; };
bool nextC(Triple t, Triple& out) {
  int a=t.a, k=t.k, c=t.c;
  if(c==1){out={a,k+1,0};return true;}
  if(c==2)return false;
  if(c==3){out={a,k+2,1};return true;}
  if(c==0){
    if(a==0){out={1,0,2*k+2};return true;}
    if(a==1 && k==0){out={5,0,1};return true;}
    if(a==1){out={2,2,2*(k-1)+1};return true;}
    out={a-2,1,2*k+1};return true;
  }
  if(a==0){
    if(k%2==0)out={2*k+2,2,c-3};
    else out={2*k+3,0,c};
    return true;
  }
  out={a-1,k+1,c-1};return true;
}
int main(int argc,char**argv) {
  const int M=argc>1?std::atoi(argv[1]):96;
  if(M<8 || M%4!=0 || M>512) return 1;
  const int Mc=M/2, Nc=Mc+2;
  auto idx=[&](Triple t){
    int c=t.c<2?t.c:2+(t.c-2)%Mc;
    return ((t.a%M)*M+t.k%M)*Nc+c;
  };
  std::uint64_t n=(std::uint64_t)M*M*Nc;
  std::vector<std::uint8_t> seen(n,0);
  std::vector<int> queue;
  queue.reserve(n);
  int start=idx({5,0,1});
  seen[start]=1;queue.push_back(start);
  std::uint64_t edges=0;
  for(std::size_t h=0;h<queue.size();++h){
    int i=queue[h],c=i%Nc,k=(i/Nc)%M,a=i/(Nc*M);
    for(int da=0;da<2;da++)for(int dk=0;dk<2;dk++)
      for(int dc=0;dc<(c<2?1:2);dc++){
        Triple t;
        if(!nextC({a+M*da,k+M*dk,c+Mc*dc},t))continue;
        ++edges;
        int j=idx(t);
        if(!seen[j]){seen[j]=1;queue.push_back(j);}
      }
  }
  int period=std::lcm(M,128);
  int lifts=period/M;
  std::uint64_t coneCount=0,coneReach=0;
  for(int x=0;x<M;x++)for(int y=0;y<M;y++){
    bool inCone=false;
    for(int dx=0;dx<lifts&&!inCone;dx++)
      for(int dy=0;dy<lifts;dy++){
        int X=x+dx*M,Y=y+dy*M;
        if(X%8==5 && (2*X+Y)%128==6){inCone=true;break;}
      }
    if(inCone){++coneCount;if(seen[idx({x,y,0})])++coneReach;}
  }
  std::cout<<"M="<<M<<" vertices="<<n<<" reached="<<queue.size()
    <<" edges="<<edges<<" cone-project="<<coneCount
    <<" cone-reached="<<coneReach<<" cone-missed="<<coneCount-coneReach<<"\n";

  // The same authentic m=1 stopping tower used in HighTowerUnbounded.lean.
  // Prints quotient membership; membership never proves concrete reachability.
  for (int depth=0,j=26;depth<3;++depth,j=16*j+42) {
    const int a=2*j+3, k=15*j+40;
    std::cout<<"highTower depth="<<depth<<" j="<<j<<" projected=("
      <<a%M<<","<<k%M<<",0) seen="<<int(seen[idx({a,k,0})])<<"\\n";
  }
  return 0;
}
