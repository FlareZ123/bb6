// Independent finite M=512 quotient census for the two mixed rectangles.
// This is computational evidence only, not a Lean proof of quotient soundness.
// The exact original-source exclusions are separately formalized in Agent3's
// MixedRectangle27Zero.lean and related files.

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

struct Triple { int a, k, c; };

static bool nextC(Triple t, Triple& out) {
  const int a=t.a, k=t.k, c=t.c;
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
  const int M=argc>1?std::atoi(argv[1]):512;
  if(M<8 || M%4!=0 || M>512) return 1;
  const int Mc=M/2, Nc=Mc+2;
  auto idx=[&](Triple t){
    const int c=t.c<2?t.c:2+(t.c-2)%Mc;
    return ((t.a%M)*M+t.k%M)*Nc+c;
  };

  const std::uint64_t n=(std::uint64_t)M*M*Nc;
  std::vector<std::uint8_t> seen(n,0);
  std::vector<int> queue;
  queue.reserve(n/3);
  const int start=idx({5,0,1});
  seen[start]=1;
  queue.push_back(start);

  std::uint64_t edges=0;
  for(std::size_t h=0;h<queue.size();++h){
    const int i=queue[h], c=i%Nc, k=(i/Nc)%M, a=i/(Nc*M);
    for(int da=0;da<2;da++)
      for(int dk=0;dk<2;dk++)
        for(int dc=0;dc<(c<2?1:2);dc++){
          Triple t;
          if(!nextC({a+M*da,k+M*dk,c+Mc*dc},t)) continue;
          ++edges;
          const int j=idx(t);
          if(!seen[j]){seen[j]=1;queue.push_back(j);}
        }
  }

  std::uint64_t rect27=0,rect27Seen=0,rect25=0,rect25Seen=0;
  for(int x=0;x<M;x++)
    for(int y=0;y<M;y++){
      if(x%32==27 && y%32==0){
        ++rect27;
        if(seen[idx({x,y,0})]) ++rect27Seen;
      }
      if(x%32==25 && y%32==4){
        ++rect25;
        if(seen[idx({x,y,0})]) ++rect25Seen;
      }
    }

  std::cout<<"M="<<M<<" vertices="<<n
           <<" reached="<<queue.size()<<" edges="<<edges<<"\n";
  std::cout<<"rect27 cells="<<rect27
           <<" quotient-admitted="<<rect27Seen
           <<" excluded="<<rect27-rect27Seen<<"\n";
  std::cout<<"rect25 cells="<<rect25
           <<" quotient-admitted="<<rect25Seen
           <<" excluded="<<rect25-rect25Seen<<"\n";
  std::cout<<"sample rect27 (59,480,0)="
           <<int(seen[idx({59,480,0})])<<"\n";
  std::cout<<"sample rect25 (25,484,0)="
           <<int(seen[idx({25,484,0})])<<"\n";
}
