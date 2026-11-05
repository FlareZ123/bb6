// Independent 384/192 abstract reverse-graph audit for original BB6CLine.nextC.
// Abstract state (a mod384, k mod384, c=0|1|2+(c mod192) for c>=2).
// Every actual CLine edge is represented; an abstract path need not lift as one
// consistent real orbit. In particular, "hit" is NEVER a halting witness.
#include <cstdint>
#include <vector>
#include <iostream>
#include <string>
using namespace std;
static constexpr int M=384,H=192,Q=M*M,N=194*Q;
static inline int enc(int a,int k,int cc){return cc*Q+a*M+k;}
static inline int mod(int x,int m){int r=x%m;return r<0?r+m:r;}
struct Result{int64_t popped; int64_t low0,low1,high; bool hit;int plen;};
Result rev(int rootk,int m,bool printPath){
 vector<uint8_t>seen(N,0);
 vector<int32_t>parent(N,-1);
 vector<int32_t>que;que.reserve(N);
 int target=enc(1,rootk,0),blank=enc(5,0,1);
 seen[target]=1;que.push_back(target);
 int64_t ct[3]={0,0,0};
 for(size_t head=0;head<que.size();head++){
   int x=que[head],cc=x/Q,v=x%Q,a=v/M,k=v%M;
   ct[(cc<2)?cc:2]++;
   auto add=[&](int aa,int kk,int ccc)->bool{
     int y=enc(aa,kk,ccc);
     if(seen[y]) return false;
     seen[y]=1;parent[y]=x;que.push_back(y);
     return y==blank;
   };
   bool hit=false;
   if(cc==0){hit=add(a,(k+M-1)%M,1);}
   else if(cc==1){
       if(a==5&&k==0)hit|=add(1,0,0);
       if(a==2&&k==2)hit|=add(1,1,0);
       if(k==1)hit|=add((a+2)%M,0,0);
       hit|=add(a,(k+M-2)%M,5);
       if(k==2&&mod(a-2,M)%2==0){int z=mod(a-2,M)/2;
         if(z%2==0)hit|=add(0,z,6);
         if((z+M/2)%2==0)hit|=add(0,z+M/2,6);
       }
   } else {
      int c=cc-2;
      hit|=add((a+1)%M,(k+M-1)%M,2+(c+1)%H);
      if(a==1&&k==0&&c%2==0){int z=mod(c-2,H)/2;for(int i=0;i<4;i++)hit|=add(0,z+96*i,0);}
      if(a==2&&k==2&&c%2==1){int z=mod(c+1,H)/2;for(int i=0;i<4;i++)hit|=add(1,z+96*i,0);}
      if(k==1&&c%2==1){int z=mod(c-1,H)/2;for(int i=0;i<4;i++)hit|=add((a+2)%M,z+96*i,0);}
      if(k==2&&mod(a-2,M)%2==0){int z=mod(a-2,M)/2;
         if(z%2==0)hit|=add(0,z,2+(c+3)%H);
         if((z+M/2)%2==0)hit|=add(0,z+M/2,2+(c+3)%H);
      }
      if(k==0&&mod(a-3,M)%2==0){int z=mod(a-3,M)/2;
         if(z%2==1)hit|=add(0,z,cc);
         if((z+M/2)%2==1)hit|=add(0,z+M/2,cc);
      }
   }
   if(hit){
     vector<int> path;int current=blank;
     while(current>=0){path.push_back(current);current=parent[current];}
     if(printPath){
       cout<<"PATH_BEGIN m="<<m<<"\n";
       for(int p:path)cout<<(p%Q)/M<<'\t'<<p%M<<'\t'<<p/Q<<'\n';
       cout<<"PATH_END m="<<m<<"\n";
     }
     return {(int64_t)head+1,ct[0],ct[1],ct[2],true,(int)path.size()};
   }
 }
 return {(int64_t)que.size(),ct[0],ct[1],ct[2],false,0};
}
int main(int argc,char** argv){
 bool printPath=argc>1&&string(argv[1])=="--paths";
 for(int m: {3,19,35,51,67,83,99,115}){
  int k=mod(124-3*m,M);auto r=rev(k,m,printPath);
  cout<<"m="<<m<<" k="<<k<<" popped="<<r.popped<<" counts="<<r.low0<<","<<r.low1<<","<<r.high<<" hit="<<r.hit<<" pathlen="<<r.plen<<endl;
 }
}
