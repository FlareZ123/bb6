#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 int M=argc>1?atoi(argv[1]):64, N=M+8, Z=N*N*N;
 auto q=[=](int x){return x<8?x:8+(x-8)%M;};
 auto idx=[=](int a,int k,int c){return (a*N+k)*N+c;};
 vector<uint8_t> seen(Z,0);vector<int> queue(Z);
 int head=0,tail=0;uint64_t edges=0;int entry=idx(5,0,1);seen[entry]=1;queue[tail++]=entry;
 while(head<tail){
  int s=queue[head++];int c=s%N,k=(s/N)%N,a=s/(N*N);
  for(int i=0;i<(a<8?1:2);i++)for(int j=0;j<(k<8?1:2);j++)for(int h=0;h<(c<8?1:2);h++){
   int A=a+i*M,K=k+j*M,C=c+h*M,U,V,W;
   if(C==1){U=A;V=K+1;W=0;}
   else if(C==2)continue;
   else if(C==3){U=A;V=K+2;W=1;}
   else if(C==0){
    if(A==0){U=1;V=0;W=2*K+2;}
    else if(A==1){if(K==0){U=5;V=0;W=1;}else{U=2;V=2;W=2*K-1;}}
    else{U=A-2;V=1;W=2*K+1;}
   }else if(A==0){if(K%2==0){U=2*K+2;V=2;W=C-3;}else{U=2*K+3;V=0;W=C;}}
   else{U=A-1;V=K+1;W=C-1;}
   int t=idx(q(U),q(V),q(W));edges++;
   if(!seen[t]){seen[t]=1;queue[tail++]=t;}
  }
 }
 printf("M=%d reached=%d edges=%llu\n",M,tail,(unsigned long long)edges);
 printf("reset=");for(int r=0;r<M;r++)if(!seen[idx(q(2*(M+r)+1),q(3*(M+r)+4),0)])printf("%d,",r);
 printf("\nside=");for(int r=0;r<M;r++)if(!seen[idx(0,q(4*(M+r)),q(24*(M+r)+23))])printf("%d,",r);
 printf("\n");
}
