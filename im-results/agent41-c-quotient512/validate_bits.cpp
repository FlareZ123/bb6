#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <sys/mman.h>
#include <vector>
using namespace std;

int main(int argc, char **argv) {
 const int m=argc==2 ? atoi(argv[1]) : 1024, n=8+m, count=n*n*n;
 auto q=[=](int x)->int {return x<8 ? x : (x-8)%m+8;};
 auto code=[=](int a,int k,int c)->int {return a*n*n + k*n + c;};
 vector<uint64_t> membership(((size_t)count+63)/64);
 auto contains=[&](int i)->bool {return (membership[i>>6]>>(i&63))&1;};
 auto insert=[&](int i)->bool {uint64_t &word=membership[i>>6];uint64_t bit=1ull<<(i&63);bool fresh=!(word&bit);word|=bit;return fresh;};
 int *queue=(int*)mmap(nullptr,(size_t)count*4,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
 if(queue==MAP_FAILED)abort();
 int front=0,back=0;uint64_t examined=0;
 insert(code(5,0,1));queue[back++]=code(5,0,1);
 for (;front<back;++front) {
  const int id=queue[front],a=id/(n*n),k=id/n%n,c=id%n;
  const int av[2]={a,a+m},kv[2]={k,k+m},cv[2]={c,c+m};
  for(int ai=0;ai<(a<8?1:2);++ai)
   for(int ki=0;ki<(k<8?1:2);++ki)
    for(int ci=0;ci<(c<8?1:2);++ci) {
     int A=av[ai],K=kv[ki],C=cv[ci],aa=0,kk=0,cc=0;
     if(C==2)continue;
     if(C==1 || C==3) {aa=A;kk=K+(C==1?1:2);cc=C==1?0:1;}
     else if(C==0) {
      if(A==0){aa=1;kk=0;cc=2*K+2;}
      else if(A==1) {aa=K==0?5:2;kk=K==0?0:2;cc=K==0?1:2*K-1;}
      else {aa=A-2;kk=1;cc=2*K+1;}
     } else if(A==0) {
      if((K&1)==0){aa=2*K+2;kk=2;cc=C-3;}
      else {aa=2*K+3;kk=0;cc=C;}
     } else {aa=A-1;kk=K+1;cc=C-1;}
     ++examined;
     int out=code(q(aa),q(kk),q(cc));
     if(insert(out))queue[back++]=out;
    }
 }
 printf("M=%d reached=%d edges=%llu\n",m,back,(unsigned long long)examined);
 printf("reset=");for(int j=0;j<m;++j)if(!contains(code(q(2*(j+m)+1),q(3*(j+m)+4),0)))printf("%d,",j);
 printf("\nside=");for(int j=0;j<m;++j)if(!contains(code(0,q(4*(j+m)),q(24*(j+m)+23))))printf("%d,",j);
 printf("\n");
 munmap(queue,(size_t)count*4);
}
