#include <iostream>
#include <string>
#include <vector>
#include <array>
#include <algorithm>
using namespace std;
// Emit freshly visited boundary configurations in the zipper convention.
int main(int argc,char**argv){
 int N=argc>1?stoi(argv[1]):1000000,E=argc>2?stoi(argv[2]):140;
 vector<unsigned char> tape(2*N+3);int id;string s;
 while(cin>>id>>s){
  string p=s;p.erase(remove(p.begin(),p.end(),'_'),p.end());array<int,12> a;
  for(int i=0;i<12;i++){int j=3*i;a[i]=p[j]=='-'?-1:4*(p[j+2]-'A')+2*(p[j]-'0')+(p[j+1]=='R');}
  int q=0,h=N+1,lo=h,hi=h,count=0;cout<<id<<' '<<s<<'\n';
  for(int t=0;t<N&&count<E;t++){
   if(h<lo||h>hi){
    bool left=h<lo;lo=min(lo,h);hi=max(hi,h);cout<<t<<' '<<(left?'L':'R')<<' '<<q<<' '<<h-(N+1)<<' ';
    if(left){cout<<"- ";for(int j=h+1;j<=hi;j++)cout<<int(tape[j]);}
    else{for(int j=h;j>=lo;j--)cout<<int(tape[j]);cout<<" -";}
    cout<<'\n';++count;
   }
   int slot=2*q+tape[h],x=a[slot];if(x<0)break;tape[h]=(x>>1)&1;h+=(x&1)?1:-1;q=x/4;
  }
  fill(tape.begin()+min(lo,h),tape.begin()+max(hi,h)+1,0);cout<<"end\n";
 }
}
