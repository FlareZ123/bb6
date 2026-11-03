#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

// Exact branches of the published BB6CLine.nextC map.
// Research status: numerical quotient experiment. A kernel proof of
// all-natural quotient soundness and graph closure is NOT included.
struct Triple {int a,k,c;};
bool nextC(Triple t, Triple &o) {
  int a=t.a,k=t.k,c=t.c;
  if(c==1){o={a,k+1,0};return true;}
  if(c==2)return false;
  if(c==3){o={a,k+2,1};return true;}
  if(c==0){
    if(a==0){o={1,0,2*k+2};return true;}
    if(a==1 && k==0){o={5,0,1};return true;}
    if(a==1){o={2,2,2*(k-1)+1};return true;}
    o={a-2,1,2*k+1};return true;
  }
  if(a==0){
    if(k%2==0)o={2*k+2,2,c-3};
    else o={2*k+3,0,c};
    return true;
  }
  o={a-1,k+1,c-1};return true;
}
struct Quotient {
  static constexpr int Ma=96,Mk=96,Mc=48;
  static constexpr int Ba=0,Bk=0,Bc=2;
  static constexpr int Na=Ma+Ba,Nk=Mk+Bk,Nc=Mc+Bc;
  static constexpr int N=Na*Nk*Nc;
  std::vector<uint8_t> seen=std::vector<uint8_t>(N,0);
  uint64_t edges=0;
  uint32_t reached=0;
  static int q(int x,int B,int M){return x<B?x:B+(x-B)%M;}
  static int qa(int x){return q(x,Ba,Ma);}
  static int qk(int x){return q(x,Bk,Mk);}
  static int qc(int x){return q(x,Bc,Mc);}
  static int index(int a,int k,int c){return (a*Nk+k)*Nc+c;}
  static int index(Triple s){return index(qa(s.a),qk(s.k),qc(s.c));}
  bool reached_triple(Triple s)const{return seen[index(s)];}
  void run(){
    std::vector<int> queue;queue.reserve(300000);
    const int origin=index({5,0,1});seen[origin]=1;queue.push_back(origin);
    for(size_t head=0;head<queue.size();head++){
      int i=queue[head],c=i%Nc,k=(i/Nc)%Nk,a=i/(Nk*Nc);
      int nrA=a>=Ba?2:1,nrK=k>=Bk?2:1,nrC=c>=Bc?2:1;
      for(int da=0;da<nrA;da++)for(int dk=0;dk<nrK;dk++)for(int dc=0;dc<nrC;dc++){
        Triple out;
        if(!nextC({a+da*Ma,k+dk*Mk,c+dc*Mc},out))continue;
        edges++;
        int j=index(out);
        if(!seen[j]){seen[j]=1;queue.push_back(j);}
      }
    }
    reached=queue.size();
  }
  static int powmod(int e,int M){
    int r=1,b=2%M;
    while(e){if(e&1)r=(r*b)%M;b=(b*b)%M;e>>=1;}
    return r;
  }
  static int normalize_mod(int x,int M){return (x%M+M)%M;}
  Triple second_halt(int j,int m)const{
    int k=normalize_mod(powmod(2*m+2,Mk)*(j+3)-(j+3*m+5),Mk);
    return {2*j+3,k+Mk,0};
  }
};
int main(){
  Quotient q;q.run();
  std::cout<<"BB6CLine mixed quotient (Ba,Bk,Bc)=(0,0,2), "
           <<"(Ma,Mk,Mc)=(96,96,48)\n";
  std::cout<<"vertices="<<Quotient::N<<" reached="<<q.reached
           <<" successor_edges="<<q.edges<<"\n";
  std::array<Triple,5> tests={Triple{13,31,0},Triple{29,79,0},
                              Triple{61,79,0},Triple{77,31,0},Triple{5,0,1}};
  for(Triple t:tests)std::cout<<"projected ("<<t.a<<","<<t.k<<","<<t.c
                            <<") reached="<<q.reached_triple(t)<<"\n";
  int missing=0,first_count=0;
  for(int j=0;j<96;j++)for(int m=0;m<96;m++){
    Triple t=q.second_halt(j+4*96,m+4*96);
    if(!q.reached_triple(t)){
      missing++;
      if(first_count<24){std::cout<<"missing pair "<<j<<","<<m
        <<" abstract "<<Quotient::qa(t.a)<<","<<Quotient::qk(t.k)<<","<<Quotient::qc(t.c)<<"\n";first_count++;}
    }
  }
  std::cout<<"missing j,m torus positions mod96="<<missing<<"/9216\n";
  return 0;
}
