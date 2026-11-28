// Finite computational exploration ONLY (not a proof of NeverHalts).
// Pin the source literal and check a five-phase exponential frontier pattern.
// Compiler: g++ -O3 -std=c++17 -Wall -Wextra. Reproducible deterministic code.
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
using namespace std;
static const string table="1RB---_1RC1LC_0RD1RF_0LD0RE_1LB1RA_1RE0LF";
constexpr uint64_t MAX_STEPS=400000000ULL;
constexpr int64_t CENTER=1000;
constexpr int64_t CELLS=3000;
int main(){
 string raw;for(char c:table)if(c!='_')raw+=c;
 if(raw.size()!=36)return 2;
 array<int,12> w{},dir{},next{};
 for(int i=0;i<12;i++){
   string x=raw.substr(3*i,3);
   if(x=="---"){w[i]=-1;continue;}
   if(x[0]<'0'||x[0]>'1'||(x[1]!='L'&&x[1]!='R')||
      x[2]<'A'||x[2]>'F')return 2;
   w[i]=x[0]-'0';dir[i]=x[1]=='R'?1:-1;next[i]=x[2]-'A';
 }
 vector<uint8_t> tape(CELLS,0);
 int64_t head=CENTER,lo=0,hi=0;
 int state=0,passed=0;
 uint64_t ones=0;
 const auto expected=[&](uint64_t k){
   uint64_t p=1;for(uint64_t j=1;j<k;j++)p*=16;
   return 352*p-20*k-16;
 };
 for(uint64_t step=1;step<=MAX_STEPS;step++){
   int i=2*state+tape[head];
   if(w[i]<0){
     cout<<"QUERY_UNDEFINED before_step="<<step<<" state="<<state
         <<" head="<<head-CENTER<<" passed_frontier_milestones="<<passed<<"\n";
     return 3;
   }
   if(tape[head] != w[i]){
     ones+=w[i]?1:-1;
     tape[head]=static_cast<uint8_t>(w[i]);
   }
   head+=dir[i];state=next[i];
   if(head<100 || head>=CELLS-100)return 4;
   int64_t x=head-CENTER;
   lo=min(lo,x);
   if(x>hi){
      hi=x;
      if(hi>=20 && hi%20==0){
        uint64_t k=static_cast<uint64_t>(hi/20);
        bool shape=(state==2 && ones==static_cast<uint64_t>(hi-1));
        for(int64_t j=-3;j<=hi+2;j++){
          int bit=(j>=0 && j<=2) || (j>=4 && j<hi);
          if(tape[CENTER+j]!=bit){shape=false;break;}
        }
        uint64_t formula=expected(k);
        cout<<"FRONTIER k="<<k<<" right="<<hi<<" steps="<<step
            <<" expected="<<formula<<" state=C:"<<int(state==2)
            <<" shape="<<int(shape)<<" ones="<<ones
            <<" left_min="<<lo<<"\n";
        if(!shape || step!=formula){
           cout<<"PATTERN_COUNTEREXAMPLE\n";return 5;
        }
        passed++;
        if(k==6){
           cout<<"EMPIRICAL_MACRO_PATTERN_ACCEPTED six checkpoints; "
               <<"NOT an inductive proof\n";
           return 0;
        }
      }
   }
 }
 cout<<"STEPS_EXHAUSTED without six checkpoints; no claimed proof\n";
 return 6;
}
