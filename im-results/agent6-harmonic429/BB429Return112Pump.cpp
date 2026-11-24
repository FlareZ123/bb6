#include <cstdint>
#include <cstdlib>
#include <iostream>
using i64=std::int64_t;
enum class Tag{F,R2,R1,R0,E1,Eeven,Eodd,O2,Oeven1,Oeven,Oodd,Halt};
struct Step{i64 u,w;Tag tag;};
static Step next(i64 u,i64 w){
 if(w>=2*u+3)return{2*u+3,w-2*u-3,Tag::F};
 if(w==2*u+2)return{0,4*u+18,Tag::R2};
 if(w==2*u+1)return{11,4*u+2,Tag::R1};
 if(w==2*u)return{0,4*u+12,Tag::R0};
 i64 d=u-w/2;
 if(!(w&1)){if(d==1)return{0,2*w+12,Tag::E1};if(!(d&1))return{11,2*u+w-2,Tag::Eeven};return{0,2*u+w+10,Tag::Eodd};}
 if(d==1)return{u,w,Tag::Halt};
 if(d==2)return{0,2*w+8,Tag::O2};
 if(!(d&1)){if(w==1)return{11,2*u+10,Tag::Oeven1};return{d+7,2*w-4,Tag::Oeven};}
 return{d+3,2*w,Tag::Oodd};
}
static void expect(i64&u,i64&w,Tag t,i64&steps){
 Step s=next(u,w);
 if(s.tag!=t){std::cerr<<"tag mismatch step="<<steps<<" state="<<u<<","<<w<<"\n";std::exit(1);}
 u=s.u;w=s.w;++steps;
}
int main(){
 i64 u=0,w=1073741884,steps=0;
 constexpr i64 N=871543;
 for(i64 i=0;i<N;i++){
  if(u!=0||w!=1073741884+112*i||w%4!=0){std::cerr<<"precondition fail i="<<i<<" state="<<u<<","<<w<<"\n";return 1;}
  for(int j=0;j<27;j++)expect(u,w,Tag::F,steps);
  expect(u,w,Tag::Oeven,steps);expect(u,w,Tag::F,steps);
  expect(u,w,Tag::Oodd,steps);expect(u,w,Tag::Eodd,steps);
  if(u!=0||w!=1073741884+112*(i+1)){std::cerr<<"return fail i="<<i<<" state="<<u<<","<<w<<"\n";return 1;}
 }
 if(w!=1171354700||steps!=27017833){std::cerr<<"final mismatch "<<u<<","<<w<<" steps="<<steps<<"\n";return 1;}
 for(int j=0;j<27;j++)expect(u,w,Tag::F,steps);
 expect(u,w,Tag::Oeven,steps);expect(u,w,Tag::F,steps);expect(u,w,Tag::Oodd,steps);
 if(u!=292838528||w!=585677746||next(u,w).tag!=Tag::F){std::cerr<<"phase boundary mismatch "<<u<<","<<w<<"\n";return 1;}
 std::cout<<"verified "<<N<<" cycles of F^27 Oeven F Oodd Eodd, 31 steps each, W += 112\n";
 std::cout<<"phase end: (0,"<<1171354700<<") after "<<27017833<<" transitions from (0,1073741884)\n";
 std::cout<<"next phase boundary state: ("<<u<<","<<w<<"), next tag F\n";
}
