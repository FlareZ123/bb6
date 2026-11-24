#include <cstdint>
#include <cstdlib>
#include <iostream>
using i64=std::int64_t;
enum class Tag { F, R2, R1, R0, E1, Eeven, Eodd, O2, Oeven1, Oeven, Oodd, Halt };
struct Step { i64 u,w; Tag tag; };
static Step next(i64 u,i64 w){
 if(w>=2*u+3)return{2*u+3,w-2*u-3,Tag::F};
 if(w==2*u+2)return{0,4*u+18,Tag::R2};
 if(w==2*u+1)return{11,4*u+2,Tag::R1};
 if(w==2*u)return{0,4*u+12,Tag::R0};
 i64 d=u-w/2;
 if((w&1)==0){if(d==1)return{0,2*w+12,Tag::E1};if((d&1)==0)return{11,2*u+w-2,Tag::Eeven};return{0,2*u+w+10,Tag::Eodd};}
 if(d==1)return{u,w,Tag::Halt};
 if(d==2)return{0,2*w+8,Tag::O2};
 if((d&1)==0){if(w==1)return{11,2*u+10,Tag::Oeven1};return{d+7,2*w-4,Tag::Oeven};}
 return{d+3,2*w,Tag::Oodd};
}
static void expect(i64&u,i64&w,Tag t,i64&steps){
 Step s=next(u,w);
 if(s.tag!=t){std::cerr<<"tag mismatch at step "<<steps<<" state="<<u<<","<<w<<"\n";std::exit(1);}
 u=s.u;w=s.w;++steps;
}
int main(){
 i64 u=0,w=805306356,steps=0;
 for(int j=0;j<27;j++)expect(u,w,Tag::F,steps);
 if(u!=402653181||w!=75){std::cerr<<"outer F27 mismatch\n";return 1;}
 expect(u,w,Tag::Oeven,steps);
 expect(u,w,Tag::Eeven,steps);
 if(u!=11||w!=805306446){std::cerr<<"outer reset mismatch "<<u<<","<<w<<"\n";return 1;}
 constexpr i64 N=1458887;
 for(i64 i=0;i<N;i++){
  if(u!=11||w<805306446||w>939523958||w%4!=2){std::cerr<<"inner precondition failure i="<<i<<" state="<<u<<","<<w<<"\n";return 1;}
  for(int j=0;j<24;j++)expect(u,w,Tag::F,steps);
  if(u!=234881021){std::cerr<<"inner F24 u mismatch\n";return 1;}
  expect(u,w,Tag::Eeven,steps);
  if(u!=11||w!=805306446+92*(i+1)){std::cerr<<"inner return mismatch i="<<i<<" state="<<u<<","<<w<<"\n";return 1;}
 }
 if(w!=939524050){std::cerr<<"inner endpoint mismatch "<<w<<"\n";return 1;}
 for(int j=0;j<25;j++)expect(u,w,Tag::F,steps);
 if(u!=469762045||w!=57){std::cerr<<"final F25 mismatch "<<u<<","<<w<<"\n";return 1;}
 expect(u,w,Tag::Oodd,steps);
 expect(u,w,Tag::Eodd,steps);
 if(u!=0||w!=939524164||steps!=36472231){std::cerr<<"final mismatch "<<u<<","<<w<<" steps="<<steps<<"\n";return 1;}
 std::cout<<"start: (0,805306356)\n";
 std::cout<<"outer: F^27 Oeven Eeven -> (11,805306446)\n";
 std::cout<<"inner: "<<N<<" x (F^24 Eeven), V += 92 -> (11,939524050)\n";
 std::cout<<"final: F^25 Oodd Eodd -> (0,939524164)\n";
 std::cout<<"total transitions: "<<steps<<"\n";
}
