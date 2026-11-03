// Machine C mixed192 reverse-core verifier, C++17.
// Exact original BB6CLine.nextC branches; exhaustive 28,459,008 representative edges.
// Both=true includes the companion terminal residue in each core.
#include <cstdio>
#include <cstdint>
#include <utility>
#include <chrono>
using P=std::pair<int,int>;
struct T {int a,k,c;};
constexpr int M=192,L=96,C=98;

bool low(int core,int a,int k,int c,bool both){
 const int w=k+c;
 const P A[7]={{0,25},{10,19},{34,7},{46,4},{48,1},{58,43},{82,31}};
 const P B[7]={{10,43},{24,37},{34,31},{46,28},{58,19},{72,13},{82,7}};
 if(core==0){
  if((a%192==35&&w%192==61)||(both&&a%192==131&&w%192==157))return true;
 }else{
  if((a%192==83&&w%192==13)||(both&&a%192==179&&w%192==109))return true;
 }
 for(const auto p:core?B:A)if(a%96==p.first&&w%48==p.second)return true;
 return false;
}
bool high(int core,int a,int k,int c){
 const int d=(a+96-c%96)%96,t=(a+k)%192;
 const P A[14]={{7,26},{8,27},{17,33},{31,38},{32,39},{43,47},
                {45,46},{55,2},{56,3},{65,9},{79,14},{80,15},{86,21},{93,22}};
 const P B[14]={{7,2},{8,3},{17,9},{21,10},{31,14},{32,15},
                {38,21},{43,23},{55,26},{56,27},{65,33},{69,34},{79,38},{80,39}};
 for(const auto p:core?B:A)if(d==p.first&&t%48==p.second)return true;
 return core==0?((d==32&&t==93)||(d==35&&t%96==45)):
                ((d==80&&t==93)||(d==83&&t%96==45));
}
bool bad(int core,int a,int k,int c,bool both){
 return c<2?low(core,a,k,c,both):high(core,a,k,c);
}
bool next(T s,T& t){
 const int a=s.a,k=s.k,c=s.c;
 if(c==1){t={a,k+1,0};return true;}
 if(c==2)return false;
 if(c==3){t={a,k+2,1};return true;}
 if(c==0){
  if(a==0)t={1,0,2*k+2};
  else if(a==1){if(k==0)t={5,0,1};else t={2,2,2*k-1};}
  else t={a-2,1,2*k+1};
  return true;
 }
 if(a==0){
  if(k%2==0)t={2*k+2,2,c-3};
  else t={2*k+3,0,c};
  return true;
 }
 t={a-1,k+1,c-1};return true;
}
int main(){
 const auto start=std::chrono::steady_clock::now();
 for(int core=0;core<2;core++)for(int both=0;both<=1;both++){
  std::uint64_t edges=0,badStates=0;
  for(int a=0;a<M;a++)for(int k=0;k<M;k++)for(int c=0;c<C;c++){
   const bool before=bad(core,a,k,c,both);
   badStates+=before;
   for(int ia=0;ia<2;ia++)for(int ik=0;ik<2;ik++)
    for(int ic=0;ic<(c<2?1:2);ic++){
     const T s{a+ia*M,k+ik*M,c+ic*L};
     T t;
     if(!next(s,t))continue;
     ++edges;
     if(bad(core,t.a,t.k,t.c,both)&&!before){
      std::printf("FAIL core=%d both=%d (%d,%d,%d)->(%d,%d,%d)\n",
                  core,both,s.a,s.k,s.c,t.a,t.k,t.c);
      return 1;
     }
    }
  }
  std::printf("PASS core=%c enlarged=%d badStates=%llu edges=%llu rootBad=%d\n",
              core?'B':'A',both,
              static_cast<unsigned long long>(badStates),
              static_cast<unsigned long long>(edges),bad(core,5,0,1,both));
  if(bad(core,5,0,1,both))return 2;
 }
 const auto dt=std::chrono::duration<double>(
                 std::chrono::steady_clock::now()-start).count();
 std::printf("elapsed %.3f s\n",dt);
}
