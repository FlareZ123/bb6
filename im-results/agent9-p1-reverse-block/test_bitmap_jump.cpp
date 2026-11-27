#include "reduced_jump.hpp"
#include <cassert>
#include <chrono>
#include <iostream>
#include <random>
using namespace bb6_jump;
int main(){
 std::mt19937 rng(45352466);
 unsigned cases=0;
 for(int j=0;j<4000;j++){
  int q=rng()%1000000000,r=rng()%15;
  bitmap_plan=false;Plan a(q,r);bitmap_plan=true;Plan b(q,r);
  assert(a.exponent==b.exponent&&a.residues==b.residues);++cases;
 }
 for(int q:{934000123,960000006,1000000001})for(int r:{18,22,26}){
  bitmap_plan=false;Plan a(q,r);bitmap_plan=true;Plan b(q,r);
  assert(a.exponent==b.exponent&&a.residues==b.residues);++cases;
 }
 std::cout<<"bitmap exact plan comparisons="<<cases<<std::endl;
 for(int F:{975077669,1009092005,1043106341})for(int r:{22,24,26,28,30}){
  if(r<=26){
   bitmap_plan=false;auto t=std::chrono::steady_clock::now();Plan p(F-r,r);
   std::cout<<"PLAN method=sparse F="<<F<<" r="<<r<<" e="<<p.exponent<<" size="<<p.residues.size()<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<std::endl;
  }
  bitmap_plan=true;auto t=std::chrono::steady_clock::now();Plan p(F-r,r);
  std::cout<<"PLAN method=bitmap F="<<F<<" r="<<r<<" e="<<p.exponent<<" size="<<p.residues.size()<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<std::endl;
 }
}
