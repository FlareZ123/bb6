#include <cassert>
#include <cstdint>
#include <iostream>
#include <chrono>
#include <string>
#include <algorithm>
using U=uint64_t;using W=__uint128_t;struct State{U q,v;};
U corr(unsigned k,U B){U D=(B&0xAAAAAAAAAAAAAAAAULL)+((B&0xCCCCCCCCCCCCCCCCULL)<<1)+((B&0xF0F0F0F0F0F0F0F0ULL)<<2)+((B&0xFF00FF00FF00FF00ULL)<<3)+((B&0xFFFF0000FFFF0000ULL)<<4)+((B&0xFFFFFFFF00000000ULL)<<5);return k*B-D;}
std::pair<U,U> block(U q,U v,unsigned k){W X=W(v)<<k;U B=X/q,R=X%q,C=corr(k,B);if(R>=C)return {B,R-C};--B;return {B,R+q-corr(k,B)};}
State wrap(U q,U v){U u=v*2;++q;while(u<q){u*=2;++q;}return {q,u-q};}
State special(U q,U v){assert(v<=2&&v+4<=q);if(v==0)return {q+2,q-3};if(v==2)return wrap(q,4);U x=q-2,j=0,A=7;while(2*A-j-8<=x){++j;A*=2;}U r=x-(A-j-7);if(r==0)return {A-1,A-6};if(r==1)return wrap(A+j+1,2*j+5);if(r==2){std::cout<<"HALT "<<q<<" "<<j<<std::endl;return {0,0};}return wrap(A+r-2,2*r-1);}
State scalar(State s){++s.q;s.v*=2;if(s.v>=s.q)s.v-=s.q;return s;}
int main(int argc,char**argv){U limit=argc>1?std::stoull(argv[1]):1000000000;bool fast=argc<3||std::string(argv[2])!="scalar";assert(limit<(1ULL<<61));
for(U q=2;q<200;++q)for(U v=0;v<q;++v)for(unsigned k=0;(1ULL<<(k+1))<=q;++k){auto [B,R]=block(q,v,k);U b=0;State s{q,v};for(unsigned j=0;j<k;++j){b=2*b+(2*s.v>=s.q+1);s=scalar(s);}assert(B==b&&R==s.v);}
State s{5,0};U skipped=0,steps=0;auto start=std::chrono::steady_clock::now();while(s.q<limit){if(s.v<=2){std::cout<<"event "<<s.q<<" "<<s.v<<std::endl;s=special(s.q,s.v);if(!s.q)break;continue;}unsigned k=std::min<U>(63-__builtin_clzll(s.q)-1,limit-s.q);if(fast&&k){auto [B,R]=block(s.q,s.v,k);if(B==0||R>2*(B&-B)){s={s.q+k,R};skipped+=k;continue;}}s=scalar(s);++steps;}
std::cout<<"end "<<s.q<<" "<<s.v<<" skipped "<<skipped<<" scalar "<<steps<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;}
