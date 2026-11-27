#include <gmpxx.h>
#include <vector>
#include <iostream>
#include <fstream>
#include <cassert>
using I=mpz_class;
struct Row{I p,q;};
using Rows=std::vector<Row>;
struct State {I a,b; Rows cs;}; // far-to-near regular P,Q; final p unknown iff !birth.
I drain(Rows &v,I &merge){I h=0;size_t j=0;merge=0;for(size_t i=0;i<v.size();i++){
  auto &r=v[i]; I cap=2*h+1;
  if(r.p>cap){r.p-=cap;r.q+=h+1+merge;merge=0;h+=h+1;if(j!=i)v[j]=std::move(r);j++;}
  else{assert(mpz_odd_p(r.p.get_mpz_t()));I t=(r.p+1)/2;h+=t;merge+=r.q+t;}
 }v.resize(j);return h;}
void cycle(State &s,bool birth){
 Rows v;v.reserve(s.cs.size()+1);I prev=3;
 for(auto &r:s.cs){v.push_back({std::move(r.q),std::move(prev)});prev=std::move(r.p);prev--;}
 if(birth)v.push_back({std::move(s.b),std::move(prev)});
 I rA,rB;I A=drain(v,rA);for(auto &r:v){assert(r.p>=2);r.p--;}
 I B=drain(v,rB);assert(v.size()>=3);I scale=1; s.cs.resize(v.size());
 for(size_t i=0;i<v.size();i++){I p=0;if(i+1<v.size())p=v[i+1].q-(2*scale-1);else if(birth)p=s.a+2+A+B+rA+rB-(2*scale-1);assert(p>=3||(!birth&&i+1==v.size()));s.cs[i]={std::move(p),v[i].p-1+scale};scale*=2;}
 if(birth){s.a=2*scale-1;s.b=scale+3+2*(A+B);}
}
I skip(const State &s){I best=(s.cs[0].q-2)/3;for(size_t i=0;i<s.cs.size();i++){
 I P=I(1)<<i;I threshold=4*P;if(i<3)threshold+=2; I q=s.cs[i].q;
 if(q<threshold)return 0;
 I k=(q-threshold)/(3*P)+1;if(k<best)best=k;
 }return best;}
void advance(State &s,I t){I k=0;size_t events=0;while(k<t){I a=skip(s);if(a>t-k)a=t-k;if(a>0){I dp=2*a,dq=3*a;for(size_t i=0;i<s.cs.size();i++){if(i+1<s.cs.size())s.cs[i].p+=dp;s.cs[i].q-=dq;dp*=2;dq*=2;}k+=a;if(k==t)break;}size_t n=s.cs.size();cycle(s,false);k++;events++;assert(s.cs.size()<n);if(events%100==0)std::cerr<<"events "<<events<<" left "<<s.cs.size()<<" elapsed bits "<<mpz_sizeinbase(k.get_mpz_t(),2)<<"\n";}std::cout<<"events="<<events<<" elapsed="<<k<<" left="<<s.cs.size()<<"\n";}
void write(const State&s,const char* name){std::ofstream f(name);f<<s.a<<' '<<s.b<<'\n';for(auto&r:s.cs)f<<r.p<<' '<<r.q<<'\n';}
int main(int argc,char**argv){size_t K=argc>1?std::stoul(argv[1]):70000;unsigned bits=argc>2?std::stoul(argv[2]):8214;State s;std::ifstream f("seed-primary.txt");f>>s.a>>s.b;Row r;while(f>>r.p>>r.q)s.cs.push_back(r);assert(s.cs.size()==3);for(size_t i=1;i<=K;i++){cycle(s,true);if(i%5000==0)std::cerr<<"generate "<<i<<" width "<<s.cs.size()<<"\n";}write(s,"primary-prefix-input.txt");s.cs.push_back({0,s.b});s.a=s.b=0;I t=(I(1)<<bits)-1-K;assert(t>=0);advance(s,t);write(s,"primary-prefix-output.txt");}
