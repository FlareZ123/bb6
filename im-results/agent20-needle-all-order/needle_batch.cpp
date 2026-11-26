// Exact low-bit affine batching for the shifted Space Needle counter x=d+2.
// Store z=x-1; then every legal transition has z'=(D_m*z+c_m)/2^m,
// D_m=2^m+3, c_m=3+2^(m-1)*(2m-5) >= 0 (m=v2(x)+1).
// Build a large batch by recursively consuming low-bit prefixes.
#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include <unistd.h>
using U = uint64_t;
using U128 = unsigned __int128;
using Bits = mp_bitcnt_t;
static_assert(sizeof(U)==sizeof(unsigned long));
struct Batch {
  mpz_class A=1, C=0;
  Bits S=0, vmax=0;
  U steps=0;
};
static U mask(Bits n) { assert(n<=64); return n==64 ? ~U(0) : (U(1)<<n)-1; }
static mpz_class mp128(U128 n) {
  U words[2]={U(n),U(n>>64)};
  mpz_class r; mpz_import(r.get_mpz_t(),2,-1,sizeof(U),0,0,words); return r;
}
static void append_small(Batch &b, Bits m) {
  assert(m>0);
  mpz_class d=mpz_class(1)<<m; d+=3;
  mpz_class c;
  if(m==1) c=0;
  else if(m==2) c=1;
  else { c=mpz_class(2*m-5)<<(m-1); c+=3; }
  b.A*=d; b.C*=d; c<<=b.S; b.C+=c;
  b.S+=m; b.steps++; b.vmax=std::max(b.vmax,m-1);
}
// m=0 means no remaining information: x=z+1=0 modulo 2^n.
static Bits low_m(const mpz_class &z,Bits n) {
  // First zero bit of z equals valuation of z+1.
  Bits v=mpz_scan0(z.get_mpz_t(),0);
  return v<n ? v+1 : 0;
}
static Batch tiny(const mpz_class &z,Bits n,U cap) {
  assert(n<=48);
  U r=z.get_ui()&mask(n); U128 A=1,C=0;
  Batch b;
  while(n&&b.steps<cap) {
    U x=(r+1)&mask(n);
    if(!x) break;
    Bits m=__builtin_ctzll(x)+1; assert(m<=n);
    U d=(U(1)<<m)+3;
    U c=m==1?0:m==2?1:3+((2*m-5)<<(m-1));
    // A <= 5^48; C/A <= S <= 48, so unsigned 128 bits suffice.
    A*=d; C=C*d+(U128(c)<<b.S);
    b.S+=m; b.steps++; b.vmax=std::max(b.vmax,m-1);
    r=(r+(m-1)+3*(x>>m))&mask(n-m); n-=m;
  }
  b.A=mp128(A); b.C=mp128(C); return b;
}
static mpz_class apply_low(const Batch &b,const mpz_class &z,Bits n) {
  assert(n>=b.S);
  mpz_class w=b.A*z+b.C;
  assert(mpz_divisible_2exp_p(w.get_mpz_t(),b.S));
  w>>=b.S;
  mpz_fdiv_r_2exp(w.get_mpz_t(),w.get_mpz_t(),n-b.S);
  return w;
}
static Batch combine(Batch a,Batch b) {
  a.C*=b.A; b.C<<=a.S; a.C+=b.C;
  a.A*=b.A; a.S+=b.S; a.steps+=b.steps; a.vmax=std::max(a.vmax,b.vmax);
  return a;
}
// Requires actual x>2^n, and actual z=low mod 2^n; then all selected
// steps have m<=remaining n and are legal. Cap is an exact step budget.
static Batch consume(const mpz_class &z,Bits n,U cap) {
  if(!n||!cap) return {};
  if(n<=48) return tiny(z,n,cap);
  Bits k=n/2;
  mpz_class low; mpz_fdiv_r_2exp(low.get_mpz_t(),z.get_mpz_t(),k);
  Batch a=consume(low,k,cap);
  if(a.steps==cap) return a;
  mpz_class mid=apply_low(a,z,n);
  if(a.S<k) {
    // Left recursion stopped at an unknown valuation crossing its cut.
    Bits m=low_m(mid,n-a.S);
    if(!m) return a;
    assert(a.S+m>k);
    Batch edge; append_small(edge,m);
    mid=apply_low(edge,mid,n-a.S);
    a=combine(std::move(a),std::move(edge));
  }
  assert(a.S>=k);
  if(a.S==n||a.steps==cap) return a;
  Batch b=consume(mid,n-a.S,cap-a.steps);
  return combine(std::move(a),std::move(b));
}
// Returns false precisely at a terminal power x=z+1.
static bool direct(mpz_class &z, Bits &vmax) {
  mpz_class x=z+1;
  Bits v=mpz_scan1(x.get_mpz_t(),0);
  if(mpz_sizeinbase(x.get_mpz_t(),2)==v+1) return false;
  mpz_class q=x>>(v+1); // (odd(x)-1)/2
  z+=v; z+=3*q; vmax=std::max(vmax,v); return true;
}
static U fingerprint(const mpz_class &z) {
  constexpr U p=18446744073709551557UL;
  return mpz_fdiv_ui(z.get_mpz_t(),p);
}
static double sec(std::chrono::steady_clock::time_point t) {return std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();}
static void report(const mpz_class &z,U steps,Bits vmax,U batches,std::chrono::steady_clock::time_point t) {
  std::cout<<"steps="<<steps<<" z_bits="<<mpz_sizeinbase(z.get_mpz_t(),2)<<" vmax="<<vmax<<" batches="<<batches<<" low64="<<z.get_ui()<<" modp="<<fingerprint(z)<<" sec="<<sec(t)<<std::endl;
}
static void tests() {
  // Every possible low input at n<=12, many deterministic pseudorandom large values,
  // exact cap behavior, and all boundary cases. No time cutoff is treated as a halt.
  U rng=0x3f41da22329b42adUL;
  auto check=[&](mpz_class z,Bits n,U cap){
    mpz_class low; mpz_fdiv_r_2exp(low.get_mpz_t(),z.get_mpz_t(),n);
    Batch b=consume(low,n,cap);
    mpz_class got=b.A*z+b.C;
    assert(mpz_divisible_2exp_p(got.get_mpz_t(),b.S)); got>>=b.S;
    Bits v=0,S=0,vm=0; mpz_class expected=z;
    for(U i=0;i<b.steps;i++) {
      v=mpz_scan0(expected.get_mpz_t(),0); S+=v+1;
      assert(S<=n&&direct(expected,vm));
    }
    assert(got==expected&&S==b.S&&vm==b.vmax&&b.steps<=cap);
    if(b.steps<cap && S<n) assert(mpz_scan0(expected.get_mpz_t(),0)>=n-S);
  };
  for(Bits n=1;n<=12;n++) for(U r=0;r<(U(1)<<n);r++) check((mpz_class(1)<<(n+2))+r,n,1000);
  for(Bits n:{48,49,63,64,65,96,97,100,127,128,129,255,256,257,1024,4096}) for(int j=0;j<20;j++) {
    mpz_class z=0;
    for(Bits k=0;k<n+128;k+=64){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;z<<=64;z+=rng;}
    z|=mpz_class(1)<<(n+1); check(z,n,j%3?U(j*7):100000);
    check((mpz_class(1)<<(n+1))+(mpz_class(1)<<(n-1))-1,n,10000);
  }
  std::cout<<"batch tests passed"<<std::endl;
}
int main(int argc,char**argv) {
  if(argc>1&&std::string(argv[1])=="test"){tests();return 0;}
  U target=argc>1?std::stoull(argv[1]):1000000;
  Bits maxB=argc>2?std::stoul(argv[2]):(1UL<<24);
  U progress=argc>3?std::stoull(argv[3]):1000000;
  mpz_class z=2; U steps=0,batches=0; Bits vmax=0;
  std::string checkpoint=argc>4?argv[4]:"";
  if(!checkpoint.empty()) {
    FILE *f=fopen(checkpoint.c_str(),"rb");
    if(f) {
      U hdr[3]; if(fread(hdr,sizeof(U),3,f)!=3||!mpz_inp_raw(z.get_mpz_t(),f)||fgetc(f)!=EOF) throw std::runtime_error("invalid checkpoint");
      fclose(f); steps=hdr[0]; vmax=hdr[1]; batches=hdr[2];
      if(steps>target||z<2) throw std::runtime_error("invalid checkpoint range");
    }
  }
  auto t=std::chrono::steady_clock::now(); U nextReport=steps+progress;
  auto save=[&](){
    if(checkpoint.empty()) return;
    std::string temp=checkpoint+".tmp"; FILE*f=fopen(temp.c_str(),"wb"); if(!f) throw std::runtime_error("checkpoint open");
    U hdr[3]={steps,vmax,batches}; if(fwrite(hdr,sizeof(U),3,f)!=3||!mpz_out_raw(f,z.get_mpz_t())||fflush(f)||fsync(fileno(f)))throw std::runtime_error("checkpoint write");
    if(fclose(f)||rename(temp.c_str(),checkpoint.c_str()))throw std::runtime_error("checkpoint rename");
  };
  report(z,steps,vmax,batches,t);
  while(steps<target) {
    Bits n=std::min(maxB,mpz_sizeinbase(z.get_mpz_t(),2)/2);
    if(n<48) {
      if(!direct(z,vmax)){std::cout<<"HALT steps="<<steps<<" exponent="<<mpz_scan0(z.get_mpz_t(),0)<<std::endl;save();return 0;}
      ++steps;
    } else {
      mpz_class low; mpz_fdiv_r_2exp(low.get_mpz_t(),z.get_mpz_t(),n);
      Batch b=consume(low,n,target-steps);
      if(!b.steps){if(!direct(z,vmax)){std::cout<<"HALT steps="<<steps<<" exponent="<<mpz_scan0(z.get_mpz_t(),0)<<std::endl;save();return 0;} ++steps;}
      else {z*=b.A; z+=b.C; assert(mpz_divisible_2exp_p(z.get_mpz_t(),b.S)); z>>=b.S; steps+=b.steps; vmax=std::max(vmax,b.vmax); ++batches;}
    }
    if(steps>=nextReport){report(z,steps,vmax,batches,t);save();nextReport=steps+progress;}
  }
  report(z,steps,vmax,batches,t); save();
  if(mpz_scan0(z.get_mpz_t(),0)==mpz_sizeinbase(z.get_mpz_t(),2))std::cout<<"HALT steps="<<steps<<" exponent="<<mpz_sizeinbase(z.get_mpz_t(),2)<<std::endl;
  else std::cout<<"No terminal through "<<steps<<" successful transitions (finite result)."<<std::endl;
}
