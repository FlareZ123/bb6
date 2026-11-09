// Exact Sheep even-return orbit from true blank section entry 10.
// Requires GMP and OpenSSL (libcrypto), C++17.
#include <gmpxx.h>
#include <openssl/sha.h>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <vector>

static std::string digest(const std::vector<uint32_t>& first) {
  std::vector<unsigned char> bytes(first.size()*4);
  for(size_t i=0;i<first.size();++i)
    for(unsigned k=0;k<4;++k) bytes[4*i+k]=(first[i]>>(8*k))&255;
  unsigned char out[SHA256_DIGEST_LENGTH];
  SHA256(bytes.data(),bytes.size(),out);
  std::ostringstream s;
  for(auto c:out) s<<std::hex<<std::setw(2)<<std::setfill('0')<<static_cast<unsigned>(c);
  return s.str();
}

struct Census {
  unsigned p;
  std::vector<uint32_t> first;
  uint32_t seen=0,last=0;
  bool reported=false;
  explicit Census(unsigned precision):p(precision),first(1u<<(precision-1),std::numeric_limits<uint32_t>::max()) {}
  void observe(uint64_t state,uint32_t lowbits){
    if(reported) return;
    const uint32_t res=(lowbits & ((1u<<p)-1))>>1;
    if(first[res]==std::numeric_limits<uint32_t>::max()){
      first[res]=static_cast<uint32_t>(state);
      ++seen;last=static_cast<uint32_t>(state);
      if(seen==first.size()) {
        reported=true;
        std::cout<<"FULL mod=2^"<<p<<" seen="<<seen<<" last_index="<<last
                 <<" sha256_le32="<<digest(first)<<"\n"<<std::flush;
      }
    }
  }
};

int main(int argc,char** argv){
  const uint64_t limit=(argc>1)?std::stoull(argv[1]):2500000;
  mpz_class x=10,u,z,q,tmp;
  Census p16(16),p17(17),p18(18);
  uint64_t exceptional=0;
  for(uint64_t i=0;i<limit;++i){
    const uint32_t lowbits=static_cast<uint32_t>(mpz_get_ui(x.get_mpz_t()));
    p16.observe(i,lowbits);p17.observe(i,lowbits);p18.observe(i,lowbits);
    if((lowbits&1)!=0) throw std::runtime_error("odd E state");
    const auto a=mpz_scan1(x.get_mpz_t(),0);
    u=x>>a;
    if(u==1){std::cout<<"HALT index="<<i<<" exponent="<<a<<"\n"; return 1;}
    if(u==3){++exceptional;z=x+a+3;}
    else {
      if(u<5 || (u%2)!=1)throw std::runtime_error("invalid source");
      z=x+a+(u-1)/2;
    }
    tmp=z-1;
    const auto h=mpz_scan1(tmp.get_mpz_t(),0);
    tmp>>=h;
    mpz_ui_pow_ui(q.get_mpz_t(),3,h);
    q=1+q*tmp;
    if(q<=x)throw std::runtime_error("non-increasing E");
    x=q;
    if((i+1)%250000==0)
      std::cout<<"CHECK n="<<i+1<<" bits="<<mpz_sizeinbase(x.get_mpz_t(),2)
               <<" covered18="<<p18.seen<<"/131072 special="<<exceptional<<"\n"<<std::flush;
    if(p18.reported)break;
  }
  std::cout<<"END covered18="<<p18.seen<<"/131072 special3="<<exceptional<<"\n";
  if(!p18.reported)return 2;
}
