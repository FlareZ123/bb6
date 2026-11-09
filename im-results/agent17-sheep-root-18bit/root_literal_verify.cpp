// Independent reference: repeat literal Sheep odd returns rather than the closed-form odd burst.
// Requires GMP and OpenSSL (libcrypto), C++17.
#include <gmpxx.h>
#include <openssl/sha.h>
#include <cstdint>
#include <iostream>
#include <vector>
#include <iomanip>
#include <limits>
using namespace std;
int main(){
  constexpr uint64_t max_index=1587692;
  vector<uint32_t> first(131072,UINT32_MAX);
  uint32_t found=0,last=0; uint64_t exceptional=0;
  mpz_class x=10,t,odd;
  for(uint64_t n=0;n<=max_index;++n){
    if((x%2)!=0){cerr<<"not even "<<n<<endl;return 2;}
    unsigned residue=(mpz_get_ui(x.get_mpz_t())&262143u)>>1;
    if(first[residue]==UINT32_MAX){first[residue]=n;++found;last=n;}
    mp_bitcnt_t a=mpz_scan1(x.get_mpz_t(),0);
    odd=x>>a;
    if(odd==1){cerr<<"HALT "<<n<<endl;return 3;}
    if(odd==3){++exceptional;t=x+a+3;}
    else t=x+a+(odd-1)/2;
    while((t%2)!=0){t=(3*t-1)/2;}
    if(t<=x){cerr<<"nonincrease "<<n<<endl;return 4;}
    x=t;
  }
  vector<unsigned char> b(first.size()*4);
  for(size_t i=0;i<first.size();++i)
    for(int k=0;k<4;++k)b[i*4+k]=(first[i]>>(8*k))&255;
  unsigned char d[SHA256_DIGEST_LENGTH]; SHA256(b.data(),b.size(),d);
  cout<<"literal states="<<(max_index+1)
      <<" bitlen-next="<<mpz_sizeinbase(x.get_mpz_t(),2)
      <<" covered="<<found<<" last="<<last
      <<" special="<<exceptional<<" sha256_le32=";
  for(auto c:d)cout<<hex<<setw(2)<<setfill('0')<<(unsigned)c;
  cout<<endl;
}
