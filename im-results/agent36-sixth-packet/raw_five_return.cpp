#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

// Independent literal D-machine simulator for the proposed sixth packet.
// The initial F state scans zero, with 1^n and (01)^4 1 immediately right.
int main(int argc, char** argv) {
  const unsigned v = argc > 1 ? static_cast<unsigned>(std::strtoul(argv[1], nullptr, 10)) : 0;
  if (v > 1) { std::fprintf(stderr, "Only samples v=0 or v=1 are supported.\n"); return 2; }
  const uint64_t n0 = 243ull*v + 214;
  const std::array<uint64_t,5> k = {81ull*v+70,216ull*v+187,576ull*v+501,
                                    1536ull*v+1338,4096ull*v+3570};
  std::array<uint64_t,5> dt{};
  for(size_t i=0;i<5;i++) dt[i] = 12*k[i]*k[i]+49*k[i]+
      (i==0?72 : i==1?58 : i==2?40 : i==3?64 : 74);
  const std::array<uint64_t,5> unary = {648ull*v+565,1728ull*v+1505,
      4608ull*v+4018,12288ull*v+10713,32768ull*v+28577};
  const std::array<std::string,5> suffix = {"0111111110111111", "01010111110111111",
      "010111110111111", "0101010110111111", "01010111"};
  uint64_t maxTime=0;
  for(uint64_t d:dt)maxTime+=d;

  std::vector<unsigned char> tape(1<<23,0);
  int head=1<<22;
  for(uint64_t i=0;i<n0;i++) tape[head+1+i]=1;
  const std::string initialSuffix="010101011";
  for(size_t i=0;i<initialSuffix.size();i++)
    tape[head+1+n0+i] = (initialSuffix[i]=='1');
  int leftOnes=0;
  unsigned state=5, count=0;
  uint64_t expectedTime=0;
  for(uint64_t t=1;t<=maxTime;t++) {
    const unsigned bit=tape[head];
    unsigned write=0,next=0;
    int dir=1;
    switch (state) {
      case 0: if(!bit){write=1;next=1;}else{write=0;next=4;} break;
      case 1: if(!bit){write=1;next=2;dir=-1;}else{write=0;next=0;} break;
      case 2: if(!bit){write=1;next=0;dir=-1;}else{write=1;next=3;dir=-1;} break;
      case 3: if(!bit){write=1;next=2;dir=-1;}else{write=1;next=5;dir=-1;} break;
      case 4: if(!bit){write=0;next=2;dir=-1;}else{write=0;next=1;dir=-1;} break;
      case 5: if(!bit){write=1;next=4;dir=-1;}else{
        std::fprintf(stderr,"Unexpected F/1 halt at %llu\n",(unsigned long long)t);
        return 3;
      }
    }
    tape[head]=static_cast<unsigned char>(write);
    if(dir==1){leftOnes+=write;++head;}
    else{--head;leftOnes-=tape[head];}
    state=next;
    if(state==5 && tape[head]==0 && leftOnes==0) {
      if(count>=5){std::fprintf(stderr,"Extra physical F/0 return\n");return 4;}
      expectedTime+=dt[count];
      uint64_t last=0;
      for(uint64_t j=0;j<100000;j++)if(tape[head+1+j])last=j+1;
      uint64_t n=0;
      while(n<last && tape[head+1+n])++n;
      std::string word;
      for(uint64_t j=n;j<last;j++)word+=char('0'+tape[head+1+j]);
      if(t!=expectedTime || n!=unary[count] || word!=suffix[count]){
        std::fprintf(stderr,"Mismatch: return=%u time=%llu n=%llu suffix=%s\n",
          count+1,(unsigned long long)t,(unsigned long long)n,word.c_str());
        return 5;
      }
      std::printf("PASS v=%u return=%u primitive=%llu unary=%llu suffix=%s\n",
        v,count+1,(unsigned long long)t,(unsigned long long)n,word.c_str());
      ++count;
    }
  }
  if(count!=5 || expectedTime!=maxTime || state!=5 || leftOnes!=0){
    std::fprintf(stderr,"Invalid terminal state\n");return 6;
  }
  std::printf("PASS v=%u all five physical F/0 returns, exact %llu primitive steps\n",
      v,(unsigned long long)maxTime);
}
