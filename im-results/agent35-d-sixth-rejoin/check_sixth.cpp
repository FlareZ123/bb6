#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

struct Rule { uint8_t write; int8_t shift; uint8_t next; };
constexpr Rule rules[6][2] = {
  {{1,1,1},{0,1,4}}, {{1,-1,2},{0,1,0}},
  {{1,-1,0},{1,-1,3}}, {{1,-1,2},{1,-1,5}},
  {{0,-1,2},{0,-1,1}}, {{1,-1,4},{1,0,6}}
};
uint64_t sqcost(uint64_t k,uint64_t linear,uint64_t constant) {
  return 12*k*k+linear*k+constant;
}
std::vector<uint8_t> cat(std::vector<uint8_t> a,const std::vector<uint8_t>& b){
  a.insert(a.end(),b.begin(),b.end());return a;
}
std::vector<uint8_t> alt(unsigned q) {
  std::vector<uint8_t> r;
  for(unsigned i=0;i<q;i++){r.push_back(0);r.push_back(1);}
  return r;
}
std::vector<uint8_t> ones(unsigned n){return std::vector<uint8_t>(n,1);}
void verify(const std::vector<uint8_t>& tape,size_t center,size_t head,uint8_t state,
    uint64_t instant,uint64_t unary,const std::vector<uint8_t>& suffix) {
  if(state!=5 || tape[head]!=0) throw std::runtime_error("state/head mismatch");
  for(size_t i=0;i<head;i++)
    if(tape[i]!=0) throw std::runtime_error("nonblank left tape");
  for(uint64_t j=0;j<unary;j++)
    if(tape[head+1+j]!=1) throw std::runtime_error("unary mismatch");
  const size_t start=head+1+unary;
  for(size_t j=0;j<suffix.size();j++)
    if(tape[start+j]!=suffix[j]) throw std::runtime_error("suffix mismatch");
  for(size_t j=start+suffix.size();j<tape.size();j++)
    if(tape[j]!=0) throw std::runtime_error("unaccounted right tape");
  std::cout << "verified t=" << instant << " unary=" << unary <<
    " suffix_bits=" << suffix.size() <<
    " head_offset=" << int64_t(head)-int64_t(center) << "\n";
}
int main(){
  for(uint64_t w=0;w<=1;w++){
    uint64_t t=27*w+23,kb=576*w+501,ke=1536*w+1338,ka=4096*w+3570;
    uint64_t c1=sqcost(3*t+1,49,72);
    uint64_t c2=sqcost(8*t+3,49,58);
    uint64_t c3=sqcost(kb,49,40);
    uint64_t c4=sqcost(ke,49,64);
    uint64_t c5=sqcost(ka,41,32)+6+2*(4*ka+6)+24;
    uint64_t steps[]={c1,c2,c3,c4,c5};
    std::vector<uint8_t> suffix[]={
      cat(cat(std::vector<uint8_t>{0},ones(8)),cat(std::vector<uint8_t>{0},ones(6))),
      cat(cat(cat(alt(2),std::vector<uint8_t>{0}),ones(5)),cat(std::vector<uint8_t>{0},ones(6))),
      cat(cat(cat(alt(1),std::vector<uint8_t>{0}),ones(5)),cat(std::vector<uint8_t>{0},ones(6))),
      cat(cat(cat(alt(3),std::vector<uint8_t>{0}),ones(2)),cat(std::vector<uint8_t>{0},ones(6))),
      cat(alt(3),ones(2))};
    uint64_t unary[]={24*t+13,64*t+33,8*kb+10,8*ke+9,8*ka+17};
    constexpr size_t tapeSize=1000000, center=200000;
    std::vector<uint8_t> tape(tapeSize,0);
    uint64_t initial=9*t+7;
    auto initialSuffix=cat(alt(4),ones(1));
    for(uint64_t j=0;j<initial;j++) tape[center+1+j]=1;
    for(size_t j=0;j<initialSuffix.size();j++)
      tape[center+1+initial+j]=initialSuffix[j];
    uint64_t elapsed=0;size_t head=center;uint8_t state=5;
    for(int i=0;i<5;i++){
      for(uint64_t j=0;j<steps[i];j++){
        auto rule=rules[state][tape[head]];
        tape[head]=rule.write;
        head=static_cast<size_t>(static_cast<int64_t>(head)+rule.shift);
        state=rule.next;
        if(state>5) throw std::runtime_error("unexpected halt");
      }
      elapsed+=steps[i];
      verify(tape,center,head,state,elapsed,unary[i],suffix[i]);
    }
  }
}
