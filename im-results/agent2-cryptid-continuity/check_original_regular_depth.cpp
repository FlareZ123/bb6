// Independent primitive-step reproduction for two verified regular D-source
// exceptional-to-E ladders. No Lean imports or accelerated transition tables.
// g++ -std=c++20 -O2 check_original_regular_depth.cpp -o check && ./check
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
#include <vector>

using i64 = std::int64_t;
struct Rule { int write, move, next; };
constexpr Rule rules[6][2] = {
  {{1,1,1},{0,1,4}}, {{1,-1,2},{0,1,0}},
  {{1,-1,0},{1,-1,3}}, {{1,-1,2},{1,-1,5}},
  {{0,-1,2},{0,-1,1}}, {{1,-1,4},{1,0,6}}
};
i64 power(int b, int m) {
  i64 n = 1;
  while (m-- > 0) n *= b;
  return n;
}
i64 e_time(int m, int U, int p) {
  i64 u = U-1, q = p, time = 0;
  for (int s=m;s>0;--s) {
    const i64 K=power(3,s)*(u+1)-1;
    time += 12*K*K+49*K+58+6*q;
    u=8*u+7;
    q+=2;
  }
  return time;
}
void check(int m, int v, int h, int U, int p, i64 benchmark) {
  const bool even=(m%2==0);
  const i64 t=3*v+(even?2:1), k=3*t+1, q=h+3;
  const i64 N=3*k+4;
  const i64 first=12*k*k+49*k+64+4*(h+1);
  const i64 K=8*t+3, second=12*K*K+49*K+58;
  const i64 J=64*v+(even?53:31);
  const i64 third=12*J*J+49*J+(even?40:70);
  const i64 steps=first+second+third+e_time(m,U,p);
  if(steps!=benchmark) throw std::runtime_error("calculated primitive time");
  if(512*v+(even?434:257)!=power(3,m+1)*U+1)
    throw std::runtime_error("E-stage input unary index");
  if(2*h+(even?3:0)!=3*m+3)
    throw std::runtime_error("E-stage packet length");

  // Initial F-on-blank cell at position 0; right tape is 1^(3k+4) (01)^q 1.
  std::unordered_set<i64> ones;
  for(i64 i=1;i<=N;i++) ones.insert(i);
  for(i64 j=0;j<q;j++) ones.insert(N+2*j+2);
  ones.insert(N+2*q+1);
  i64 head=0;
  int state=5;
  for(i64 i=0;i<steps;i++) {
    if(state==6) throw std::runtime_error("halted before endpoint");
    const int scan=ones.contains(head)?1:0;
    const Rule a=rules[state][scan];
    if(a.write) ones.insert(head);
    else ones.erase(head);
    head+=a.move;
    state=a.next;
  }
  // Predicted exact final F/0 tape (up to invisible far-right zeros).
  std::vector<int> finalBits(3*power(8,m)*U+1,1);
  finalBits.push_back(0);
  for(int j=0;j<p+2*m;j++){ finalBits.push_back(1); finalBits.push_back(0); }
  finalBits.insert(finalBits.end(),3,1);
  finalBits.push_back(0);
  finalBits.insert(finalBits.end(),6,1);
  std::unordered_set<i64> expected;
  for(std::size_t i=0;i<finalBits.size();i++)
    if(finalBits[i])expected.insert(head+1+static_cast<i64>(i));
  int errors=0;
  for(auto i:ones)if(!expected.contains(i))errors++;
  for(auto i:expected)if(!ones.contains(i))errors++;
  std::cout<<"m="<<m<<" k="<<k<<" q="<<q<<" right_support="<<(N+2*q+1)
    <<" primitive_steps="<<steps<<" ending_F0="<<(state==5&&!ones.contains(head))
    <<" tape_symmetric_difference="<<errors<<"\n";
  if(state!=5||ones.contains(head)||errors)
    throw std::runtime_error("primitive final checkpoint mismatch");
}
int main() {
  check(1,4,3,256,4,8263623);
  check(2,1,3,35,1,9885171);
  std::cout<<"PASS both independent literal six-state primitive traces\n";
}
