#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <string>
#include <vector>

// Exact D-start table: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.
struct Rule { int write, move, state; };
constexpr Rule rules[6][2] = {
  {{1, 1, 1}, {0, 1, 4}}, {{1, -1, 2}, {0, 1, 0}},
  {{1, -1, 0}, {1, -1, 3}}, {{1, -1, 2}, {1, -1, 5}},
  {{0, -1, 2}, {0, -1, 1}}, {{1, -1, 4}, {0, 0, 6}}
};
struct Outcome { char kind; int ones; std::string tail; int64_t steps; int hitState; int64_t hitTime; };
struct Simulator {
  static constexpr int size = 1 << 17, offset = size / 2;
  std::vector<int> stamp = std::vector<int>(size);
  std::vector<unsigned char> bit = std::vector<unsigned char>(size);
  int generation = 0, rightmost = 0;
  int get(int p) const {
    return (p >= -offset && p < offset && stamp[offset+p] == generation)
      ? bit[offset+p] : 0;
  }
  void put(int p,int b) {
    if(p < -offset || p >= offset) std::abort();
    stamp[offset+p] = generation;
    bit[offset+p] = b;
    rightmost = std::max(rightmost,p);
  }
  Outcome run(int branch,int m,const std::string& suffix,int64_t cap,int marker) {
    ++generation;
    rightmost = 0;
    const int states[] = {1,0,4}; // B/A/E on zero.
    int state=states[branch], head=0, nonzeroLeft=m+2, p=-1;
    int hitState=-1; int64_t hitTime=-1;
    for(int j=0;j<branch;j++) put(p--,0);
    for(int j=0;j<m;j++){put(p--,1);put(p--,0);}
    put(p--,1);put(p--,1);
    for(int j=0;j<(int)suffix.size();j++)put(j+1,suffix[j]=='1');
    for(int64_t t=0;t<cap;t++) {
      if(hitState==-1 && head==marker) {hitState=state;hitTime=t;}
      if(state==6) return {'H',-1,"",t,hitState,hitTime};
      if(t>0 && state==5 && !get(head) && !nonzeroLeft) {
        int next=head+1;
        while(next<=rightmost && get(next)) ++next;
        std::string rest;
        for(int j=next;j<=rightmost;j++)rest+=char('0'+get(j));
        while(!rest.empty() && rest.back()=='0')rest.pop_back();
        return {'R',next-head-1,rest,t,hitState,hitTime};
      }
      Rule r=rules[state][get(head)];
      put(head,r.write);
      if(r.state==6){state=6;continue;}
      if(r.move==1){nonzeroLeft+=r.write;head++;}
      else {nonzeroLeft-=get(head-1);head--;}
      if(nonzeroLeft<0 || head < -offset || head >= offset)std::abort();
      state=r.state;
    }
    return {'?',-1,"",cap,hitState,hitTime};
  }
};
int main(int argc,char**argv) {
  const int maxBits=argc>1?std::atoi(argv[1]):15;
  const int maxM=argc>2?std::atoi(argv[2]):3;
  const int64_t cap=argc>3?std::atoll(argv[3]):1000000;
  if(maxBits>20 || maxBits<0 || maxM<0) return 2;
  Simulator small,large;
  for(int branch=0;branch<3;branch++)for(int m=0;m<=maxM;m++) {
    std::map<int64_t,int64_t> returns,halts;
    int64_t fail=0,unknown=0; std::map<int,int64_t> hitTypes;
    int64_t divergentHits=0;
    std::string firstFailure;
    for(int len=0;len<=maxBits;len++)for(int mask=0;mask<(1<<len);mask++) {
      std::string suffix;
      for(int j=0;j<len;j++)suffix+=char('0'+((mask>>j)&1));
      auto x=small.run(branch,m,suffix,cap,-branch-2*m-1);
      auto y=large.run(branch,m+4,suffix,cap,-branch-2*m-1);
      if(x.kind=='?'||y.kind=='?'){unknown++;continue;}
      hitTypes[x.hitState]++;
      if(x.hitState!=y.hitState || x.hitTime!=y.hitTime) divergentHits++;
      if(x.kind=='H'&&y.kind=='H') {halts[y.steps-x.steps]++;continue;}
      if(x.kind=='R'&&y.kind=='R'&&y.ones==x.ones+8&&y.tail==x.tail) {
        returns[y.steps-x.steps]++;continue;
      }
      if(!fail)firstFailure="suffix="+suffix+" first="+x.kind+":"+
        std::to_string(x.ones)+":"+x.tail+":"+std::to_string(x.steps)+
        " second="+y.kind+":"+std::to_string(y.ones)+":"+y.tail+
        ":"+std::to_string(y.steps);
      fail++;
    }
    std::cout<<"branch="<<"BAE"[branch]<<" m="<<m
      <<" failures="<<fail<<" unknown="<<unknown;
    for(auto [d,c]:returns)std::cout<<" Rdiff("<<d<<")="<<c;
    for(auto [d,c]:halts)std::cout<<" Hdiff("<<d<<")="<<c;
    for(auto [st,c]:hitTypes)std::cout<<" firstMarkerState("<<st<<")="<<c;
    std::cout<<" markerMismatch="<<divergentHits;
    if(fail)std::cout<<" FIRST_FAILURE "<<firstFailure;
    std::cout<<'\n';
  }
}
