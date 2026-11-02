#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

struct Check { std::uint64_t t; int n; int suffix; };
int main() {
  constexpr int SIZE = 2000000;
  constexpr int MID = SIZE/2;
  std::vector<unsigned char> tape(SIZE, 0);
  const int wr[6][2]={{1,0},{1,0},{1,1},{1,1},{0,0},{1,1}};
  const int dr[6][2]={{1,1},{-1,1},{-1,-1},{-1,-1},{-1,-1},{-1,0}};
  const int nx[6][2]={{1,4},{2,0},{0,3},{2,5},{2,1},{4,6}};
  const std::array<Check,9> checkpoints={{{36,9,0},{226,27,0},{1430,75,0},{9562,203,0},{66753,545,0},{468794,1457,0},{3315299,3889,0},{23503104,10365,1},{166999736,27659,0}}};
  int pos=MID,state=0,minpos=pos,maxpos=pos;
  std::size_t ci=0;
  for(std::uint64_t t=0;t<=checkpoints.back().t;t++) {
    if (ci<checkpoints.size() && t == checkpoints[ci].t) {
      const auto &ck=checkpoints[ci];
      bool correct=(state==5 && tape[pos]==0);
      for (int i=minpos;i<pos;i++) if(tape[i]) correct=false;
      for (int i=1;i<=ck.n;i++) if(tape[pos+i]!=1) correct=false;
      if (ck.suffix) {
        if (tape[pos+ck.n+1] !=0) correct=false;
        for(int j=2;j<=7;j++) if(tape[pos+ck.n+j]!=1) correct=false;
        if(tape[pos+ck.n+8] !=0) correct=false;
      } else if(tape[pos+ck.n+1]!=0) correct=false;
      std::cout<<"t="<<t<<" state="<<state<<" offset="<<(pos-MID)<<" n="<<ck.n<<" suffix="<<ck.suffix<<" valid="<<correct<<"\n";
      if (!correct) return 2;
      ci++;
    }
    if (t==checkpoints.back().t) break;
    const int bit=tape[pos];
    const int next=nx[state][bit];
    if(next==6){ std::cout<<"HALT t="<<t<<"\n";return 3; }
    tape[pos]=wr[state][bit];
    pos+=dr[state][bit];state=next;
    if(pos<=100 || pos>=SIZE-100) return 4;
    minpos=std::min(minpos,pos);maxpos=std::max(maxpos,pos);
  }
  std::cout<<"all checkpoints matched; min/head/max offsets="<<(minpos-MID)<<","<<(pos-MID)<<","<<(maxpos-MID)<<"\n";
  return 0;
}
