// Exact 2-symbol 6-state blank-prefix simulator for *untrusted discovery*.
// Output is an observed first unassigned slot; only Lean knownRun validates it.
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_set>

struct Move { int w, dr, nx; bool defined; };

int main(int argc,char**argv){
  if(argc!=2){std::cerr<<"usage: ./simulate_missing max_steps\n";return 2;}
  uint64_t limit=std::stoull(argv[1]);
  int family,leaf;std::string tab;
  while(std::cin>>family>>leaf>>tab){
    std::string s;for(char c:tab)if(c!='_')s.push_back(c);
    if(s.size()!=36){std::cerr<<"invalid table "<<tab<<"\n";return 3;}
    Move m[12];
    for(int i=0;i<12;i++){
      const std::string z=s.substr(3*i,3);
      m[i]=z=="---" ? Move{0,0,0,false} :
          Move{z[0]-'0',z[1]=='R'?1:-1,z[2]-'A',true};
    }
    std::unordered_set<int64_t> ones;
    ones.reserve(262144);
    int64_t head=0;int q=0;
    uint64_t t=0;
    for(;t<=limit;t++){
      const int bit=ones.contains(head)?1:0;
      const int slot=2*q+bit;
      const Move v=m[slot];
      if(!v.defined){
        std::cout<<family<<" "<<leaf<<" LATE "<<t<<" "<<slot<<" "<<tab<<"\n";
        break;
      }
      if(t==limit){
        std::cout<<family<<" "<<leaf<<" UNRESOLVED "<<t<<" "<<slot<<" "<<tab<<"\n";
        break;
      }
      if(v.w)ones.insert(head);else ones.erase(head);
      head+=v.dr;q=v.nx;
    }
    std::cout.flush();
  }
}
