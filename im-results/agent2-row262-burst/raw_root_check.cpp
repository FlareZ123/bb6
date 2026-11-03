// Independent literal-RLE primitive-step checkpoint for BB(6) row262.
// SFT: compiles as C++17; no external packages and no synthetic macro semantics.
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_set>
#include <array>
using namespace std;
struct Action { int write, move, next; bool defined=false; };
int main() {
    const string rle="1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---";
    array<array<Action,2>,6> table{};
    size_t o=0; int actions=0;
    for(int s=0;s<6;s++) {
        for(int b=0;b<2;b++) {
            string tok=rle.substr(o+3*b,3);
            if(tok!="---") { table[s][b]={tok[0]-'0',tok[1]=='R'?1:-1,tok[2]-'A',true}; actions++; }
        }
        o+=6;
        if(s!=5 && rle[o++]!='_') return 1;
    }
    if(actions!=11) return 2;
    uint64_t returns=0, primitive=0;
    int st=0; int64_t head=0;
    unordered_set<int64_t> ones;
    const uint64_t target=10000000ULL;
    while(returns<target) {
        bool read=ones.find(head)!=ones.end();
        auto a=table[st][int(read)];
        if(!a.defined) {
            cout<<"HALTED primitive="<<primitive<<" head="<<head<<" returns="<<returns<<"\n";
            return 3;
        }
        if(a.write) ones.insert(head); else ones.erase(head);
        head+=a.move; st=a.next; primitive++;
        if(st==0) {
            returns++;
            if(returns==100000ULL || returns==1000000ULL || returns==target)
                cout<<"A="<<returns<<" primitive="<<primitive<<" head="<<head
                    <<" occupied="<<ones.size()<<"\n";
        }
    }
    if(primitive!=46717881ULL || head!=2741 || ones.size()!=2722) return 4;
    cout<<"PASS 10m rooted original RLE primitive-exact A checkpoints; no all-time inference\n";
}
