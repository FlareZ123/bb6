// Research-only exact sparse-machine trace census, NOT a formal certificate.
// Simulates each 2638-source remaining complete/one-hole literal as supplied.
// A first undefined query after n ordinary moves is a genuine *candidate*
// n+1-step halting total completion; still requires an accepted Lean witness.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <map>
using namespace std;
struct Summary {
 string table,status; uint64_t steps; int64_t lo,hi,ones;
 int state; uint64_t undef_at;
};
int main(int argc,char **argv) {
 if(argc!=4){cerr<<"usage: sim <remaining.txt> <max_steps> <out.tsv>\n";return 2;}
 string file=argv[1];uint64_t limit=stoull(argv[2]);
 if(limit>10000000){cerr<<"limit capped to 10m\n";return 2;}
 ifstream in(file);ofstream out(argv[3]);
 if(!in || !out){cerr<<"missing input or output\n";return 2;}
 out<<"table\tstatus\tsteps\tleft_min\tright_max\tonescnt\tstate\n";
 vector<unsigned char> tape(2*limit+3,0);
 uint64_t counter=0,halted=0,ordinary=0,kept=0,maxScore=0;
 vector<Summary> score;
 string t;
 while(getline(in,t)){
  if(t.empty())continue;
  string raw;for(char x:t)if(x!='_')raw+=x;
  if(raw.size()!=36){cerr<<"bad size "<<t<<"\n";return 2;}
  auto old=tape.begin()+limit+1;
  (void)old;
  fill(tape.begin(),tape.end(),0);
  int64_t pos=static_cast<int64_t>(limit)+1,lo=0,hi=0,ones=0;
  int state=0;string status="LIMIT";uint64_t steps=limit;
  for(uint64_t i=0;i<limit;i++){
   uint8_t read=tape[static_cast<size_t>(pos)];
   string move=raw.substr(static_cast<size_t>((2*state+read)*3),3);
   if(move=="---"){status="FIRST_UNDEFINED";steps=i;break;}
   if(move.size()!=3|| (move[0]!='0'&&move[0]!='1') ||
     (move[1]!='L'&&move[1]!='R') || move[2]<'A'||move[2]>'F'){
      cerr<<"invalid move "<<move<<" table "<<t<<"\n";return 2;}
   uint8_t w=move[0]=='1';
   if(read!=w)ones+=(w?1:-1);
   tape[static_cast<size_t>(pos)]=w;
   pos+=(move[1]=='R'?1:-1);
   int64_t x=pos-(static_cast<int64_t>(limit)+1);
   lo=min(lo,x);hi=max(hi,x);
   state=move[2]-'A';
  }
  out<<t<<"\t"<<status<<"\t"<<steps<<"\t"<<lo<<"\t"<<hi<<"\t"<<ones<<"\t"<<state<<"\n";
  counter++;
  if(status=="FIRST_UNDEFINED"){
    halted++; maxScore=max(maxScore,steps+1);
    score.push_back({t,status,steps,lo,hi,ones,state,steps});
  }else kept++;
 }
 if(counter!=124){cerr<<"wrong input count "<<counter<<"\n";return 2;}
 sort(score.begin(),score.end(),[](auto&a,auto&b){return a.steps>b.steps;});
 cout<<"SIMULATOR_NOT_PROOF total="<<counter<<" max_steps="<<limit
     <<" queried_undefined="<<halted<<" remained="<<kept
     <<" candidate_max_score="<<maxScore<<"\n";
 for(size_t j=0;j<min<size_t>(score.size(),22);j++)
     cout<<"HALT_CANDIDATE steps="<<score[j].steps
         <<" head_min="<<score[j].lo<<" head_max="<<score[j].hi
         <<" ones="<<score[j].ones<<" table="<<score[j].table<<"\n";
 return 0;
}
