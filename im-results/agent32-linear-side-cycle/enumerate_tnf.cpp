// Normalized first-hole enumeration; all emitted witnesses are untrusted.
#include <array>
#include <bitset>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <map>
#include <algorithm>
#include "side_scan.hpp"
using namespace std;
using Table=array<int,12>;
using Res=side_scan::Result;
side_scan::Scanner scanner;
int limit=1000;
int encode(char w,char r,char q){return (w-'0')*12+(r=='R')*6+(q-'A');}
string decode(int a){if(a<0)return a==-1?"---":"HHH";return string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
Table parse(string str){str.erase(remove(str.begin(),str.end(),'_'),str.end());Table p;for(int i=0;i<12;i++)p[i]=str[3*i]=='-'?-1:encode(str[3*i],str[3*i+1],str[3*i+2]);return p;}
string show(const Table& p){string s;for(int i=0;i<12;i++){if(i&&i%2==0)s+='_';s+=decode(p[i]);}return s;}
Res classify(const Table& p){return scanner.run(p,limit);}
long long pow25(int k){long long r=1;while(k--)r*=25;return r;}
int maxDelay(const Table& p,int state=0,int seen=1){int out=0;for(int q=0;q<6;q++)if(!(seen>>q&1)){int a=p[2*q];if(a==-1||(a>=0&&a/12==0&&a%6==state))out=max(out,1+maxDelay(p,q,seen|(1<<q)));}return out;}
map<string,long long> stats,mass;long long maxscore=-1;string maxcode;ofstream tree,op;
void build(Table p,int cut,long long mult){int holes=count(p.begin(),p.end(),-1);Res a=classify(p);if(a.typ==0){stats["open"]++;mass["open"]+=mult*pow25(holes);string s=show(p);op<<s<<'\n';tree<<"[\"open\",\""<<s<<"\"]";return;}if(a.typ==2){stats["cycle"]++;mass["cycle"]+=mult*pow25(holes);tree<<"[\"cycle\","<<a.e<<','<<a.k<<','<<(a.dir?"true":"false")<<','<<a.b<<']';return;}p[a.s]=-2;int d=maxDelay(p),score=a.n+1+d;if(score>maxscore){maxscore=score;maxcode=show(p);}mass["halt"]+=mult*pow25(holes-1);if(holes==1){stats["last"]++;mass["total"]+=mult*24;tree<<"[\"last\","<<a.n<<','<<a.s<<']';return;}stats["split"]++;tree<<"[\"split\","<<a.n<<','<<a.s<<",[";for(int i=0;i<24;i++){if(i)tree<<',';if(i%6>cut){tree<<"[\"skip\"]";continue;}p[a.s]=i;build(p,cut+(i%6==cut),mult*(i%6==cut?6-cut:1));}tree<<"]]";}
int main(int argc,char**argv){if(argc<2)return 2;if(argc>2)limit=atoi(argv[2]);string arg=argv[1];arg.erase(remove(arg.begin(),arg.end(),'_'),arg.end());if(arg.size()!=36||limit<0)return 2;for(int i=0;i<12;i++){string s=arg.substr(3*i,3);if(s!="---"&&((s[0]!='0'&&s[0]!='1')||(s[1]!='L'&&s[1]!='R')||s[2]<'A'||s[2]>'F'))return 2;}tree.open("tree.json");op.open("open.txt");Table p=parse(arg);int cut=1;for(int i=0;i<12;i++)if(p[i]>=0)cut=max(cut,max(i/2+1,p[i]%6+1));build(p,cut,1);tree<<'\n';for(auto [s,n]:stats)cout<<s<<":"<<n<<' ';cout<<'\n';long long tot=0;for(auto [s,n]:mass){cout<<s<<":"<<n<<' ';tot+=n;}cout<<" total="<<tot<<"\nmaxscore="<<maxscore<<" table="<<maxcode<<endl;}
