#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <algorithm>
#include "side_scan.hpp"
using namespace std;
using Table=array<int,12>;
side_scan::Scanner scanner;
int limit=10000;
Table parse(string str){str.erase(remove(str.begin(),str.end(),'_'),str.end());Table p;for(int i=0;i<12;i++)p[i]=str[3*i]=='-'?-1:(str[3*i]-'0')*12+(str[3*i+1]=='R')*6+str[3*i+2]-'A';return p;}
string show(const Table& p){string s;for(int a:p){if(a<0)s+="---";else {s+=char('0'+a/12);s+=char(a%12>=6?'R':'L');s+=char('A'+a%6);}}return s;}
int id; long long opens,cycles,last,splits;
void build(Table p,int cut){int holes=count(p.begin(),p.end(),-1);auto a=scanner.run(p,limit);if(a.typ==0){opens++;cout<<id<<' '<<show(p)<<'\n';return;}if(a.typ==2){cycles++;return;}if(holes==1){last++;return;}splits++;for(int i=0;i<24;i++){if(i%6>cut)continue;p[a.s]=i;build(p,cut+(i%6==cut));}}
int main(int argc,char**argv){if(argc>1)limit=atoi(argv[1]);string s;while(cin>>id>>s){auto p=parse(s);int cut=1;for(int i=0;i<12;i++)if(p[i]>=0)cut=max(cut,max(i/2+1,p[i]%6+1));opens=cycles=last=splits=0;build(p,cut);cerr<<id<<' '<<opens<<' '<<cycles<<' '<<last<<' '<<splits<<'\n';}}
