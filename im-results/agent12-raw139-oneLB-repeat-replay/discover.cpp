#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using namespace std;
struct Rule {int q,p; bool right; string l,r,cons,prod;};
string repr(const Rule& x){return to_string(x.q)+" "+to_string(x.p)+" "+to_string(x.right)+" "+(x.l.empty()?"-":x.l)+" "+(x.r.empty()?"-":x.r)+" "+x.cons+" "+x.prod;}
Rule rule(const unsigned char* tr,int p,const int* t){
 int h=0,q=tr[0]/2,lo=0,hi=0;map<int,int> initial,tape;
 for(int j=0;j<p;j++){
  assert(q==tr[j]/2);int b=tr[j]%2;
  if(!tape.count(h))initial[h]=tape[h]=b;else assert(tape[h]==b);
  int c=t[tr[j]]; assert(c!=24);tape[h]=c/2%2;h+=c%2?1:-1;q=c/4;lo=min(lo,h);hi=max(hi,h);
 }
 assert(q==tr[0]/2&&h!=0);
 // Include the final head cell, reading its known next-cycle input if it was untouched.
 if(!tape.count(h))initial[h]=tape[h]=tr[0]%2;
 else assert(tape[h]==tr[0]%2);
 string li,ri,lf,rf;
 for(int j=-1;j>=lo;j--)li+=char('0'+initial.at(j));
 for(int j=0;j<=hi;j++)ri+=char('0'+initial.at(j));
 for(int j=h-1;j>=lo;j--)lf+=char('0'+tape.at(j));
 for(int j=h;j<=hi;j++)rf+=char('0'+tape.at(j));
 if(h>0){assert(lf.substr(0,li.size())==li&&ri.substr(0,rf.size())==rf);return {q,p,true,li,rf,ri.substr(rf.size()),lf.substr(li.size())};}
 else {assert(li.substr(0,lf.size())==lf&&rf.substr(0,ri.size())==ri);return {q,p,false,lf,ri,li.substr(lf.size()),rf.substr(ri.size())};}
}
int main(int argc,char**argv){int v=argc>1?atoi(argv[1]):0;int tab[2][12]={{7,20,11,1,14,9,17,16,6,11,0,24},{7,23,11,13,14,21,24,16,6,11,3,0}};auto t=tab[v];int Z=1<<21;vector<unsigned char>a(2*Z),tr;tr.reserve(35000000);int h=Z,q=0;for(;;){int s=2*q+a[h],k=t[s];if(k==24)break;tr.push_back(s);a[h]=(k>>1)&1;h+=k&1?1:-1;q=k>>2;assert(h>=0&&h<2*Z);}
 int N=tr.size(),raw=0;map<string,int> ids;vector<string> rules;vector<pair<int,int>> commands;vector<long long> coverage;long long sum=0;int cap=48;
 for(int i=0;i<N;){int bestp=0,bestk=0;for(int p=1;p<=cap&&i+2*p<=N;p++){if(tr[i]/2!=tr[i+p]/2||memcmp(&tr[i],&tr[i+p],p))continue;int k=2;while(i+(k+1)*p<=N&&!memcmp(&tr[i],&tr[i+k*p],p))k++;if(k*p>bestk*bestp){bestp=p;bestk=k;}if(bestk*bestp>10000)break;}
  if(bestk<2||bestp*bestk<20){raw++;i++;continue;}
  if(raw){commands.push_back({-1,raw});raw=0;}
  auto s=repr(rule(&tr[i],bestp,t));int id;auto it=ids.find(s);if(it==ids.end()){id=rules.size();ids.emplace(s,id);rules.push_back(s);coverage.push_back(0);}else id=it->second;
  commands.push_back({id,bestk});i+=bestp*bestk;coverage[id]+=(long long)bestp*bestk;sum+=bestp*bestk;
 }
 if(raw)commands.push_back({-1,raw});
 printf("%d %d %d %zu %zu\n",N,q,int(a[h]),rules.size(),commands.size());for(auto&s:rules)cout<<s<<"\n";for(auto [id,k]:commands)cout<<id<<" "<<k<<"\n";
 fprintf(stderr,"variant=%d total=%d macro-covered=%lld rules=%zu commands=%zu\n",v,N,sum,rules.size(),commands.size());for(int j=0;j<min(30,(int)rules.size());j++)fprintf(stderr,"rule %d %s coverage %lld\n",j,rules[j].c_str(),coverage[j]);
}
