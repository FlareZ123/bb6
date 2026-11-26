#include <boost/multiprecision/cpp_int.hpp>
#include <vector>
#include <iostream>
#include <fstream>
#include <array>
#include <chrono>
#include <stdexcept>
using I=boost::multiprecision::cpp_int;
using namespace std;
struct St {vector<I> g{0}; vector<int>s; int b=0; I t=0;};
void check(bool b,const char*why){if(!b)throw runtime_error(why);}
void dump(const St&st,ostream&o){o<<"{\"t\":\""<<st.t<<"\",\"b\":"<<st.b<<",\"g\":[";for(size_t i=0;i<st.g.size();i++)o<<(i?",":"")<<'"'<<st.g[i]<<'"';o<<"],\"s\":[";for(size_t i=0;i<st.s.size();i++)o<<(i?",":"")<<st.s[i];o<<"]}\n";}
int charge(const St&st,int i){return ((st.g[i+1]+st.s[i+1]+(st.s[i]==2))%3).convert_to<int>();}
// Deadline distance avoids divisions by huge powers. Gap changes are
// computed by ternary addition, a single small-integer division per digit.
int event(St& st,vector<I>& powers, bool&badBirth,bool&unprotected, I&margin) {
 int m=st.s.size();while((int)powers.size()<=m)powers.push_back(3*powers.back());
 I dist=0,delta=0;int j=m;bool found=false;
 for(int i=0;i<m;i++){
  if(found&&dist>=delta)break;
  if(!found||st.g[i+1]<delta){
   I d=st.g[i+1]*powers[i+1]+dist;
   if(st.s[i]==0)d+=powers[i];else if(st.s[i]==2)d+=2*powers[i];
   if(!found||d<delta){found=true;delta=move(d);j=i;}
  }
  dist+=(2-st.s[i])*powers[i];
 }
 if((st.b>=0||m==0)&&(!found||dist<delta)){delta=dist;j=m;found=true;}
 check(found,"no deadline");
 if(delta!=0){
  st.g[0]+=delta;I q=delta;int carry=0;
  for(int i=0;i<m;i++){
   if(q==0&&carry==0)break;
   auto digit=(q%3).convert_to<int>();q/=3;
   int sum=st.s[i]+digit+carry;int next=sum%3;carry=sum/3;
   st.g[i+1]-=q+carry+(next==2)-(st.s[i]==2);
   check(st.g[i+1]>=0,"negative gap");st.s[i]=next;
  }
  st.t+=delta;
 }
 badBirth=false;unprotected=false;margin=0;int kind;
 if(j==m){
  for(int d:st.s)check(d==2,"boundary not all H");
  if(st.b==0){
   if(m>0&&st.g[0]%3!=0){badBirth=true;
     if(st.g.back()>0){I p=m-1;for(int i=1;i<=m;i++)p+=st.g[i];margin=st.g[0]+1-(3*p+2);unprotected=margin<0;}
     else if(m>=2){I p=m-1;for(int i=1;i<m;i++)p+=st.g[i];p+=1;margin=st.g[0]+1-(3*p+2);unprotected=margin<0;}
     if(unprotected)return 7;
   }
   if(m==0){st.g.insert(st.g.begin(),0);st.s.insert(st.s.begin(),2);st.b=1;}
   else if(st.g.back()>0){st.g[0]++;st.g.insert(st.g.begin(),0);st.s.insert(st.s.begin(),2);st.g.back()--;st.b=1;}
   else {st.g[0]++;st.g.insert(st.g.begin(),0);st.s.insert(st.s.begin(),2);st.g[st.g.size()-2]++;st.g.pop_back();st.s.pop_back();st.b=-1;}
   kind=0;
  }else{
   if(m==0&&st.b==-1)return 6;
   st.g[0]++;fill(st.s.begin(),st.s.end(),0);if(st.b==1)st.b=0;kind=1;
  }
 }else{
  check(st.s[j]==1&&st.g[j+1]==0,"bad collision state");
  for(int i=0;i<j;i++)check(st.s[i]==2,"bad carry prefix");
  if(j+1<m){
   int next=st.s[j+1];bool boundary=next==0&&j+2==m&&st.g.back()==0&&st.b==-1;
   if(next!=1&&!boundary)return 5;
   st.g[0]++;fill(st.s.begin(),st.s.begin()+j,0);
   if(next==1){st.g[j]+=1+st.g[j+2];kind=2;}
   else{st.g[j]++;st.b=0;kind=3;}
   st.g.erase(st.g.begin()+j+1,st.g.begin()+j+3);st.s.erase(st.s.begin()+j,st.s.begin()+j+2);
  }else{
   st.g[0]++;fill(st.s.begin(),st.s.begin()+j,0);st.s.pop_back();st.g.pop_back();
   if(st.b==-1)st.b=0;else if(st.b==0)st.b=1;else{st.b=-1;st.g.back()++;}kind=4;
  }
 }
 st.t++;return kind;
}
int main(int argc,char**argv){uint64_t limit=argc>1?stoull(argv[1]):2000000,startIndex=0;St st;vector<I>pow{1};array<uint64_t,8> counts{};uint64_t bads=0;auto start=chrono::steady_clock::now();
 if(argc>2){ifstream in(argv[2]);check(bool(in),"no checkpoint");size_t m;in>>startIndex>>st.t>>st.b>>m>>bads;st.s.resize(m);st.g.resize(m+1);for(auto &g:st.g)in>>g;for(auto &d:st.s)in>>d;for(auto&c:counts)in>>c;check(bool(in),"bad checkpoint");}
 for(uint64_t i=startIndex+1;i<=limit;i++){
  bool bad,unsafe;I margin;int k=event(st,pow,bad,unsafe,margin);counts[k]++;
  if(bad){++bads;cout<<"BAD_BIRTH "<<i<<" m="<<st.s.size()<<" margin="<<margin<<" safe="<<!unsafe<<" t="<<st.t<<endl;}
  if(k>=5){cout<<"STOP "<<i<<" kind="<<k<<endl;dump(st,cout);return 0;}
  if(i%100000==0||i==limit){cout<<"CHECKPOINT "<<i<<" m="<<st.s.size()<<" t="<<st.t<<" trailing="<<st.g.back()<<" b="<<st.b<<" bads="<<bads<<" counts=";for(auto c:counts)cout<<c<<",";cout<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<" exceptional=";for(int j=0;j+1<(int)st.s.size();j++)if(charge(st,j)!=1)cout<<j<<":"<<charge(st,j)<<",";cout<<endl;
    ofstream out(argc>3?argv[3]:"odometer172-checkpoint.txt");out<<i<<' '<<st.t<<' '<<st.b<<' '<<st.s.size()<<' '<<bads<<'\n';for(auto &g:st.g)out<<g<<' ';out<<'\n';for(auto &d:st.s)out<<d<<' ';out<<'\n';for(auto &c:counts)out<<c<<' ';out<<'\n';}
 }
}
