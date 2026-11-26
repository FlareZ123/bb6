// Candidate generation only; all emitted certificates are checked in Lean.
#define AGENT46_CLASSIFY_ONLY
#include "select_complete.cpp"
#include <fstream>
#include <map>
#include <set>
using U=uint64_t;
using DFA=vector<int>;
vector<DFA> bank;
struct Rule{int dst,src,off;};
U compose(U mask,const U* rows){U v=0;while(mask){int j=__builtin_ctzll(mask);v|=rows[j];mask&=mask-1;}return v;}
bool far(const Table& m,const DFA& a,bool rev){
 int d=int(a.size()/2),N=6*d+1,H=N-1; U T[122]{}; Rule rules[240]; int nr=0; U halt=U(1)<<H;T[H]=T[N+H]=halt;
 for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int b=0;b<2;b++){
  int x=m[2*q+b],i=b*N+6*l+q;
  if(x<0){T[i]=halt;continue;}
  int w=x/12,n=x%6; bool right=x%12>=6;
  if(right!=rev)T[i]=U(1)<<(6*a[2*l+w]+n);
  else for(int j=0;j<d;j++)for(int e=0;e<2;e++)if(a[2*j+e]==l)rules[nr++]={i,e*N+6*j+n,w*N};
 }
 for(;;){U cur=1,seen=0;while(cur){seen|=cur;if(seen&halt)return false;cur=compose(cur,T)&~seen;}
  bool changed=false;for(int j=0;j<nr;j++){auto [dst,src,off]=rules[j];U x=T[dst]|compose(T[src],T+off);if(x!=T[dst]){T[dst]=x;changed=true;}}
  if(!changed)return true;
 }
}
struct Node {Res a;array<int,24> child{};string raw,df;bool rev=false;};
vector<Node> nodes;map<string,pair<bool,DFA>> overrides;set<string> autoTables;
string showD(const DFA&d){string s;for(int v:d)s+=char('0'+v);return s;}
DFA parseD(string s){DFA d;for(char c:s)d.push_back(c-'0');if(d.empty()||d.size()%2||d.size()>20||d[0]!=0||any_of(d.begin(),d.end(),[&](int v){return v<0||v>=int(d.size()/2);}))throw runtime_error("bad DFA");return d;}
int solve(Table p,int cut,int holes){
 if(nodes.size()>=200000)return -1;
 int i=nodes.size();nodes.push_back({});int m=mask(p);if(m){nodes[i].a={3,m,0,0,0,0,0};return i;}
 auto a=classify<120,256,120>(p);if(!a.typ)a=classify<1000,2048,256>(p);
 if(!a.typ){string raw=show(p);nodes[i].raw=raw;
   if(autoTables.count(raw)){nodes[i].a.typ=6;return i;}
   auto ov=overrides.find(raw);if(ov!=overrides.end()){
     const auto&[rev,d]=ov->second;if(!far(p,d,rev)){cerr<<"bad override "<<raw<<endl;return -1;}
     nodes[i].a.typ=5;nodes[i].df=showD(d);nodes[i].rev=rev;return i;}
   for(const auto&d:bank)for(int rev=0;rev<2;rev++)if(far(p,d,rev)){nodes[i].a.typ=5;nodes[i].df=showD(d);nodes[i].rev=rev;return i;}
   auto late=classify<1000,2048,1000>(p);if(late.typ==2){nodes[i].a=late;return i;}
   cerr<<"unresolved "<<raw<<endl;return -1;
 }
 nodes[i].a=a;if(a.typ==2||holes==1)return i;
 nodes[i].a.typ=4;
 for(int q=min(cut,5);q>=0;q--)for(int w=0;w<2;w++)for(int r=0;r<2;r++){
  int x=12*w+6*r+q;p[a.s]=x;int j=solve(p,max(cut,q+1),holes-1);if(j<0)return -1;nodes[i].child[x]=j+1;
 }
 return i;
}
void emit(int i){const auto&n=nodes[i];auto a=n.a;
 if(a.typ==6){cout<<"[\"auto\",\""<<n.raw<<"\"]";return;}
 if(a.typ==5){cout<<"[\"far\",\""<<n.raw<<"\","<<(n.rev?1:0)<<",\""<<n.df<<"\"]";return;}
 if(a.typ==3){cout<<"[\"state\","<<a.n<<']';return;}
 if(a.typ==2){cout<<"[\"cycle\","<<a.e<<','<<a.k<<','<<(a.dir?"true":"false")<<','<<a.b<<']';return;}
 if(a.typ==1){cout<<"[\"last\","<<a.n<<','<<a.s<<']';return;}
 cout<<"[\"split\","<<a.n<<','<<a.s<<",[";
 for(int j=0;j<24;j++){if(j)cout<<',';if(n.child[j])emit(n.child[j]-1);else cout<<"null";}cout<<"]]";
}
int main(int argc,char**argv){if(argc!=4)return 2;ifstream f(argv[1]),g(argv[2]),h(argv[3]);if(!f||!g||!h)return 2;string s,d;int rev;while(f>>d)bank.push_back(parseD(d));while(g>>s>>rev>>d)overrides[s]={bool(rev),parseD(d)};while(h>>s)autoTables.insert(s);int cut,holes;while(cin>>s>>cut>>holes){nodes.clear();int i=solve(parse(s),cut,holes);if(i<0)return 1;emit(i);cout<<'\n';}}
