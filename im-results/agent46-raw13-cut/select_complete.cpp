// Candidate generation only. Lean checks the returned complete trees.
#define main ngram_main
#include "../agent1-ngram/ngram.cpp"
#undef main
#include <bitset>
using Table=array<int,12>;
struct Res{int typ,n,s,e,k,dir,b;};
int encode(char w,char r,char q){return (w-'0')*12+(r=='R')*6+(q-'A');}
string decode(int a){return a<0?"---":string(1,'0'+a/12)+char(a%12>=6?'R':'L')+char('A'+a%6);}
Table parse(string s){Table p;for(int i=0;i<12;i++)p[i]=s[3*i]=='-'?-1:encode(s[3*i],s[3*i+1],s[3*i+2]);return p;}
string show(Table const&p){string s;for(auto a:p)s+=decode(a);return s;}
int mask(Table const&p){int seen=1,todo=1;while(todo){int q=__builtin_ctz(todo);todo&=todo-1;for(int a=0;a<2;a++){int x=p[q*2+a];if(x<0)return 0;int d=1<<(x%6);todo|=d&~seen;seen|=d;}}return seen;}
template<int L,int W,int MAXPER> Res classify(Table const&p){
 using Tape=bitset<W>; constexpr int O=W/2;
 struct Cfg{int q,h;Tape t;};
 static const auto above=[](){array<Tape,W> a{};for(int i=W-1;i>=0;i--){if(i<W-1)a[i]=a[i+1];a[i].set(i);}return a;}();
 static const auto below=[](){array<Tape,W> a{};for(int i=0;i<W;i++){if(i)a[i]=a[i-1];a[i].set(i);}return a;}();
 Cfg c{0,O,{}};Cfg tr[L+1];int last[6]={-1,-1,-1,-1,-1,-1},prev[L+1];
 for(int n=0;n<=L;n++){
  int s=2*c.q+c.t[c.h];if(p[s]<0)return {1,n,s,0,0,0,0};
  int low=c.h,high=c.h,i=n-1;
  for(int j=last[c.q];j>=0 && n-j<=MAXPER;j=prev[j]){
   while(i>=j){low=min(low,tr[i].h);high=max(high,tr[i].h);i--;}
   int d=c.h-tr[j].h;
   if(d>=0 && ((tr[j].t^(c.t>>d))&above[low]).none())return {2,0,0,j,n-j,1,low-O};
   if(d<=0 && ((tr[j].t^(c.t<<(-d)))&below[high]).none())return {2,0,0,j,n-j,0,high-O};
  }
  if(n==L)break;
  tr[n]=c;prev[n]=last[c.q];last[c.q]=n;int x=p[s];c.t[c.h]=x/12;c.h+=(x%12>=6?1:-1);c.q=x%6;
 }
 return {0,0,0,0,0,0,0};
}
struct Node{Res a;int child[24]{};string p;};vector<Node> nodes;
bool extended=false, zeroRE=false, zeroRC=false, zeroRD=false, zeroLC=false, zeroLB=false;
int complete(Table p,int cut,int holes){
 if(nodes.size()>=15000)return -1;
 int i=nodes.size();nodes.push_back({});int m=mask(p);if(m){nodes[i].a={3,m,0,0,0,0,0};return i;}
 auto a=classify<120,256,120>(p);
 if(extended && !a.typ)a=classify<1000,2048,256>(p);
 if(!a.typ){
    auto raw=show(p);
    if(zeroLB){
      static const array<string,9> ps={
        "1RB1LC1RC0LD1LA0RB0LB0RE0RF---1RD1RF",
        "1RB1LC1RC0LD1LA0RB0LB0RE1RF1LE---0RD",
        "1RB1LC1RC0LD1LA0RB0LB0RE1RF1LC---0RD",
        "1RB1LC1RC0LD1LA0RB0LB0RE1RF---0RD1RB",
        "1RB1LC1RC0LD1LA0RB0LB1RE0RF---1RD0RF",
        "1RB1LC1RC0LD1LA0RB0LB1RE0RF---0RD1RF",
        "1RB1LC1RC0LD1LA0RB0LB1RE0RF---0RD1RB",
        "1RB1LC1RC0LD1LA0RB0LB1RE1RF---1LF0RD",
        "1RB1LC1RC0LD1LA0RB0LB1RE0RD1RF1RE---"};
      for(int v=0;v<9;v++)if(raw==ps[v]){nodes[i].a={16,v,0,0,0,0,0};return i;}
    }
    if(zeroLC){
      static const array<string,5> ps={
        "1RB1LC1RC0LD1LA0RB0LC0RE1RF---0RD1RF",
        "1RB1LC1RC0LD1LA0RB0LC0RE1RD1RF---1RA",
        "1RB1LC1RC0LD1LA0RB0LC1RE0RF---1RB1RD",
        "1RB1LC1RC0LD1LA0RB0LC1RE1RD0RF---1RE",
        "1RB1LC1RC0LD1LA0RB0LC1RE1RD0RF---1LD"};
      for(int v=0;v<5;v++)if(raw==ps[v]){nodes[i].a={15,v,0,0,0,0,0};return i;}
    }
    if(zeroRD){
      static const array<string,5> ps={
        "1RB1LC1RC0LD1LA0RB0RD1LE0LF---1RD0LE",
        "1RB1LC1RC0LD1LA0RB0RD1LE1RD0LF0LE---",
        "1RB1LC1RC0LD1LA0RB0RD1RE0RF---0LC0RF",
        "1RB1LC1RC0LD1LA0RB0RD1RE0RB0RF---1RE",
        "1RB1LC1RC0LD1LA0RB0RD1RE0RB0RF---1LD"};
      for(int v=0;v<5;v++)if(raw==ps[v]){nodes[i].a={14,v,0,0,0,0,0};return i;}
    }
    if(zeroRC && raw=="1RB1LC1RC0LD1LA0RB0RC1LE0LA0LF1LB---"){nodes[i].a={13,0,0,0,0,0,0};return i;}
    if(zeroRE){
      static const array<string,5> ps={
        "1RB1LC1RC0LD1LA0RB1LB0RE0RF1RD---0RE",
        "1RB1LC1RC0LD1LA0RB1LB0RE1RF1RD---0RE",
        "1RB1LC1RC0LD1LA0RB1LB0RE1RF0RA---0RE",
        "1RB1LC1RC0LD1LA0RB1LB0RE1RF1RD---1LE",
        "1RB1LC1RC0LD1LA0RB1LB0RE1RE0RF---0RA"};
      for(int v=0;v<5;v++)if(raw==ps[v]){nodes[i].a={11,v,0,0,0,0,0};return i;}
      if(raw=="1RB1LC1RC0LD1LA0RB1LB0RE1RD1RF---1RD"){nodes[i].a={12,0,0,0,0,0,0};return i;}
    }
    if(extended && raw=="1RB1LC1RC0LD1LA0RB1LB0LE0RF---1RE0RB"){nodes[i].a={8,0,0,0,0,0,0};return i;}
    if(extended && raw=="1RB1LC1RC0LD1LA0RB1LB1RE1RF1RC---0RE"){nodes[i].a={9,0,0,0,0,0,0};return i;}
    if(extended && raw=="1RB1LC1RC0LD1LA0RB1LB1RE0RF0RA---0RD"){nodes[i].a={10,0,0,0,0,0,0};return i;}
    if(raw=="1RB1LC1RC0LD1LA0RB1LB1LE1RF0RC---1RE"){nodes[i].a={6,0,0,0,0,0,0};return i;}
    if(raw=="1RB1LC1RC0LD1LA0RB1LB1LE0RE1RF0RC---"||raw=="1RB1LC1RC0LD1LA0RB1LB1LE0RF---0RC1RF"||raw=="1RB1LC1RC0LD1LA0RB1LB1LE1LF---1RF0RC"){nodes[i].a={7,0,0,0,0,0,0};nodes[i].p=raw;return i;}
    bool shared=raw.substr(0,24)=="1RB1LC1RC0LD1LA0RB1LB1LE" && (raw.substr(24,3)=="0RE"||raw.substr(24,3)=="0RF"||raw.substr(24,3)=="1LF");
    for(int k=1;k<=((zeroRE||zeroRC||zeroRD||zeroLC||zeroLB)?7:extended?6:shared?7:(raw=="1RB1LC1RC0LD1LA0RB1LB1LE1RF1RC---1RE"?5:4));k++){NGram ng(raw,k);if(ng.check()){nodes[i].a={5,k,0,0,0,0,0};nodes[i].p=raw;return i;}}
    if(!extended)a=classify<1000,2048,256>(p);if(!a.typ)return -1;
 }
 nodes[i].a=a;if(a.typ==2||holes==1)return i;
 nodes[i].a.typ=4;
 for(int q=min(cut,5);q>=0;q--)for(int w=0;w<2;w++)for(int r=0;r<2;r++){
  int x=12*w+6*r+q;p[a.s]=x;int j=complete(p,max(cut,q+1),holes-1);if(j<0)return -1;nodes[i].child[x]=j+1;
 }
 return i;
}
void emit(int i){auto n=nodes[i];auto a=n.a;
 if(a.typ==16){cout<<"[\"pump0LB\","<<a.n<<']';return;}
 if(a.typ==15){cout<<"[\"pump0LC\","<<a.n<<']';return;}
 if(a.typ==14){cout<<"[\"pump0RD\","<<a.n<<']';return;}
 if(a.typ==13){cout<<"[\"pump0RC\"]";return;}
 if(a.typ==11){cout<<"[\"pump0RE\","<<a.n<<']';return;}
 if(a.typ==12){cout<<"[\"late0RE\"]";return;}
 if(a.typ==10){cout<<"[\"sparse1RE\"]";return;}
 if(a.typ==9){cout<<"[\"pump1RE2\"]";return;}
 if(a.typ==8){cout<<"[\"pump0LE\"]";return;}
 if(a.typ==6){cout<<"[\"pump1RE\"]";return;}
 if(a.typ==7){cout<<"[\"sharedpump\",\""<<n.p<<"\"]";return;}
 if(a.typ==5){cout<<"[\"ngram\",\""<<n.p<<"\"]";return;}
 if(a.typ==3){cout<<"[\"state\","<<a.n<<']';return;}
 if(a.typ==2){cout<<"[\"cycle\","<<a.e<<','<<a.k<<','<<(a.dir?"true":"false")<<','<<a.b<<']';return;}
 if(a.typ==1){cout<<"[\"last\","<<a.n<<','<<a.s<<']';return;}
 cout<<"[\"split\","<<a.n<<','<<a.s<<",[";
 for(int j=0;j<24;j++){if(j)cout<<',';if(n.child[j])emit(n.child[j]-1);else cout<<"null";}cout<<"]]";
}
int main(){string s;int cut,holes;while(cin>>s>>cut>>holes){zeroRE=s=="1RB1LC1RC0LD1LA0RB1LB0RE------------";zeroRC=s=="1RB1LC1RC0LD1LA0RB0RC---------------";zeroRD=s=="1RB1LC1RC0LD1LA0RB0RD---------------";zeroLC=s=="1RB1LC1RC0LD1LA0RB0LC---------------";zeroLB=s=="1RB1LC1RC0LD1LA0RB0LB---------------";extended=zeroRE||zeroRC||zeroRD||zeroLC||zeroLB||s=="1RB1LC1RC0LD1LA0RB1LB0LE------------"||s=="1RB1LC1RC0LD1LA0RB1LB1RE------------";nodes.clear();int i=complete(parse(s),cut,holes);if(i<0){cerr<<"unresolved "<<s<<'\n';return 1;}cout<<s<<' ';emit(i);cout<<'\n';}}
