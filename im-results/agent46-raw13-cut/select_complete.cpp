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
bool extended=false, zeroRE=false, zeroRC=false, zeroRD=false, zeroLC=false, zeroLB=false, oneRD=false, zeroRA=false, oneLA=false, oneRA=false, zeroRB=false, oneLC=false, oneRE=false;
int complete(Table p,int cut,int holes){
 if(nodes.size()>=(oneRE?100000:15000))return -1;
 int i=nodes.size();nodes.push_back({});int m=mask(p);if(m){nodes[i].a={3,m,0,0,0,0,0};return i;}
 auto a=classify<120,256,120>(p);
 if(extended && !a.typ)a=classify<1000,2048,256>(p);
 if(!a.typ){
    auto raw=show(p);
    if(oneRE){
      static const array<string,35> ps={"---0LF0RE1LF1LD","0LF0LF1RD---1LD","1RD0RF1RB---1LC","---1LF0RE1LF1LD","0RD1RF0LC---1LE","1RD1RF0LC---1LE","0LA1RF0LC---1LE","1RA1RF0LC---1LE","1LB1RF---0LD1RE","0RF1RF---0LC0RD","---0RE1LF0LF0LD","0LF0RE1LF0LD---","0LF0RE1LC0LD---","0LF1LE1RD---1LD","0LD1RE1RF1LD---","0LD1RE1RF1LB---","0LB1RE1RF1LB---","1LF0LD0RE1LD---","1LF1RD---0LD0LF","0RD0LC1RF---0RE","0RD0LC1RF---1RE","1RD0LC0RF---1LA","1RD0LC1RF---0RE","1RD0LC1RF---1RE","1RD0LC1RF---0LD","1LF0RA0RE1LD---","0RD0RA1RF---1RB","1RD0RA0RF---0LE","1RD0RA0RF---1RB","1RD0RA1RF---1RB","1RD0RA1RF---0LA","1LF1LA0RE1LD---","0RD1LA1RF---1RB","1RD1LA0RF---1RB","1RD1LA1RF---1RB"};
      for(int v=0;v<35;v++)if(raw=="1RB1LC1RC0LD1LA0RB1RE"+ps[v]){
        nodes[i].a={23,1007000+v,0,0,0,0,0};return i;
      }
    }
    if(zeroRB){
      static const array<string,18> ps={"0RE0RF1RD---0RE","0RE0RF1RD---1RE","0RE1RF1RD---0RE","0RE1RF1RD---1LE","0RE1RF1RD---1RE","0RE1RD1RF---1RB","1LE1RF0RA---0RE","1RE0RF1RD---0RE","1RE0RF1RD---1RE","1RE0RF1RF---1RD","1RE1RF1RD---0RE","1RE1RF1RD---1LE","1RE1RF1RD---1RE","1RE1LE1RF---1RD","1RE1RD0RF---0RA","1RE1RD0RF---1LA","1RE1RD1RF---0LD","1RE1RD1RF---1RD"};
      for(int v=0;v<18;v++)if(raw=="1RB1LC1RC0LD1LA0RB0RB"+ps[v]){
        nodes[i].a={21,999000+v,0,0,0,0,0};return i;
      }
    }
    if(oneLC){
      static const array<string,18> ps={"0LE0RF---1RE1RB","0RE0RF---0RD1RF","0RE0RF---0RD1RA","0RE1RD0RF---1LE","0RE1RD0RF---1RE","0RE1RD0RF---1LC","0RE1RD0RF---1RA","0RE1RD1RF---0RE","1LE1RD0RF---1RE","1LE1RD1RF---0RE","1RE0RF1LB---1RD","1RE0RF------1RB","1RE1RF0RA---0LE","1RE0RD0RF---1LE","1RE0RD0RF---1RE","1RE0RD0RF---1RB","1RE0RD1RF---1LB","1RE1LD0RF---1RB"};
      for(int v=0;v<18;v++)if(raw=="1RB1LC1RC0LD1LA0RB1LC"+ps[v]){
        nodes[i].a={22,1003000+v,0,0,0,0,0};return i;
      }
    }
    if(oneLA){
      static const array<string,10> ps={"0RE1RD1RF---1RB","1RE1RF1RA0LE---","1RE1RF1RA1RE---","1RE1RF1RB1LD---","1RE1RF---1RD1RE","1RE1RF---1RD0RD","1RE1RF---1RD0RC","1RE1RF---1RB---","1RE1RE1RF1RB---","1RE1LD1RF1RB---"};
      for(int v=0;v<10;v++)if(raw=="1RB1LC1RC0LD1LA0RB1LA"+ps[v]){
        nodes[i].a={19,179+v,0,0,0,0,0};return i;
      }
    }
    if(oneRA){
      static const array<string,8> ps={"1LE---1LF0LA0LD","1LE---1LF0LA0RA","1LE---1LF0LA1LA","1LE1LF0RE1RC---","1LE0LF1LB1RD---","1LE1LF1LB0RE---","1LE1LF1LB1RC---","1LE1LF1LB0LA---"};
      for(int v=0;v<8;v++)if(raw=="1RB1LC1RC0LD1LA0RB1RA"+ps[v]){
        nodes[i].a={20,300+v,0,0,0,0,0};return i;
      }
    }
    if(zeroRA){
      static const array<string,9> ps={
        "1LE0RF---1LB0RF","1LE0RF---0RB1RF","1LE1LF---0RF0LA",
        "1LE0RE0RF1LB---","1LE0RE1RF0RB---","1RE1LF---0RC0LE",
        "1RE1LF---1RC0LE","1RE1LE0LF0RB---","1RE1LE0LF1LB---"};
      for(int v=0;v<9;v++)if(raw=="1RB1LC1RC0LD1LA0RB0RA"+ps[v]){
        nodes[i].a={18,74+v,0,0,0,0,0};return i;
      }
    }
    if(oneRD){
      static const array<string,15> ps={
        "1RB1LC1RC0LD1LA0RB1RD0RE1RC0RF---1LD",
        "1RB1LC1RC0LD1LA0RB1RD0RE1RC1RF---0RE",
        "1RB1LC1RC0LD1LA0RB1RD1LE0LD0LF---0LE",
        "1RB1LC1RC0LD1LA0RB1RD1LE1LD0RF---1RE",
        "1RB1LC1RC0LD1LA0RB1RD1LE1RC1RF---0RE",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LF---0LD0LF",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LF---0RD0LF",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LF---1RD0LF",
        "1RB1LC1RC0LD1LA0RB1RD1RE0RB0RF---1RE",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LB0RF---1LD",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LB0RF---0LB",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LB0RF---0LA",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LB1RF---1RE",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LB1RF---1RC",
        "1RB1LC1RC0LD1LA0RB1RD1RE1LB1RF---1LA"};
      for(int v=0;v<15;v++)if(raw==ps[v]){nodes[i].a={17,v,0,0,0,0,0};return i;}
    }
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
    for(int k=1;k<=((zeroRE||zeroRC||zeroRD||zeroLC||zeroLB||oneRD||zeroRA||oneLA||oneRA||zeroRB||oneLC||oneRE)?7:extended?6:shared?7:(raw=="1RB1LC1RC0LD1LA0RB1LB1LE1RF1RC---1RE"?5:4));k++){NGram ng(raw,k);if(ng.check()){nodes[i].a={5,k,0,0,0,0,0};nodes[i].p=raw;return i;}}
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
 if(a.typ==23){cout<<"[\"oneREHard\","<<a.n<<']';return;}
 if(a.typ==21){cout<<"[\"zeroRBHard\","<<a.n<<']';return;}
 if(a.typ==22){cout<<"[\"oneLCHard\","<<a.n<<']';return;}
 if(a.typ==19){cout<<"[\"oneLAHard\","<<a.n<<']';return;}
 if(a.typ==20){cout<<"[\"oneRAHard\","<<a.n<<']';return;}
 if(a.typ==18){cout<<"[\"zeroRAHard\","<<a.n<<']';return;}
 if(a.typ==17){cout<<"[\"auto1RD\","<<a.n<<']';return;}
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
int main(){string s;int cut,holes;while(cin>>s>>cut>>holes){zeroRE=s=="1RB1LC1RC0LD1LA0RB1LB0RE------------";zeroRC=s=="1RB1LC1RC0LD1LA0RB0RC---------------";zeroRD=s=="1RB1LC1RC0LD1LA0RB0RD---------------";zeroLC=s=="1RB1LC1RC0LD1LA0RB0LC---------------";zeroLB=s=="1RB1LC1RC0LD1LA0RB0LB---------------";oneRD=s=="1RB1LC1RC0LD1LA0RB1RD---------------";zeroRA=s=="1RB1LC1RC0LD1LA0RB0RA---------------";oneLA=s=="1RB1LC1RC0LD1LA0RB1LA---------------";oneRA=s=="1RB1LC1RC0LD1LA0RB1RA---------------";zeroRB=s=="1RB1LC1RC0LD1LA0RB0RB---------------";oneLC=s=="1RB1LC1RC0LD1LA0RB1LC---------------";oneRE=s=="1RB1LC1RC0LD1LA0RB1RE---------------";extended=oneRE||zeroRB||oneLC||oneLA||oneRA||zeroRA||oneRD||zeroRE||zeroRC||zeroRD||zeroLC||zeroLB||s=="1RB1LC1RC0LD1LA0RB1LB0LE------------"||s=="1RB1LC1RC0LD1LA0RB1LB1RE------------";nodes.clear();int i=complete(parse(s),cut,holes);if(i<0){cerr<<"unresolved "<<s<<'\n';return 1;}cout<<s<<' ';emit(i);cout<<'\n';}}
