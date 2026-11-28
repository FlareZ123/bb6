#include <bits/stdc++.h>
using namespace std;
struct Snap{int q,h; bitset<512> ones;};
struct Res{int kind; int slot,t; vector<Snap> hist;}; // 0 unknown,1 halt,2 long
Res trace(const array<int,12>& p,int cap=100){int q=0,h=0;bitset<512> ones;vector<Snap> hist;hist.reserve(cap+1);for(int t=0;t<=cap;t++){hist.push_back({q,h,ones});int idx=h+256;bool bit=idx>=0&&idx<512&&ones[idx];int slot=2*q+(bit?1:0),a=p[slot];if(a==0||a==1)return {a==0?0:1,slot,t,move(hist)};int v=a-2;if(idx>=0&&idx<512){if(v>=12)ones.set(idx);else ones.reset(idx);}q=v%6;h+=(v%12>=6?1:-1);if(h<-250||h>250){cerr<<"range";exit(2);}}return {2,-1,cap+1,move(hist)};}
bitset<512> rightMask[512], leftMask[512];
void initMasks(){for(int b=0;b<512;b++){for(int i=0;i<512;i++){if(i>=b)rightMask[b].set(i);if(i<=b)leftMask[b].set(i);}}}
bool side(const vector<Snap>& hist,int maxEntry=60,int maxPeriod=30){int maxe=min<int>(hist.size(),maxEntry);for(int e=0;e<maxe;e++){int rmin=INT_MAX,lmax=INT_MIN;for(int j=e+1;j<min<int>(hist.size(),e+maxPeriod+1);j++){int hp=hist[j-1].h;rmin=min(rmin,hp);lmax=max(lmax,hp);auto&a=hist[e];auto&b=hist[j];int delta=b.h-a.h;if(a.q!=b.q)continue;for(int rr=0;rr<2;rr++){bool right=rr==0;if(right?delta<0:delta>0)continue;int boundary=right?rmin:lmax;int bi=boundary+256;if(bi<0||bi>=512)continue;bitset<512> shifted=delta>=0?(b.ones>>delta):(b.ones<<(-delta));const auto&mask=right?rightMask[bi]:leftMask[bi];if((((a.ones^shifted)&mask).none()))return true;}}}return false;}
int main(int argc,char**argv){initMasks();if(argc!=2){cerr<<"usage: raw34_pair_depth8_census residualRows.json\n";return 2;}ifstream in(argv[1]);if(!in){cerr<<"cannot open residual rows\n";return 2;}vector<int>nums;char ch;while(in.get(ch)){if(isdigit((unsigned char)ch)){int v=ch-'0';while(in.peek()!=EOF&&isdigit((unsigned char)in.peek())){char d=in.get();v=v*10+(d-'0');}nums.push_back(v);}}if(nums.size()%12){cerr<<"bad nums "<<nums.size();return 2;}vector<array<int,12>>rows(nums.size()/12);for(size_t i=0;i<rows.size();i++)for(int j=0;j<12;j++)rows[i][j]=nums[12*i+j];long long p6=0,c7=0,h7=0,u7=0,l7=0,c8=0,h8=0,l8=0;vector<array<int,12>>open7;for(auto p:rows){auto r0=trace(p);if(r0.kind!=0)continue;p6++;int s=r0.slot;for(int c=1;c<=25;c++){p[s]=c;auto r=trace(p);if(side(r.hist))c7++;else if(r.kind==1)h7++;else if(r.kind==0){u7++;open7.push_back(p);}else l7++;}}
for(auto p:open7){auto r0=trace(p);if(r0.kind!=0){cerr<<"open7 invariant\n";return 3;}int s=r0.slot;for(int c=1;c<=25;c++){p[s]=c;auto r=trace(p);if(side(r.hist))c8++;else if(r.kind==1)h8++;else l8++;}}
if(rows.size()!=12356||p6!=11571||c7!=198646||h7!=11571||u7!=62061||l7!=16997||c8!=1233087||h8!=62061||l8!=256377){cerr<<"census mismatch\n";return 4;}
const long long residual6=11571LL*625+732LL*625+52LL*15625+390625;
const long long newly7=(c7+h7)*25,newly8=c8+h8,remaining=residual6-newly7-newly8;
if(residual6!=8892500||newly7!=5255425||newly8!=1295148||remaining!=2341927){cerr<<"mass mismatch\n";return 5;}
cout<<"{\n"
    <<"  \"depth6ResidualRows\": "<<rows.size()<<",\n"
    <<"  \"openDepth6Rows\": "<<p6<<",\n"
    <<"  \"depth7\": {\"sidecycles\": "<<c7<<", \"halts\": "<<h7<<", \"open\": "<<u7<<", \"long\": "<<l7<<"},\n"
    <<"  \"depth8FromOpen7\": {\"sidecycles\": "<<c8<<", \"halts\": "<<h8<<", \"long\": "<<l8<<"},\n"
    <<"  \"depth6ResidualPhysical\": "<<residual6<<",\n"
    <<"  \"newlyClassifiedPhysical\": "<<(newly7+newly8)<<",\n"
    <<"  \"remainingPhysical\": "<<remaining<<"\n"
    <<"}\n";
}
