#include <bits/stdc++.h>
using namespace std; using Word=vector<pair<int,int>>;
int mod3(int x){int r=x%3;return r<0?r+3:r;}
int floor3(int x){int q=x/3,r=x%3;if(r<0)--q;return q;}
bool synchronizes(const Word&w,char branch){
  // By one_extra_digit_carry_bound, actual starts at k+1 have a,b in [-1,1].
  // The larger branch-specific ranges are invariant under subsequent steps.
  const int startAmin=-1,startAmax=1,startBmin=-1,startBmax=1;
  const int invAmin=branch=='L'?-2:-4,invAmax=branch=='L'?2:1;
  bool have=false;array<int,4>ref{};
  for(int xp0=0;xp0<3;xp0++)for(int yp0=0;yp0<3;yp0++)
    for(int a0=startAmin;a0<=startAmax;a0++)for(int b0=startBmin;b0<=startBmax;b0++){
      int xp=xp0,yp=yp0,a=a0,b=b0;bool nz=false,nt2=false;
      for(auto [x,y]:w){int tx,ty;if(branch=='L'){tx=x-yp+a;ty=yp+b;}else{tx=-x-xp-yp+a;ty=xp+yp+b;}
        int ox=mod3(tx),oy=mod3(ty);a=floor3(tx);b=floor3(ty);nz|=ox!=0;nt2|=ox!=2;xp=x;yp=y;
        if(a<invAmin||a>invAmax||b< -2||b>2)return false;
      }
      if(!nz||!nt2)return false;array<int,4>end={xp,yp,a,b};if(!have){ref=end;have=true;}else if(end!=ref)return false;
    }
  return true;
}
int main(){string line;map<int,int>lengthDist,endDist;map<int,vector<int>>lenExamples,endExamples;int total=0;
 while(getline(cin,line)){istringstream in(line);int n,L;in>>n>>L;Word w;string s;for(int i=0;i<L;i++){in>>s;w.push_back({s[0]-'0',s[1]-'0'});}int best=99,earliest=999;
  for(int len=3;len<=6;len++)for(int i=0;i+len<=(int)w.size();i++){Word sub(w.begin()+i,w.begin()+i+len);if(synchronizes(sub,'L')&&synchronizes(sub,'R')){best=min(best,len);earliest=min(earliest,i+len);}}
  lengthDist[best]++;endDist[earliest]++;if(lenExamples[best].size()<10)lenExamples[best].push_back(n);if(endExamples[earliest].size()<10)endExamples[earliest].push_back(n);total++;
 }
 cout<<"blocks "<<total<<"\n";for(auto [k,v]:lengthDist){cout<<"minimum_reset_subword_length "<<k<<" count "<<v<<" examples";for(int n:lenExamples[k])cout<<" "<<n;cout<<"\n";}for(auto [k,v]:endDist){cout<<"earliest_reset_end_exclusive "<<k<<" count "<<v<<" examples";for(int n:endExamples[k])cout<<" "<<n;cout<<"\n";}
}
