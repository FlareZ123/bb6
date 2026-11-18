#include <bits/stdc++.h>
using namespace std;
using Word = vector<pair<int,int>>;

int mod3(int x) { int r=x%3; return r<0 ? r+3 : r; }
int floor3(int x) { int q=x/3, r=x%3; if(r<0) --q; return q; }

bool synchronizes(const Word& w, char branch) {
  const int amin = branch=='L' ? -2 : -4;
  const int amax = branch=='L' ?  2 :  1;
  bool haveReference=false;
  array<int,4> reference{};
  for(int xp0=0;xp0<3;xp0++)
    for(int yp0=0;yp0<3;yp0++)
      for(int a0=amin;a0<=amax;a0++)
        for(int b0=-2;b0<=2;b0++) {
          int xp=xp0, yp=yp0, a=a0, b=b0;
          bool seenNonzero=false, seenNotTwo=false;
          for(auto [x,y] : w) {
            int tx,ty;
            if(branch=='L') { tx=x-yp+a; ty=yp+b; }
            else { tx=-x-xp-yp+a; ty=xp+yp+b; }
            int ox=mod3(tx), oy=mod3(ty);
            a=floor3(tx); b=floor3(ty);
            seenNonzero |= ox!=0;
            seenNotTwo |= ox!=2;
            xp=x; yp=y;
            if(a<amin || a>amax || b< -2 || b>2) return false;
          }
          if(!seenNonzero || !seenNotTwo) return false;
          array<int,4> finalState={xp,yp,a,b};
          if(!haveReference) { reference=finalState; haveReference=true; }
          else if(finalState!=reference) return false;
        }
  return true;
}

int main() {
  string line;
  map<int,int> minLengthDistribution, earliestEndDistribution;
  map<int,vector<int>> lengthExamples, endExamples;
  int total=0;
  while(getline(cin,line)) {
    istringstream in(line);
    int index,length;
    if(!(in>>index>>length)) continue;
    Word w;
    string pairDigits;
    for(int i=0;i<length;i++) {
      in>>pairDigits;
      w.push_back({pairDigits[0]-'0',pairDigits[1]-'0'});
    }
    int bestLength=99, earliestEnd=999;
    for(int subLength=3;subLength<=6;subLength++) {
      for(int start=0;start+subLength<=(int)w.size();start++) {
        Word sub(w.begin()+start,w.begin()+start+subLength);
        if(synchronizes(sub,'L') && synchronizes(sub,'R')) {
          bestLength=min(bestLength,subLength);
          earliestEnd=min(earliestEnd,start+subLength);
        }
      }
    }
    minLengthDistribution[bestLength]++;
    earliestEndDistribution[earliestEnd]++;
    if(lengthExamples[bestLength].size()<10) lengthExamples[bestLength].push_back(index);
    if(endExamples[earliestEnd].size()<10) endExamples[earliestEnd].push_back(index);
    total++;
  }
  cout << "blocks " << total << "\n";
  for(auto [length,count] : minLengthDistribution) {
    cout << "minimum_reset_subword_length " << length << " count " << count << " examples";
    for(int n:lengthExamples[length]) cout << " " << n;
    cout << "\n";
  }
  for(auto [end,count] : earliestEndDistribution) {
    cout << "earliest_reset_end_exclusive " << end << " count " << count << " examples";
    for(int n:endExamples[end]) cout << " " << n;
    cout << "\n";
  }
  return 0;
}
