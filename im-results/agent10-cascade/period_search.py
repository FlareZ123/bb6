from math import lcm
from collections import Counter
from fractions import Fraction as F

def params(word):
    A=B=D=0; S=C=E=0
    for v,d in word:
        p=3**(v-1)
        S=p*(S+(16<< (A+D)))
        C=p*(C+(2<<A))
        E=p*(E+((2*D+5)<<A))
        A+=v; B+=v-1;D+=d
    P=2**A; R=3**B
    if D==0 or P*2**D<=R:return None
    a=F(S,P*2**D-R); b=F(C,P-R); c=(F(E)-P*b*D)/(P-R)
    return a,b,c

def level(h):
    k=max(0,(h+5).bit_length()-3)
    while h+k+5>=8<<k:k+=1
    return k

def generate(n):
    h=2;k=level(h); states=[];word=[]
    for _ in range(n):
        states.append((h,k))
        if h+k+4==4<<k:print('HALT',_,k);break
        x=2*h+5;z=x+(16<<k)+2*k+5;v=(z&-z).bit_length()-1
        h2=(3**(v-1)*(z>>v)-5)//2
        k2=level(h2);word.append((v,k2-k));h,k=h2,k2
    return states,word

def search(n=50000, maxperiod=32):
    states,word=generate(n);cache={};cnt=Counter(); tested=Counter();out=[]
    for i in range(len(word)):
        h,k=states[i]
        for L in range(1,min(maxperiod,(len(word)-i)//2)+1):
            if word[i]!=word[i+L] or word[i:i+L]!=word[i+L:i+2*L]:continue
            w=tuple(word[i:i+L]);cnt[L]+=1
            if w in cache:p=cache[w]
            else:
                p=params(w);cache[w]=p
            if p is None:continue
            a,b,c=p
            if not 8<=a<=16:continue
            if a.denominator>1 and lcm(b.denominator,c.denominator)%a.denominator:continue
            D=sum(d for v,d in w)
            if (2**D-1)**2%a.denominator:continue
            tested[L]+=1
            if a*(1<<k)+b*k+c==2*h+5:
                out.append((i,k,w,p));print('MATCH',i,k,w,p,flush=True)
    print('states',len(states),'last level',states[-1][1],'two-repeat candidates',sum(cnt.values()),'after arithmetic filters',sum(tested.values()),'unique words',len(cache),'matches',len(out));print('raw per period',cnt);print('tested',tested)
if __name__=='__main__':search()
