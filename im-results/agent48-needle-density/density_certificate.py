from fractions import Fraction as F
from itertools import combinations
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import re

src=Path(__file__).with_name('NeedleOrderTable.lean').read_text()
rows=re.findall(r'theorem order(\d+) : Period \(2\^\(\d+\+1\)\+3\) (\d+).*?check_sound \(ps:=\[([\d, ]+)\]\)',src,flags=re.S)
assert len(rows)==51
classes=[]
mid=F(0)
for i,(v,r,fs) in enumerate(rows):
    v,r=int(v),int(r)
    assert v==i
    ps=list(map(int,fs.split(',')))
    D=2**(v+1)+3
    assert prod(ps)==r and all(p>=2 and all(p%d for d in range(2,isqrt(p)+1)) for p in set(ps))
    assert pow(2,r,D)==1 and all(pow(2,r//p,D)!=1 for p in set(ps))
    if v<=10:
        classes.extend((K,r) for K in range(r) if pow(2,K+1,D)==(2*v-3)%D)
    else:
        mid+=F(1,r)
assert classes==[(0,4),(9,10),(12,18),(22,66),(13,130),(98,204)]
low=F(0)
for i in range(1,len(classes)+1):
    for group in combinations(classes,i):
        if all((a-b)%gcd(r,s)==0 for (a,r),(b,s) in combinations(group,2)):
            low+=(-1)**(i+1)*F(1,lcm(*(r for _,r in group)))
tail=F(8,15)*sum(F(1,j) for j in (49,50,51))
upper=low+mid+tail
assert low==F(87067,218790) and tail==F(29996,937125)
assert upper<F(433335,1000000)
assert 1-upper>F(566665,1000000)
print('low',low,float(low),'mid',float(mid),'tail',tail,float(tail))
print('no-parent interval',float(1-upper),float(1-low))
