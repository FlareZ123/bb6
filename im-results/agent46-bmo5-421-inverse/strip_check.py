from collections import Counter
import subprocess
from symbolic import depth

def strip_depth(w,n):
    j=(w*3**n-3)//2-n
    if n<6:
        d,root=depth(j+n)
        assert root>3
        return max(0,d-n)
    a,D,c,k,s=8,3,-w-6,j,1
    while s<255:
        p=5*pow(2,k,3*D)%(3*D)
        r=(a*p+c)%(3*D)
        assert r%D==0
        u=r//D
        if u==0:a*=2;k-=1
        elif u==p%3:a+=8*D;c-=6*D
        else:return s
        D*=3;s+=1
    raise AssertionError('unresolved')

for w in (5,7):
    for n in range(6,13):
        j=(w*3**n-3)//2-n
        d,root=depth(j+n)
        assert root>3 and d-n==strip_depth(w,n),(w,n,d,strip_depth(w,n))
    N=10000
    expected=Counter(strip_depth(w,n) for n in range(N+1))
    result=subprocess.check_output(['./strip_sieve',str(w),str(N)],text=True).splitlines()
    got=dict(tuple(map(int,line.split())) for line in result[:-1])
    assert got==expected,(w,got,expected)
    print('matched',w,'literal n=6..12 and singleton modular histogram n=0..10000')
