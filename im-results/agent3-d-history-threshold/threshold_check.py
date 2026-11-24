"""Finite certificates for unbounded E-guard suffix threshold (literal D table)."""
RULES=((1,1,1),(0,1,4),(1,-1,2),(0,1,0),(1,-1,0),(1,-1,3),
       (1,-1,2),(1,-1,5),(0,-1,2),(0,-1,1),(1,-1,4),None)
def hist(s):
    return tuple('ABCDEFG'.index(c) for c in s.replace(' ',''))
X=hist('EC AF AC BA EB'); T=hist('AC BA EB'); U=hist('BA EB AC')
Z=hist('EC AG'); AD=hist('AD'); BC=hist('BC')
P='0101101011'; M='01100'; J='111111'

def block(w,left,right):
    """Exact local steps with right-boundary replies; G is propagated halt."""
    a=list(map(int,w)); j=cost=0
    for i in range(0,len(left),2):
        q,r=left[i:i+2]; p=0
        while True:
            if p<0:
                assert q==r; break
            if p==len(a):
                assert j<len(right) and q==right[j]
                q=right[j+1]; j+=2
                if q==6:
                    assert r==6 and i+2==len(left); break
                p-=1; continue
            tr=RULES[2*q+a[p]]
            if tr is None:
                assert r==6 and i+2==len(left); break
            a[p],d,q=tr; cost+=1; p+=d
    assert j==len(right)
    return ''.join(map(str,a)),cost

def guard(left):
    a=list(map(int,'00101010')); h=low=j=cost=0; q=4
    while True:
        if h==0:
            assert j<len(left) and q==left[j]
            q=left[j+1]; j+=2
            if q==6:
                assert j==len(left); return 'halt',cost
            h=1; low=max(low,h)
        else:
            b=a[h-1]
            if h==low and h>=2 and h%2==0 and q in (1,3) and b==0:
                assert j==len(left); return 'return',h,q,''.join(map(str,a[:h-1][::-1])),cost
            tr=RULES[2*q+b]
            if tr is None:
                assert j==len(left); return 'halt',cost
            a[h-1],d,q=tr; cost+=1; h-=d; low=max(low,h)
            assert 0<=h<=len(a)

def main():
    cases=[(P,X,X+T,'0101010101',121),('0101010101',T,T,'0101010101',60),
           ('0101010101',AD,AD,'1111111111',20),
           (M,X,(),'01010',29),('01010',T,U,'01010',30),('01010',AD,BC,'11111',10),
           (J,U,(),'101010',21),('101010',U,U,'101010',36),('101010',BC,BC,'111111',12),
           (P,Z,Z,'1011010110',18),(P,Z,X+AD,'1111111111',79)]
    for w,l,r,out,c in cases: assert block(w,l,r)==(out,c)
    assert guard(X)==('return',8,1,'0111101',31)
    assert guard(Z)==('halt',3)
    assert block('0',BC,())==('1',1)
    print('14 fixed local certificates passed (11 block, 2 guard, 1 blank)')
if __name__=='__main__': main()
