"""Finite exact inverse checks for five fourth-generation Sheep target families.

The all-exponent theorem and large-valuation bounds are separately proved.
"""
R=(72,144,360,504,576)

def F(t: int) -> int | None:
    a=(t & -t).bit_length()-1
    u=t>>a
    if u==1: return None
    if u==3: return t+a+3
    return t+a+(u-1)//2

def inverse(y: int) -> tuple[int,...]:
    out=set()
    for a in range(y.bit_length()+1):
        t=3<<a
        if F(t)==y: out.add(t)
        numerator=2*y-2*a+1
        m=(1<<(a+1))+1
        u,r=divmod(numerator,m)
        if r==0 and u>=5 and u&1:
            t=u<<a
            assert F(t)==y
            out.add(t)
    return tuple(sorted(out))

def main() -> None:
    count=0
    for j in range(72,3001):
        if j%648 not in R: continue
        p=((1<<(j+1))+1)//3
        x=((1<<(j+2))+5)//9
        y=((1<<(j+3))+19)//27
        assert inverse(1<<j)==(p,),j
        assert inverse(p)==(x,),j
        assert inverse(x)==(y,),j
        assert inverse(y)==(),j
        count+=1
    print('PASS',count,'fourth-generation inverse trees through exponent 3000')
    gates=[(81,4,16),(5,4,4),(243,4,43),(17,4,12),(13,4,10),
           (19,4,6),(5,3,4),(81,3,17),(17,3,1),(5,3,1),
           (5,2,1),(27,2,7),(17,2,13),(5,1,1)]
    for q in range(200):
        for r in R:
            j=r+648*q
            assert all(pow(2,j+k,m)!=target for m,k,target in gates)
    print('PASS 1000 full modular-gate instances')

if __name__=='__main__': main()
