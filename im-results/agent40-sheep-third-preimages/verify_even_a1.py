"""Independent finite verification of sixteen Sheep depth-three inverse barriers."""

R=(2,22,26,38,58,62,70,98,106,110,130,142,146,166,170,178)

def F(t: int) -> int | None:
    assert t>=3
    a=(t&-t).bit_length()-1
    u=t>>a
    if u==1: return None
    if u==3: return t+a+3
    return t+a+(u-1)//2

def inv(y: int) -> tuple[int, ...]:
    result=set()
    for a in range(y.bit_length()+1):
        special=3<<a
        if F(special)==y: result.add(special)
        n=2*y-2*a+1
        d=(1<<(a+1))+1
        u,r=divmod(n,d)
        if not r and u>=5 and u&1:
            x=u<<a
            assert F(x)==y
            result.add(x)
    return tuple(sorted(result))

def main() -> None:
    count=0
    for j in range(22,2001):
        if j%180 not in R: continue
        p=((1<<(j+1))+1)//3
        x=((1<<(j+3))-2)//15
        assert inv(1<<j)==(p,),j
        assert inv(p)==(x,),j
        assert inv(x)==(),j
        count+=1
    print('PASS',count,'complete three-level inverse trees for j<=2000')
    for q in range(250):
        for r in R:
            j=r+180*q
            assert pow(2,j+4,9)!=7
            assert pow(2,j+4,25)!=19
            assert pow(2,j+4,27)!=22
            assert pow(2,j+4,13)!=9
            assert pow(2,j+2,27)!=7
            assert pow(2,j+2,9)!=4
    print('PASS 4000 modular gate instances')

if __name__=='__main__':
    main()
