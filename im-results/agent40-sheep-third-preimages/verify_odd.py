"""Exact finite checks for seven more Sheep third-generation target classes."""
R=(11,31,71,91,131,191,211)

def F(t: int) -> int | None:
    a=(t & -t).bit_length()-1
    u=t >> a
    if u==1: return None
    if u==3: return t+a+3
    return t+a+(u-1)//2

def inverse(y: int) -> tuple[int,...]:
    parents=set()
    for a in range(y.bit_length()+1):
        special=3<<a
        if F(special)==y: parents.add(special)
        numerator=2*y-2*a+1
        mod=(1<<(a+1))+1
        u,r=divmod(numerator,mod)
        if r==0 and u>=5 and (u&1):
            t=u<<a
            assert F(t)==y
            parents.add(t)
    return tuple(sorted(parents))

def main() -> None:
    count=0
    for j in range(11,1501):
        if j%300 not in R: continue
        p=2*((1<<(j+1))-1)//5
        x=((1<<(j+4))-18)//25
        assert inverse(1<<j)==(p,),j
        assert inverse(p)==(x,),j
        assert inverse(x)==(),j
        count+=1
    print("PASS",count,"exact three-level inverse trees up to j=1500")
    for q in range(100):
        for r in R:
            j=r+300*q
            assert pow(2,j+5,125)!=61
            assert pow(2,j+5,1625)!=261
    print("PASS 700 uniform-modulus instances")

if __name__=="__main__":
    main()
