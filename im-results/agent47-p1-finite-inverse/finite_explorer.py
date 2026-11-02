"""Explore finite P1 ancestor cones; numerical samples do not prove residue classes."""
from collections import Counter

def is_fourteen_power(value):
    q, r = divmod(value, 14)
    return r == 0 and q > 0 and (q & (q-1)) == 0

def check_index(n, limit=50000):
    root=14*pow(2,n)-2*n-16
    todo=[(root,3)]
    seen=set()
    fail=[]
    branches=0
    while todo and len(seen)<limit:
        b,d=todo.pop()
        if (b,d) in seen:
            fail.append(("repeated",b,d))
            break
        seen.add((b,d))
        if b<8 or b%4 or d<1:
            fail.append(("bad_hub",b,d))
            continue
        k=b//4-1
        c=d+b//2
        while c>=2:
            branches+=1
            x=2*k-4
            y=c+4
            if x<4:
                fail.append(("range",x,y))
                break
            if y%2==0:
                if is_fourteen_power(x+12):
                    fail.append(("power",x,y))
            elif x%4==2 and x>2:
                pass
            elif x%4==0 and x>=8:
                todo.append((x,y))
            else:
                fail.append(("unknown",x,y))
            if c%2==0:
                break
            c=(c-3)//2
            k=k+c//2+1
    if todo:
        fail.append(("limit",len(todo)))
    return not fail,len(seen),branches,fail

if __name__=="__main__":
    for residue in (2,50):
        data=[check_index(n) for n in range(residue,10000,64) if n>=14]
        print(residue,len(data),sum(int(x[0]) for x in data),
              Counter(x[1] for x in data),Counter(x[2] for x in data))
