"""Independent exact-integer P1 inverse enumerator for a fixed n.

Uses the original explicit k,c power/mass equations rather than the
C++ scanner's algebraically simplified child-b formula. Stores active
states only to independently validate the streaming unique-parent count.
"""
import sys

def search(n):
    root=(14*(1<<n)-2*n-16,3)
    stack=[root]
    visited={root}
    edges=0
    while stack:
        b,d=stack.pop()
        assert b>=8 and b%4==0 and d%2==1
        A=d+b//2+3
        exponent=(A & -A).bit_length()-1
        for t in range(exponent):
            c=(A//(1<<t))-3
            if c<1 or c%2!=1:
                continue
            numerator=b+d-c-2*t-2
            if numerator<4 or numerator%2!=0:
                continue
            k=numerator//2
            child=(2*k-4,c+4)
            edges+=1
            if child[1]==5:
                return {"n":n,"status":"HIT","child":child,"parent":(b,d),"t":t}
            if child[0]>=8 and child[0]%4==0 and child not in visited:
                visited.add(child)
                stack.append(child)
    return {"n":n,"status":"COMPLETE","active":len(visited),"edges":edges}

if __name__ == "__main__":
    print(search(int(sys.argv[1])))
