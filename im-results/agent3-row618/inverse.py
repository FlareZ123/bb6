"""Exact inverse of the Row618 section recurrence; no bound on exponent."""
def direct(m, under=False):
    t=max(0,(m-1).bit_length()-3)
    P=1<<t
    k=2*m-12*P-(0 if under else 1)
    if 2<=k<4*P and (k%2==0)==under:
        n=4*P+k-t-2
        if n>=5: return n,t

def parents(n):
    h=direct(n)
    if h: yield h[0]
    if n%3!=2: return
    a=(2*n-1)//3
    while True:
        h=direct(a,True)
        if h: yield h[0]
        if a%3: return
        a=a//3*2

def reaches(j):
    todo=[(4<<j)-j-1]; seen=set()
    while todo:
        n=todo.pop()
        if n==5: return True
        if n<5 or n in seen: continue
        seen.add(n)
        todo.extend(parents(n))
    return False

if __name__=='__main__':
    import sys
    for j in range(int(sys.argv[1])):
        if reaches(j): print('reachable terminal',j)
    print('finite scan finished')
