"""Independent finite test of the exact B1 main-section return rule."""
M = '1RB1RD1RC1RE0LA0RC1LA1LD---1LF1LC0LE'
BLOCK = {'00':'00000','01':'00110','10':'11000','11':'11110'}

def prefix(q, p):
    if q == 0:
        return ('','110','100')[p]
    bits = bin(q)[2:]
    return '110'+''.join(BLOCK[a+b] for a,b in zip(bits,bits[1:])) + (BLOCK[bits[-1]+str(p)] if p < 2 else {'0':'00100','1':'11100'}[bits[-1]])

def step_return(P, n):
    word = P + '1'*(2*n+5)
    head = len(P)+2*n+1
    tape = {i-head for i,b in enumerate(word) if b=='1'}
    h=0; q=1; t=0; carries=[]
    while True:
        m=M[6*q+3*(h in tape):6*q+3*(h in tape)+3]
        assert m!='---', (P,n,t)
        if m[0]=='1':tape.add(h)
        else:tape.discard(h)
        h += 1 if m[1]=='R' else -1
        q=ord(m[2])-65;t+=1
        assert t<100000
        if q==1 and h in tape:
            if max(tape)==h+3 and all(h+i in tape for i in range(1,4)):
                z=h-1
                while z in tape:z-=1
                P2=''.join('1' if x in tape else '0' for x in range(min(tape),z+1))
                return P2,h-z-1,t,carries
            z=h-1
            while z in tape:z-=1
            carries.append((h-z-1,''.join('1' if x in tape else '0' for x in range(h+1,max(tape)+1))))

def main():
    count=0; max_steps=0
    for q in range(512):
        for p in range(3):
            for n in (0,1,2,5,13,37):
                P=prefix(q,p); P2,run,t,carry=step_return(P,n)
                q2,p2=(q,p+1) if p<2 else (q+1,0)
                assert P2==prefix(q2,p2) and run==2*n+3,(q,p,n,P,P2,prefix(q2,p2),run)
                assert len(carry)==(p==2), (q,p,n,carry)
                if carry: assert carry[0][0]==1
                count+=1;max_steps=max(max_steps,t)
    print(f'{count} independently replayed arbitrary (q,p,n) return instances; max {max_steps} primitive transitions')
if __name__=='__main__':main()
