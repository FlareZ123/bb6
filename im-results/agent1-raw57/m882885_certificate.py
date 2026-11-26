"""Exact finite certificate for the M882/M885 shared epoch map.
The closure check exhausts a finite product, not a bounded orbit.
Run with Python 3; no dependencies.
"""
D=[(1,2),(2,3),(2,2),(4,2),(5,6),(2,7),(8,2),(9,2),(2,10),(11,2),(12,2),(13,2),(14,2),(15,16),(17,2),(18,2),(19,2),(20,2),(2,21),(22,23),(24,2),(25,2),(2,26),(27,2),(2,28),(2,29),(30,2),(2,31),(32,2),(33,2),(34,2),(35,2),(2,36),(2,24),(37,2),(2,38),(39,2),(40,41),(42,2),(2,43),(44,2),(45,2),(2,46),(2,2),(47,2),(48,49),(50,2),(51,2),(2,52),(53,2),(2,54),(55,2),(56,2),(2,57),(58,28),(59,2),(60,2),(61,2),(62,63),(58,2),(64,2),(47,38),(65,66),(28,2),(67,41),(68,2),(69,2),(70,2),(71,2),(2,72),(47,73),(74,2),(75,2),(76,2),(77,2),(2,78),(2,79),(80,2),(81,2),(82,2),(2,83),(84,2),(2,85),(86,2),(87,2),(58,2),(88,36),(2,89),(2,90),(91,2),(92,2),(93,36),(94,2),(2,95),(96,2),(97,2),(20,98),(99,2),(100,2),(101,2),(48,23),(102,41),(103,2),(2,73)]
ACCEPT={43,54,78,85}
SEED="0101010000010101"
T={
"C":{"0":("C0",""),"1":("BAD","")},
"C0":{"0":("Copy","10101"),"1":("C01","")},
"C01":{"0":("A","10010"),"1":("BAD","")},
"A":{"0":("A0",""),"1":("A1","")},
"A0":{"0":("C",""),"1":("A","00")},
"A1":{"0":("A","00"),"1":("Copy","010")},
"Copy":{"0":("Copy","0"),"1":("Copy","1")},
"BAD":{"0":("BAD",""),"1":("BAD","")},
}
F={}
for q in T:
    s=q; out=""
    while s not in ("Copy","BAD"):
        s,v=T[s]["0"]; out+=v
    F[q]=out if s=="Copy" else None

def walk(q,w):
    for a in w: q=D[q][int(a)]
    return q

def closure():
    assert len(D)==104 and all(0<=j<len(D) for row in D for j in row)
    assert walk(0,SEED) in ACCEPT
    todo=[(0,"C",walk(0,"0"))]; seen=set(todo); n_accept=0
    for i,q,j in todo:
        if i in ACCEPT:
            n_accept+=1
            assert q!="BAD" and walk(j,F[q]) in ACCEPT,(i,q,j)
        for a in "01":
            s,v=T[q][a]
            x=(D[i][int(a)],s,walk(j,v) if s!="BAD" else 0)
            if x not in seen: seen.add(x);todo.append(x)
    assert (len(seen),n_accept)==(382,10)
    print("104 DFA states; 382 reachable product states; 10 accepting product states; closure PASSED")

def table(b):
    return [a for row in ["1RB1LF","1RC"+b,"0RD---","1LD1RE","0RA0LA","1RD0LF"] for a in (row[:3],row[3:])]

def step(t,q,l,r):
    a=t[2*(ord(q)-65)+int(r[0] if r else "0")]
    assert a!="---"
    w,d,s=a
    if d=="R": return s,w+l,r[1:]
    return s,l[1:],(l[0] if l else "0")+w+r[1:]

def run(t,z,n):
    for _ in range(n): z=step(t,*z)
    return z

def macros(b,entry,setup,mix):
    t=table(b)
    assert run(t,("A","",""),entry)==("C","11011","0000"+SEED)
    # X/Y are unread arbitrary-tail markers; reading either raises.
    def check(q,l,r,n,s,L,R):
        assert run(t,(q,l,r),n)==(s,L,R),(b,q,l,r,n)
    check("C","11011","0000Y",setup,"C","110"+"1"*8,"Y")
    check("C","110X","00Y",11,"A","X","10101Y")
    check("C","110X","010Y",3,"A","010110X","Y")
    check("A","01X","10Y",4,"A","0111X","Y")
    check("A","01X","01Y",mix,"A","0111X","Y")
    check("A","01X","00Y",2,"C","1101X","Y")
    check("A","01X","11Y",4,"A","11X","10Y")
    # General drain follows by repeated F1 shifts and final four moves.
    check("A","1X","1Y",1,"F","X","11Y")
    check("F","1X","1Y",1,"F","X","10Y")
    check("F","0X","1Y",1,"F","X","00Y")
    check("F","X","00Y",4,"A","X","10Y")
    check("A","1"*8,"1Y",13,"A","","1"+"0"*8+"1Y")
    check("A","","1"+"0"*8+"1Y",4,"A","011","0"*7+"1Y")
    check("A","011","0"*7+"1Y",2,"C","11011","0"*5+"1Y")
    print("M"+("882" if b=="0LA" else "885")+": entry and all symbolic macros PASSED")

if __name__=="__main__":
    closure()
    macros("0LA",223,42,6)
    macros("1LD",241,48,8)
