"""Replay finite witness prefixes, independently of Lean."""
TABLES = {
    3864: (7,10,11,22,14,17,24,16,20,11,3,0),
    4344: (7,12,11,24,14,21,23,16,20,11,3,13),
    11287: (7,8,11,3,14,21,24,16,20,11,19,2),
    10338: (7,21,11,1,14,24,3,16,20,11,15,20),
}
def step(t,q,h,o):
    v=t[2*q+(h in o)]
    assert v!=24, (q,h)
    if v&2:o.add(h)
    else:o.discard(h)
    return v>>2,h+(1 if v&1 else -1)
def check_side(i,entry,period,right,boundary):
    q=h=0;o=set()
    for _ in range(entry):q,h=step(TABLES[i],q,h,o)
    q0,h0,o0=q,h,o.copy()
    keep=lambda x: x>=boundary if right else x<=boundary
    for _ in range(period):
        assert keep(h)
        q,h=step(TABLES[i],q,h,o)
    d=h-h0
    assert q==q0 and (d>=0 if right else d<=0)
    assert {x for x in o0 if keep(x)}=={x-d for x in o if keep(x-d)}
    print(i,entry,period,d,boundary)
if __name__=='__main__':
    check_side(3864,1443,672,False,-2)
    check_side(4344,5234,1112,False,-8)
    check_side(11287,2656,948,True,-7)
    q=h=0;o=set()
    for _ in range(6120):q,h=step(TABLES[10338],q,h,o)
    assert (q,h,o)==(5,-98,set(range(-95,28)))
    print(10338,6120,q,h,len(o))
