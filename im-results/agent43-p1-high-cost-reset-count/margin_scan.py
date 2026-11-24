from time import monotonic

CASES=[(30,82),(286,1442),(350,586),(1614,5824),(2990,6154),(3342,13730)]
for n,K in CASES:
    Q=7*2**n-(n+3); cs={1}; lo=Q+1; arg=0; bad=[]; t=monotonic()
    for j in range(K):
        if cs:
            w=Q-j+2-max(cs)
            if w<lo: lo=w; arg=j
            if 2 in cs: bad.append(j)
        cs={v>>1 for c in cs for v in (c,c+Q-j) if not v&1}
    L=2*(n+3*K+10)+6
    assert not cs and lo>=L and not bad
    print(n,K,'empty',not cs,'min_left_bits',lo.bit_length(),'min_left_layer',arg,'margin',lo>=L,'bad',bad,'secs',round(monotonic()-t,2),flush=True)
