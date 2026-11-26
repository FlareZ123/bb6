"""Raw57/1LB M211: exact prefix-rewrite invariant, no external dependencies.
Discovery is finite; the separately checked certificate proves all-time closure.
Run: python m211_prefix_certificate.py
"""
from collections import defaultdict, deque

TABLE = "1RB1LB_1RC0LE_0RD0RF_1LD1RE_1RA0LA_1RD---"
MOVES = tuple(TABLE.replace("_", "")[i:i+3] for i in range(0,36,3))

def move(q, bit):
    s = MOVES[2*q+bit]
    assert s != "---", "queried the undefined transition"
    return ord(s[2])-65, int(s[0]), 1 if s[1]=="R" else -1

def section(word):
    tape = {i for i,b in enumerate(word) if b=="1"}
    p = 0
    q = 1
    hi = -1
    for t in range(1,1000001):
        hi = max(hi,p)
        q,b,dp = move(q,int(p in tape))
        if b: tape.add(p)
        else: tape.discard(p)
        p += dp
        if q==1 and p<min(tape,default=p+1):
            out = "".join("1" if j in tape else "0"
                          for j in range(p,max(tape,default=p)+1))
            return out,t,p,hi
    raise RuntimeError("section discovery limit")

def discover():
    rules = {}
    w = "010001"
    t0 = 14
    entry = None
    for i in range(100):
        z,t,p,h = section(w)
        k = w[:h+1].ljust(h+1,"0")
        d = z[:h-p+1].ljust(h-p+1,"0")
        assert p<0
        assert k not in rules or rules[k]==(d,t)
        rules[k] = d,t
        t0 += t
        w = z
        if entry is None and len(w)>=161:
            entry = t0,w
    assert len(rules)==57 and max(map(len,rules))==161
    assert entry is not None and entry[0]==14922 and len(entry[1])==163
    return rules,entry

def run_zip(q,L,R,t):
    """Exact untrimmed zipper. An opaque tail sentinel must never be read."""
    L,R = deque(L),deque(R)
    for _ in range(t):
        a = R.popleft() if R else 0
        assert a in (0,1), "opaque suffix was accessed"
        q,b,dp = move(q,a)
        if dp==1:
            L.appendleft(b)
        else:
            c = L.popleft() if L else 0
            R.appendleft(b)
            R.appendleft(c)
    return q,list(L),list(R)

def bits(w): return list(map(int,w))

def check_macros(rules,entry):
    t,w = entry
    assert run_zip(0,[],[],t)==(1,[],bits(w))
    for k,(d,n) in rules.items():
        assert n>0
        marker = object()
        # The marker makes every attempted read of an arbitrary suffix fail;
        # exact returned stack identity proves that suffix remains untouched.
        assert run_zip(1,[],bits(k)+[marker],n)==(1,[],bits(d)+[marker])

def walk(trans,states,w):
    for a in w:
        states={r for s in states for r in trans.get((s,a),())}
        if not states: break
    return states

def build_automaton(rules,w):
    """Saturation over reverse prefix rules; not trusted by the checker."""
    edges = defaultdict(set)
    n = 1
    def fresh():
        nonlocal n
        s=n
        n+=1
        return s
    p=0
    for a in w:
        q=fresh()
        edges[p,a].add(q)
        p=q
    final=p
    trie={}
    pds=[]
    for k,(d,_) in rules.items():
        p=0
        for a in d[:-1]:
            if (p,a) not in trie:
                trie[p,a]=fresh()
                pds.append((p,a,trie[p,a],""))
            p=trie[p,a]
        pds.append((p,d[-1],0,k))
    rounds=0
    while True:
        added=0
        for p,a,q,v in reversed(pds):
            ends=walk(edges,{q},v)
            old=len(edges[p,a])
            edges[p,a].update(ends)
            added+=len(edges[p,a])-old
        rounds+=1
        if not added: break
    return edges,final,n,rounds

def check_invariant(rules,entry,edges,final):
    # Entry accepted. For every rule k -> d, any NFA path consuming k
    # from the start has the same endpoint available after consuming d.
    # Therefore every accepted k ++ R rewrites to an accepted d ++ R.
    assert final in walk(edges,{0},entry[1])
    for k,(d,_) in rules.items():
        assert walk(edges,{0},k)<=walk(edges,{0},d), k
    # Product of NFA with the trie recognizing words with no rule prefix.
    # A matched prefix exits the product permanently; a mismatch goes to -1.
    trie={}
    terminal=set()
    n=1
    for w in rules:
        p=0
        for a in w:
            if (p,a) not in trie:
                trie[p,a]=n
                n+=1
            p=trie[p,a]
        terminal.add(p)
    queue=deque([(0,0)])
    seen={(0,0)}
    while queue:
        s,p=queue.popleft()
        assert s!=final, "accepted word has no rule prefix"
        for a in "01":
            q=trie.get((p,a),-1)
            if q in terminal: continue
            for u in edges.get((s,a),()):
                pair=(u,q)
                if pair not in seen:
                    seen.add(pair)
                    queue.append(pair)
    return len(seen)

def main():
    rules,entry=discover()
    check_macros(rules,entry)
    edges,final,n,rounds=build_automaton(rules,entry[1])
    product=check_invariant(rules,entry,edges,final)
    print("table",TABLE)
    print("entry",entry[0],entry[1])
    print("rules",len(rules),"max input",max(map(len,rules)))
    print("NFA states",n,"edges",sum(map(len,edges.values())),
          "rounds",rounds,"uncovered product states",product)
    print("All exact macros, entry, closure and totality checked.")
    return rules,entry,edges,final,n

if __name__=="__main__":
    main()
