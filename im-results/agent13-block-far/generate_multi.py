#!/usr/bin/env python3
"""Generate a forward block-FAR certificate and kernel-checkable Lean source.
Usage: python generate.py [output-directory] [partial-table]
Requires only Python 3; the emitted files import BlockFAR and RangeCheck.
"""
from collections import defaultdict, deque
from functools import lru_cache
from pathlib import Path
import sys

DEFAULT_TABLE = '1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---'

def generate(table, out, width=3, cap=2, mod=4, runs=2, flip=False, name="HeldBlock", minimize_left=False, sparse=False):
    alphabet=2**width
    suffix="" if width==3 else str(width)
    ns="BB6BlockFAR"+suffix+"." + ("Held" if name=="HeldBlock" else name)
    code = table.replace('_', '')
    assert len(code) == 36
    moves = [None if t == '---' else (int(t[0]), (t[1] == 'R') != flip, ord(t[2])-65)
             for t in (code[i:i+3] for i in range(0,36,3))]
    assert all(m is None or (m[0] in (0,1) and 0 <= m[2] < 6) for m in moves)
    @lru_cache(None)
    def macro(q,d,a):
        h = 0 if d else width-1
        seen = set()
        while 0 <= h < width:
            k = (q,h,a)
            if k in seen: return None
            seen.add(k)
            mv = moves[2*q+(a>>h&1)]
            if mv is None: return None
            w,d,q = mv
            a = (a & ~(1<<h)) | (w<<h)
            h += 1 if d else -1
        return q,d,a

    left = [()]; leftids = {():0}; delta = {}; pred = defaultdict(list)
    nodes = [('T',)]; nodeids = {nodes[0]:0}
    edges = defaultdict(set); copier = defaultdict(set); pending = defaultdict(list); event = deque()
    def node(key):
        if key not in nodeids:
            nodeids[key] = len(nodes); nodes.append(key)
        return nodeids[key]
    def ctrl(l,q,d): return node(('c',l,q,int(d)))
    def add(s,a,t):
        if (a,t) not in edges[s]:
            edges[s].add((a,t)); event.append((s,a,t))
    def copy(q,v):
        if q not in copier[v]:
            copier[v].add(q)
            for a,t in tuple(edges[v]): add(q,a,t)
    def applyleft(l0,b,q,w,v):
        p = ctrl(l0,q,False); x = node(('x',p,b))
        add(x,w,v); add(p,b,x)
    def push(l,a):
        key = (l,a)
        if key in delta: return delta[key]
        xs = left[l]
        if not xs and a == 0: ys = ()
        elif xs and xs[0][0] == a:
            s,n,m = xs[0]; ys = ((s,min(cap,n+1),(m+1)%mod),)+xs[1:]
        else: ys = ((a,1,1%mod),)+xs[:runs-1]
        if ys not in leftids: leftids[ys] = len(left); left.append(ys)
        j = leftids[ys]; delta[key] = j; pred[j].append(key)
        for q,w,v in pending[j]: applyleft(l,a,q,w,v)
        return j
    push(0,0); add(0,0,0); copy(ctrl(0,0,True),0)
    count = 0
    while event:
        s,a,v = event.popleft(); count += 1
        if count > 5000000: raise RuntimeError('saturation limit')
        for q in tuple(copier[s]): add(q,a,v)
        key = nodes[s]
        if key[0] != 'c': continue
        _,l,q,d = key
        m = macro(q,bool(d),a)
        if m is None: raise RuntimeError(f'abstract row not a finite exit: {key}, {a}')
        q2,d2,w = m
        if d2: copy(ctrl(push(l,w),q2,True),v)
        else:
            pending[l].append((q2,w,v))
            for l0,b in tuple(pred[l]): applyleft(l0,b,q2,w,v)
    zero = {0}; rev = defaultdict(list)
    for s,es in edges.items():
        for a,t in es:
            if a == 0: rev[t].append(s)
    zq = deque(zero)
    while zq:
        for s in rev[zq.popleft()]:
            if s not in zero: zero.add(s); zq.append(s)
    assert all(v not in zero or q in zero for v,qs in copier.items() for q in qs)
    print('saturation',len(left),len(nodes),sum(map(len,edges.values())))

    # Quotient by equality of acceptance and sets of labelled successor classes.
    D = len(left); N = len(nodes)
    rows = defaultdict(set)
    for s,es in edges.items():
        for a,t in es: rows[s,a].add(t)
    cls = [int(s in zero) for s in range(N)]
    while True:
        keys = {}; new = []
        for s in range(N):
            k = (s in zero,tuple(tuple(sorted({cls[t] for t in rows[s,a]})) for a in range(alphabet)))
            new.append(keys.setdefault(k,len(keys)))
        if new == cls: break
        cls = new
    dead = len(set(cls)); C = dead+1
    r2 = defaultdict(set); z2 = {cls[s] for s in zero}
    for (s,a),ts in rows.items(): r2[cls[s],a].update(cls[t] for t in ts)
    ctr = {tuple(rest):cls[i] for i,(k,*rest) in enumerate(nodes) if k == 'c'}
    aux = {}
    for i,(k,*rest) in enumerate(nodes):
        if k == 'x':
            p,b = rest; _,l,q,d = nodes[p]; aux[l,q,d,b] = cls[i]
    if minimize_left:
        # Minimize left partial DFA preserving right control and auxiliary identities.
        sig=[tuple(ctr.get((l,q,d),dead) for q in range(6) for d in range(2))+tuple(aux.get((l,q,0,b),dead) for q in range(6) for b in range(alphabet)) for l in range(D)]
        lc=[0]*D
        while True:
            keys={};new=[]
            for l in range(D):
                k=(sig[l],tuple(lc[delta[l,a]] if (l,a) in delta else -1 for a in range(alphabet)))
                new.append(keys.setdefault(k,len(keys)))
            if new==lc:break
            lc=new
        D2=len(set(lc)); print('left minimized',D,'->',D2)
        delta={(lc[l],a):lc[j] for (l,a),j in delta.items()}
        ctr={(lc[l],q,d):v for (l,q,d),v in ctr.items()}
        aux={(lc[l],q,d,b):v for (l,q,d,b),v in aux.items()}
        D=D2
    pred = defaultdict(list)
    for (l,a),j in sorted(delta.items()): pred[j].append((l,a))
    assert delta[0,0] == 0 and ctr[0,0,1] in z2
    zeroNext = [min(r2[s,0]&z2) if s in z2 else dead for s in range(C)]
    checkcount = 0
    for l in range(D):
        for q in range(6):
            for d in range(2):
                p = ctr.get((l,q,d),dead)
                for a in range(alphabet):
                    ts = r2[p,a]
                    if not ts: continue
                    checkcount += 1
                    q2,d2,w = macro(q,bool(d),a)
                    if d2:
                        p2 = ctr[delta[l,w],q2,1]
                        for v in ts:
                            assert v not in z2 or p2 in z2
                            assert all(r2[v,b] <= r2[p2,b] for b in range(alphabet))
                    else:
                        for l0,b in pred[l]:
                            p2 = ctr[l0,q2,0]; x = aux[l0,q2,0,b]
                            assert x in r2[p2,b] and ts <= r2[x,w]
    print('checked',D,C,sum(map(len,r2.values())),len(z2),checkcount)
    data = dict(push=[1+delta[l,a] if (l,a) in delta else 0 for l in range(D) for a in range(alphabet)],
        ctrl=[ctr.get((l,q,d),dead) for l in range(D) for q in range(6) for d in range(2)],
        aux=[aux.get((l,q,0,b),dead) for l in range(D) for q in range(6) for b in range(alphabet)],
        edges=[sorted(r2[s,a]) for s in range(C) for a in range(alphabet)],
        zeroNext=zeroNext, pred=[[alphabet*l+a for l,a in pred[j]] for j in range(D)])
    def tree(xs, default):
        items=[(i,v) for i,v in enumerate(xs) if v!=default]
        def go(x):
            if not x:return str(default)
            if len(x)==1:
                i,v=x[0];return f'if i = {i} then {v} else {default}'
            k=len(x)//2
            return f'if i < {x[k][0]} then ({go(x[:k])}) else ({go(x[k:])})'
        return 'fun i => '+go(items)
    def pack(xs,b): return sum(v<<(b*i) for i,v in enumerate(xs))
    def vector(xs,b,stride):
        assert all(0<=x<2**b for x in xs)
        words = [hex(pack(xs[i:i+stride],b)) for i in range(0,len(xs),stride)]
        return f'⟨{b},{stride},#[\n'+',\n'.join(','.join(words[i:i+4]) for i in range(0,len(words),4))+']⟩'
    def packedrows(xs,b,length,stride):
        return f'⟨{vector([pack([v+1 for v in x],b) for x in xs],b*length,stride)},{b},{length}⟩'
    b = max(D,C).bit_length(); pb = (alphabet*D).bit_length()
    pm = max(1,max(map(len,data['pred']))); em = max(1,max(map(len,data['edges'])))
    s = '''import BlockFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6BlockFAR.Held

def machine : Table := fun q b =>
  (['''+','.join('none' if mv is None else f'some ⟨{str(bool(mv[0])).lower()},{str(mv[1]).lower()},{mv[2]}⟩' for mv in moves)+'''] : List (Option Move))[2*q.val+b.toNat]?.getD none

'''
    if sparse:
        s = s.replace("import BlockFAR", "import SparseBlockFAR"+suffix)
        for field,key in [('pushCodes','push'),('controlCodes','ctrl'),('auxiliaryCodes','aux'),('zeroNextCodes','zeroNext')]:
            s += f'def {field} : Nat → Nat := '+tree(data[key],0 if key=='push' else dead)+'\n\n'
        s += 'def predecessorCodes : Nat → List Nat := '+tree(data['pred'],[])+'\n\n'
        s += 'def edgeCodes : Nat → List Nat := '+tree(data['edges'],[])+'\n\n'
    else:
        for field,key in [('pushCodes','push'),('controlCodes','ctrl'),('auxiliaryCodes','aux'),('zeroNextCodes','zeroNext')]:
            s += f'def {field} : Packed := '+vector(data[key],b,32)+'\n\n'
        s += 'def predecessorCodes : PackedRows := '+packedrows(data['pred'],pb,pm,3)+'\n\n'
        s += 'def edgeCodes : PackedRows := '+packedrows(data['edges'],b,em,10)+'\n\n'
    s += 'def zeroCodes : Nat := '+hex(sum(1<<i for i in z2))+'\n\n'
    s += f'''def cert : Data {D-1} {C-1} := {{
  start := 0
  pushCodes := pushCodes
  controlCodes := controlCodes
  auxiliaryCodes := auxiliaryCodes
  predecessorCodes := predecessorCodes
  edgeCodes := edgeCodes
  zeroCodes := zeroCodes
  zeroNextCodes := zeroNextCodes
}}
end BB6BlockFAR.Held
'''
    if sparse: s = s.replace('def cert : Data', 'def cert : SparseData')
    out.mkdir(parents=True,exist_ok=True)
    (out/(name+'Packed.lean')).write_text(s.replace('BB6BlockFAR.Held',ns).replace('import BlockFAR\n','import BlockFAR'+suffix+'\n').replace('import RangeCheck\n','import RangeCheck'+suffix+'\n').replace('import HeldBlockPacked','import '+name+'Packed'),encoding='utf8')
    s = '''import HeldBlockPacked
import RangeCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6BlockFAR.Held

theorem base_ok : cert.baseCheck = true := by decide +kernel
'''
    for kind,f in [('pred','(fun l => symbols.all (cert.predCheckAt l))'),('rows','(cert.rowsAt machine)')]:
        for i in range(0,D,1 if width>=5 or D>200 else 10):
            s += f'theorem {kind}_{i} : rangeCheck {D-1} {f} {i} {min(1 if width>=5 or D>200 else 10,D-i)} = true := by decide +kernel\n'
        s += f'theorem {kind}_full : rangeCheck {D-1} {f} 0 {D} = true := by\n'
        expr = f'{kind}_0'
        for i in range(1 if width>=5 or D>200 else 10,D,1 if width>=5 or D>200 else 10):
            expr = f'(rangeCheck_join {D-1} {f} 0 {i} {min(1 if width>=5 or D>200 else 10,D-i)} {expr} {kind}_{i})'
        s += '  exact '+expr+'\n'
    s += '''theorem pred_ok : cert.predCheck = true := rangeCheck_full _ _ pred_full
theorem rows_ok : cert.rowsCheck machine = true := rangeCheck_full _ _ rows_full
theorem valid : cert.Valid machine := ⟨base_ok,pred_ok,rows_ok⟩
theorem never : ∀ k, ∃ c, run machine k primBlank = some c := cert.sound machine valid
#print axioms never
end BB6BlockFAR.Held
'''
    (out/(name+'Proof.lean')).write_text(s.replace('BB6BlockFAR.Held',ns).replace('import BlockFAR\n','import BlockFAR'+suffix+'\n').replace('import RangeCheck\n','import RangeCheck'+suffix+'\n').replace('import HeldBlockPacked','import '+name+'Packed'),encoding='utf8')

    # Also expose the same finite certificate to independent source checkers.
    # Existing Lean callers can continue ignoring the return value.
    return dict(width=width, moves=moves, left_states=D, right_nodes=C,
                zero_states=sorted(z2), **data)

if __name__ == '__main__':
    generate(sys.argv[2] if len(sys.argv)>2 else DEFAULT_TABLE, Path(sys.argv[1] if len(sys.argv)>1 else '.'))
