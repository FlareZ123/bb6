"""Emit chunked sparse zipper proofs for exact long last-hole traces."""
from pathlib import Path

def bits(xs):
    return '['+','.join('true' if x else 'false' for x in xs)+']'

def config(q,h,l,r):
    return f'⟨{q},({h}),{bits(l)},{bits(r)}⟩'

def trace_lines(tab,n,name,B,chunk=128):
    s='table'+name
    lines=[f'def {s} : PartialMachine := fun (q,b) => match q.val,b with']
    for i,m in enumerate(tab):
        if m!='---':
            lines.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(m[0]=="1").lower()},{str(m[1]=="R").lower()},{ord(m[2])-65}⟩)')
    lines+=['  | _,_ => none',f'def z{name}_0 : Z := zblank']
    q=h=0;l=[];r=[];prev=0
    for k in range(1,n+1):
        m=tab[2*q+(l[0] if l else 0)]
        assert m!='---',(name,k)
        w=int(m[0]);d=m[1];q=ord(m[2])-65
        if d=='R':
            l=[r[0] if r else 0,w]+l[1:];r=r[1:];h+=1
        else:
            l=l[1:];r=[w]+r;h-=1
        if k%chunk==0 or k==n:
            a=f'z{name}_{prev}';b=f'z{name}_{k}';p=f'run{name}_{prev}';t=f'run{name}_{k}';e=f'step{name}_{k}'
            lines += [f'def {b} : Z := {config(q,h,l,r)}',f'theorem {e} : zrun {s} {k-prev} {a} = some {b} := by decide +kernel']
            if prev==0: lines += [f'theorem {t} : zrun {s} {k} zblank = some {b} := {e}']
            else: lines += [f'theorem {t} : zrun {s} {k} zblank = some {b} := join {p} {e}']
            prev=k
    assert tab[2*q+(l[0] if l else 0)]=='---' and tab.count('---')==1
    lines += [f'theorem safe{name} : Cover (WeightedBound {B}) {s} := last_trace {B} {n} {s} z{name}_{n} run{name}_{n} (by decide) (by decide) (by decide) (by decide)',f'#print axioms safe{name}']
    return lines

def module(rid, B, traces, output):
    ns=f'Q0Root{rid}'
    lines=['import Q0Trace',f'import {ns}Base','set_option maxRecDepth 100000','set_option maxHeartbeats 0','open BB6Coverage BB6.Agent13BlankDelay Q0Trace Q0ExhaustiveTree BB6Coverage.Agent50Zipper',f'namespace {ns}']
    for i,(tab,n) in enumerate(traces):lines+=trace_lines(tab,n,str(i),B)
    lines += ['def longSym (p : PartialMachine) : Bool := '+ ' || '.join(['sym p']+[f'sameTable p table{i}' for i in range(len(traces))]), f'theorem longSym_sound (p : PartialMachine) (h : longSym p = true) : Cover (WeightedBound {B}) p := by', '  simp only [longSym, Bool.or_eq_true] at h', '  rcases h with '+ '|'.join(['h']*(len(traces)+1)), '  · exact sym_sound p h']
    for i in range(len(traces)):
        lines += [f'  · have he : p = table{i} := sameTable_sound h','    subst p',f'    exact safe{i}']
    lines += [f'end {ns}']
    Path(output).write_text('\n'.join(lines)+'\n')

if __name__=='__main__':
    import sys
    from generate_q0_exhaustive_lean import load, replace, MOVES
    manifest,tab,tree=load(Path(sys.argv[1])); traces=[]
    def walk(t,tab):
        if t[0]=='h' and t[1]>512: traces.append((tab,t[1]))
        if t[0]=='b':
            for k,m in zip(t[3],MOVES): walk(k,replace(tab,t[2],m))
    walk(tree,tab)
    module(manifest['rootId'],manifest['bound'],traces,sys.argv[2])
    print('long traces:',[( ''.join(t),n) for t,n in traces])
