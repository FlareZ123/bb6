"""Deterministic six-hole discovery and Lean materializer; source checker is authoritative.
Usage: python generate_sixhole_child.py D0 QUERY_SLOT CODE OUTPUT_DIR
"""
from collections import Counter
from pathlib import Path
import sys
from generate_slice import simulate, gram, rle, learn, cert, boolean

ROOT=[8,-1,11,-1,13,13,-1,-1,-1,-1,-1,-1]
SPECS=[gram(k) for k in range(1,8)]+[rle(n,c,m) for n in range(1,4) for c in range(1,5) for m in range(1,4)]

def discover(d,s,v):
    root=ROOT.copy();root[6]=d;root[s]=v
    stats=Counter();maxhalt=0
    def visit(row):
        nonlocal maxhalt
        stats['nodes']+=1;mass=25**row.count(-1)
        w=simulate(row,120)
        if w[0]=='timeout':
            for desc in SPECS:
                c=learn(row,desc)
                if c is not None:
                    stats['far']+=1;stats['far_mass']+=mass;return ['far',c]
            w=simulate(row,2000)
        tag=w[0]
        if tag=='hole':
            i,t=w[1:]
            if row.count(-1)==1 and 0 not in row:
                maxhalt=max(maxhalt,t);stats['last']+=1;stats['last_mass']+=mass
                return ['last',i,t]
            stats['branch']+=1
            return ['branch',i,[visit(row[:i]+[j]+row[i+1:]) for j in range(25)]]
        if tag=='halt':maxhalt=max(maxhalt,w[1])
        if tag=='timeout':raise RuntimeError(('unresolved',row))
        stats[tag]+=1;stats[tag+'_mass']+=mass
        return list(w)
    tree=visit(root)
    assert sum(stats[k] for k in ('halt_mass','cycle_mass','last_mass','far_mass'))==25**6
    print(dict(stats), 'max live halt',maxhalt)
    return tree,max(255,maxhalt+6)

def emit(d,s,v,tree,B,out):
    prefix=f'Box27Child{d:02d}V{v:02d}';ns=f'BB6.Agent49.{prefix}';out=Path(out);out.mkdir(parents=True,exist_ok=True)
    head=f'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent49.Box27Slice\nopen BB6.Agent13.Box17 (decode slot)\n'
    def size(t):return 1+sum(size(c) for c in t[2]) if t[0]=='branch' else 1
    def term(t):
        tag,*a=t
        if tag=='halt':return f'.terminal (.halt {a[0]})'
        if tag=='last':return f'.terminal (.last {a[0]} {a[1]})'
        if tag=='cycle':return f'.terminal (.cycle {a[0]} {a[1]} {boolean(a[2])} ({a[3]}))'
        if tag=='far':return '.automata '+cert(a[0])
        i,k=a
        return f'.branch {i} ['+',\n'.join(f'({j}, {term(u)})' for j,u in enumerate(k))+']'
    core=prefix+'Core'
    (out/(core+'.lean')).write_text('import Box27CanonicalFrontier\nimport Box27SliceCore\n'+head+f'def base : PartialMachine := refine (BB6.Agent49.Box27EarlyTerminal.base {d}) (slot {s}) (decode {v})\nend {ns}\n')
    parts=[];buf=[];count=0;serial=0;joins=[]
    def flush():
        nonlocal buf,count
        if not buf:return
        name=f'{prefix}Part{len(parts):04d}';parts.append(name)
        (out/(name+'.lean')).write_text('import '+core+'\n'+head+'\n'.join(buf)+f'\nend {ns}\n');buf=[];count=0
    def go(t,p):
        nonlocal serial,count
        i=serial;serial+=1;n=f'g{i}';z=size(t)
        if z<=126:
            if count+z>400:flush()
            buf.append(f'def p{i} : PartialMachine := {p}\ndef t{i} : Tree := {term(t)}\ntheorem c{i} : audit {B} 6 p{i} t{i} = true := by decide\ntheorem {n} : Good {B} p{i} := audit_sound {B} 6 p{i} t{i} c{i}\n');count+=z;return n
        sl,k=t[1:];names=[go(c,f'(refine {p} (slot {sl}) (decode {j}))') for j,c in enumerate(k)]
        joins.append(f'theorem {n} : Good {B} {p} := by\n  apply split_good {B} {p} {sl}\n  intro v\n  have hv : '+' ∨ '.join(f'v = {j}' for j in range(25))+' := by omega\n  rcases hv with '+'|'.join(['rfl']*25)+'\n'+''.join('  · exact '+x+'\n' for x in names));return n
    name=go(tree,'base');flush()
    (out/(prefix+'Source.lean')).write_text(''.join('import '+p+'\n' for p in parts)+head+'\n'.join(joins)+f'\ntheorem bound : Good {B} base := {name}\n#print axioms bound\nend {ns}\n')
    print(prefix,len(parts),serial,len(joins))
if __name__=='__main__':
    d,s,v=map(int,sys.argv[1:4]);tree,B=discover(d,s,v);emit(d,s,v,tree,B,sys.argv[4])
