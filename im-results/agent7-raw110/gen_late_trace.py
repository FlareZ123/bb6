"""Generate kernel-reduced finite trace certificates for raw110's final pair.
Run with output directory as argument. All generated claims use rfl, not native_decide.
"""
from pathlib import Path
import sys
from itertools import groupby
COMPRESSED = '--compressed' in sys.argv
PAIR={'A':'10','B':'01','C':'00','D':'11'}
REV={v:k for k,v in PAIR.items()}
def pairs(r):return ''.join(REV[r[i:i+2].ljust(2,'0')] for i in range(0,len(r),2))
def bw(slow,l,w):
    i=0;cost=0
    while True:
        if w[i:i+1]=='A': l='1'+l;i+=1;cost+=2
        elif w[i:i+2]=='CA':l='00'+l;i+=2;cost+=4
        else:break
    w=w[i:]
    if w[:1]=='D':return cost+1,None
    if w[:1]=='B':r='0'+''.join(PAIR[x] for x in w[1:]);cost+=7 if slow else 3
    elif w[:2]=='CB':r='011'+''.join(PAIR[x] for x in w[2:]);cost+=7
    elif w[:2]=='CC':r='010'+''.join(PAIR[x] for x in w[2:]);cost+=7
    elif w[:2]=='CD':r='100'+''.join(PAIR[x] for x in w[2:]);cost+=7
    else:assert w in ('','C');r='01';cost+=7
    k=len(l)-len(l.lstrip('0')); l=l[k:];r='10'*k+r;cost+=2*k
    if not l:return cost+4,('0',pairs(r))
    l=l[1:];r='0'+r;cost+=6 if slow else 2
    j=len(l)-len(l.lstrip('1'));l=l[j:];r='10'*j+r;cost+=2*j+3
    return cost,('00'+l[1:] if l else '0',pairs(r))
def state(s):
    l,r=s
    if COMPRESSED:
        runs=[(k,len(list(g))) for k,g in groupby(l)]
        a=len(r)-len(r.lstrip('A'))
        return '⟨['+','.join(f'({str(k=="1").lower()},{n})' for k,n in runs)+f'],{a},['+','.join('.'+x for x in r[a:])+']⟩'
    return '⟨['+','.join('true' if x=='1' else 'false' for x in l)+'],['+','.join('.'+x for x in r)+']⟩'
def chunks(slow,chunk=64):
    s=('1','');i=0;total=0
    while True:
        orig=s;cost=0
        for k in range(chunk):
            c,s=bw(slow,*s);cost+=c;i+=1
            if s is None:break
        total+=cost
        yield orig,s,k+1,cost,total
        if s is None:
            assert i==19203 and total==[6659485,6766857][slow],(i,total)
            break
HEADER='set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nopen BB6BlockFAR BB6Carry\n' + ('open BB6Raw110Run\nopen BB6Raw110Word (Outcome prepend_sound)\n' if COMPRESSED else 'open BB6Raw110Word\n')
def generate(out):
    out.mkdir(parents=True,exist_ok=True)
    imports=[]; assembly=[]
    for slow in (False,True):
        variant='Slow' if slow else 'Fast'
        b=str(slow).lower()
        rows=list(chunks(slow))
        segments=[]
        for part,start in enumerate(range(0,len(rows),40)):
            group=rows[start:start+40]
            mod=f'Raw110Word{variant}{part:02}'
            imports.append(mod)
            lines=['import '+('Raw110RunSweep' if COMPRESSED else 'Raw110WordSweep'),HEADER,f'namespace {mod}']
            lines.append(f'def s0 : State := {state(group[0][0])}')
            total=0
            for j,(a,z,n,c,t) in enumerate(group):
                if z is not None:
                    lines.append(f'def s{j+1} : State := {state(z)}')
                    lines.append(f'theorem ck{j} : replay {b} {n} s{j} = .next {c} s{j+1} := by rfl')
                    lines.append(f'theorem step{j} : BB6BlockFAR.run (machine {b}) {c} s{j}.render = some s{j+1}.render := checked_next {b} {n} {c} s{j} s{j+1} ck{j}')
                    proof=f'step{j}' if j==0 else f'@BB6Raw110Word.join {b} s0.render s{j}.render s{j+1}.render {total} {c} pre{j-1} step{j}'
                    lines.append(f'theorem pre{j} : BB6BlockFAR.run (machine {b}) {total+c} s0.render = some s{j+1}.render := {proof}')
                else:
                    lines.append(f'theorem ck{j} : replay {b} {n} s{j} = .halt {c} := by rfl')
                    lines.append(f'theorem step{j} : (Outcome.halt {c}).sound {b} s{j}.render := checked_halt {b} {n} {c} s{j} ck{j}')
                    proof=f'step{j}' if j==0 else f'@prepend_sound {b} s0.render s{j}.render {total} (.halt {c}) pre{j-1} step{j}'
                    lines.append(f'theorem pre{j} : (Outcome.halt {total+c}).sound {b} s0.render := {proof}')
                total+=c
            lines.extend([f'end {mod}',''])
            (out/(mod+'.lean')).write_text('\n'.join(lines))
            segments.append((mod,len(group)-1,total,group[-1][1] is None))
        total=1
        prev=f'first_sound {b}'
        for mod,j,c,halt in segments:
            if halt:
                assembly.append(f'theorem {variant.lower()}_trace : (Outcome.halt {total+c}).sound {b} primBlank  := @prepend_sound {b} primBlank {mod}.s0.render {total} (.halt {c}) ({prev}) {mod}.pre{j}')
                assembly.append(f'#print axioms {variant.lower()}_trace')
            else:
                name=f'{variant.lower()}_{mod[-2:]}'
                assembly.append(f'theorem {name} : BB6BlockFAR.run (machine {b}) {total+c} primBlank = some {mod}.s{j+1}.render  := @BB6Raw110Word.join {b} primBlank {mod}.s0.render {mod}.s{j+1}.render {total} {c} ({prev}) {mod}.pre{j}')
                prev=name
            total+=c
    (out/'Raw110WordTrace.lean').write_text('\n'.join('import '+m for m in imports)+'\n'+HEADER+'namespace BB6Raw110Trace\n'+'\n'.join(assembly)+'\nend BB6Raw110Trace\n')
if __name__=='__main__':
    generate(Path(sys.argv[1]))
