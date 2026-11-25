#!/usr/bin/env python3
"""Infer and emit checked parameterized sweep traces. Search can fail; it
never contributes an unverified nonhalting claim. The Lean checker is the
only acceptance criterion for an emitted trace."""
from autoword import infer,Word,C
import sys,json

def bits(w):return '['+','.join('true' if x=='1' else 'false' for x in w)+']'
def word(w):return '(.periodic '+bits(w.pre)+' '+bits(w.block)+' '+word(w.post)+')' if w.block else '(.lit '+bits(w.pre)+')'
def cfg(z):return f'⟨{z.q},{word(z.l)},{word(z.r)}⟩'
def opstr(info):
    if info is None:return '.step'
    d,lp,rp,I,O,k,L,R=info
    if d=='L':lp,rp,L,R=rp,lp,R,L
    return f'.{"right" if d=="R" else "left"} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {word(L)} {word(R)} {k}'
def machine(i,t):
    out=[f'def p{i} : PartialMachine := fun s => match s.1.val,s.2 with']
    for k in range(12):
        a=t[3*k:3*k+3];v='none' if a=='---' else f'some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)'
        out.append(f'  | {k//2},{str(bool(k%2)).lower()} => {v}')
    out.append('  | _,_ => none')
    return '\n'.join(out)
def emit_one(i,t,r,source=True):
    j,f,(d,path,(a,b)),n=r
    ops='[\n    '+',\n    '.join(opstr(info) for z,y,info in path)+'\n  ]'
    s=machine(i,t)+f'\n\ndef c{i} : Cert := ⟨{j},{cfg(f)},{d},{ops},{a},{b}⟩\n\ntheorem checked{i} : check p{i} c{i} = true := by decide\n'
    if source:s+=f'theorem never{i} (m : Machine) (hm : compatible p{i} m) : NeverHalts m := check_never p{i} c{i} checked{i} m hm\n'
    return s

def emit(raws,output,ns='Raw13Auto',source=True,budget=1):
    out=['import '+('Agent46AutoPump' if source else 'AutoPump'),'set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace BB6Coverage.Agent31Pump.Auto.{ns}','open BB6Coverage Agent31Pump Auto']
    failed=[]
    for i,t in enumerate(raws):
        r=infer(t,budget=budget)
        if r and r[0]!='hole':
            out.append(emit_one(i,t,r,source))
            print(f'{i} {t} seed={r[0]} inc={r[2][0]} cost={r[2][2]}',file=sys.stderr,flush=True)
        else:failed.append((i,t));print(f'FAIL {i} {t}',file=sys.stderr,flush=True)
    out.append(f'end BB6Coverage.Agent31Pump.Auto.{ns}')
    open(output,'w').write('\n\n'.join(out)+'\n')
    return failed

def unpackword(w):
    return Word(w) if isinstance(w,str) else Word(w[0],w[1],unpackword(w[2]))

def emit_fixture(i,d,source=True):
    q,l,r=d['family'];f=C(q,unpackword(l),unpackword(r));path=[]
    for item in d['ops']:
        if isinstance(item,int):path.extend((None,None,None) for _ in range(item))
        else:
            dr,lp,rp,I,O,L,R,k=item;L,R=unpackword(L),unpackword(R)
            if dr=='L':lp,rp,L,R=rp,lp,R,L
            path.append((None,None,(dr,lp,rp,I,O,k,L,R)))
    return emit_one(i,d['table'],(d['entry'],f,(d['inc'],path,(d['a'],d['b'])),0),source)

def emit_fixtures(fixtures,output,ns,source=True):
    out=['import '+('Agent46AutoPump' if source else 'AutoPump'),'set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace BB6Coverage.Agent31Pump.Auto.{ns}','open BB6Coverage Agent31Pump Auto']
    out.extend(emit_fixture(i,d,source) for i,d in enumerate(fixtures))
    out.append(f'end BB6Coverage.Agent31Pump.Auto.{ns}')
    open(output,'w').write('\n\n'.join(out)+'\n')

if __name__=='__main__':
    source='--local' not in sys.argv
    ns=sys.argv[3] if len(sys.argv)>3 else 'Raw13Auto'
    if sys.argv[1].endswith('.json'):
        emit_fixtures(json.load(open(sys.argv[1])),sys.argv[2],ns,source)
    else:
        raw=[x.split()[0] for x in open(sys.argv[1]) if x.strip()]
        failed=emit(raw,sys.argv[2],ns,source,budget=5)
        sys.exit(bool(failed))
