"""Emit kernel-checked guided chunks. The generator is untrusted; every
instruction is checked against exact packed tape semantics in Lean."""
import pathlib, sys
trace=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2]); only=set(map(int,sys.argv[3:]))
rows=[(0,0,0,0)]; instr=[]
def val(s): return int(s[::-1] or '0',2)
def bit(s): return 'true' if s else 'false'
def digit(r): return r%16==10 or (r%16==6 and r>=8)
def guide(r,n):
    if n==0: return f'(.lit {r})'
    assert digit(r), (r,n)
    b=int(r%16==6); s=r//16
    if s in (1,6):
        assert (b+n)//2 <= int(s==1)
        return f'(.term {bit(b)} {bit(s==1)})'
    k=(s^(s+1)).bit_length()-1
    m=k//3 if k and k%3==0 and digit(s>>k) else 0
    return f'(.bit {bit(b)} {m} {guide(s>>(3*m),((b+n)//2)<<m)})'
for line in trace.read_text().splitlines():
    i,kind,cost,t,l,r=line.split('\t'); rr=rows[-1][3]; k=(rr^(rr+1)).bit_length()-1
    if kind in ('fill','blank'):
        assert k%3==0
        inst=f'.fill {k//3} {guide(rr>>k,1<<(k//3))}'
    elif kind=='good':
        inst=f'.one {k} {guide(rr>>k,1)}'
    else:
        inst=f'.raw {cost}'
    instr.append(inst);rows.append((int(t),5 if kind=='F0' else 0,val(l),val(r)))
assert len(rows)==25612 and rows[-1][0]==44423003584937617011264491060 and rows[-1][1]==5 and rows[-1][2]%2==0
n=len(rows)-1
ns='BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay'
head=f'namespace {ns}\nopen BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
def z(i):
    _,q,l,r=rows[i];return f'⟨{q},{l},{r}⟩'
def join(names):
    if len(names)==1:return names[0]
    m=len(names)//2;return f'(packed_join {join(names[:m])} {join(names[m:])})'
for gi,start in enumerate(range(0,n,1000)):
    if only and gi not in only:continue
    end=min(n,start+1000); name=f'Raw13RAChunk{gi:02d}'; group=f'raGroup{gi:02d}'; s='import Raw13RAGuided\n'+head; chunks=[]
    for a in range(start,end,50):
        b=min(end,a+50); c=f'raPart{a:05d}'; chunks.append(c); dt=rows[b][0]-rows[a][0]; ins='['+',\n  '.join(instr[a:b])+']'
        s+=f'def ins{a:05d} : List Instr := {ins}\n'
        s+=f'theorem {c} : PackedOK {z(a)} {dt} {z(b)} :=\n  guidedReplay_sound (by decide : guidedReplay ins{a:05d} {z(a)} = some ({dt},{z(b)}))\n\n'
    s+=f'theorem {group} : PackedOK {z(start)} {rows[end][0]-rows[start][0]} {z(end)} :=\n  {join(chunks)}\n#print axioms {group}\nend {ns}\n';(out/f'{name}.lean').write_text(s)
