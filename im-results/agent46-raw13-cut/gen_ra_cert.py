import pathlib,sys
trace=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2] if len(sys.argv)>2 else '.')
rows=[(0,0,0,0)]
def val(s): return int(s[::-1] or '0',2)
for line in trace.read_text().splitlines():
    i,kind,_,t,l,r=line.split('\t'); rows.append((int(t),5 if kind=='F0' else 0,val(l),val(r)))
assert len(rows)==25612 and rows[-1][0]==44423003584937617011264491060 and rows[-1][1]==5 and rows[-1][2]%2==0
n=len(rows)-1
ns='BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay'
head=f'namespace {ns}\nopen BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
def z(i):
    _,q,l,r=rows[i];return f'⟨{q},{l},{r}⟩'
def join(names):
    if len(names)==1:return names[0]
    m=len(names)//2;return f'(packed_join {join(names[:m])} {join(names[m:])})'
groups=[]
for gi,start in enumerate(range(0,n,1000)):
    end=min(n,start+1000); name=f'Raw13RAChunk{gi:02d}'; group=f'raGroup{gi:02d}';groups.append((name,group)); s='import Raw13Coupled6OneRAPacked\n'+head; chunks=[]
    for a in range(start,end,100):
        b=min(end,a+100); c=f'raPart{a:05d}';chunks.append(c); dt=rows[b][0]-rows[a][0]
        s+=f'theorem {c} : PackedOK {z(a)} {dt} {z(b)} :=\n  replayP_sound (by decide : replayP {b-a} {z(a)} = some ({dt},{z(b)}))\n\n'
    s+=f'theorem {group} : PackedOK {z(start)} {rows[end][0]-rows[start][0]} {z(end)} :=\n  {join(chunks)}\n#print axioms {group}\nend {ns}\n';(out/f'{name}.lean').write_text(s)
s='import Raw13RAWitness\n'+''.join('import '+name+'\n' for name,_ in groups)+head+'open BB6.Agent13BlankDelay\n'
s+=f'theorem raw13OneRA_assigned : PackedOK {z(0)} count {z(n)} :=\n  {join([g for _,g in groups])}\n\ntheorem raw13OneRA_cover : Cover (WeightedBound bound) p :=\n  packed_cover raw13OneRA_assigned (by decide) (by decide)\n\ntheorem raw13OneRA_bound (m : Machine) (hm : compatible p m) : WeightedBound bound m :=\n  raw13OneRA_cover.sound m hm\n\ntheorem raw13OneRA_halts : HaltsAfter (weightedTNFDefaultCompletion p) count :=\n  packed_halts raw13OneRA_assigned (by decide) (by decide)\n#print axioms raw13OneRA_halts\n#print axioms raw13OneRA_bound\n#print axioms raw13OneRA_assigned\n#print axioms raw13OneRA_cover\nend {ns}\n'
(out/'Raw13RAFinal.lean').write_text(s)

# Guided sparse prefixes replace expensive full-word parsing during kernel replay.
import subprocess
subprocess.run([sys.executable,str(pathlib.Path(__file__).with_name("gen_ra_guided.py")),str(trace),str(out)],check=True)
