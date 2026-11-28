from pathlib import Path
import sys,re
TABLE = '1RB0LE_1RC1RA_0RD0RF_1LD0RA_1LA1LB_1RD---'
RULES = TABLE.replace('_','')
ENTRY=153471; PERIOD=15364; PREFIX=31; CHUNK=1024

def step(z):
    q,l,r=z
    s=int(l[0]) if l else 0
    rule=RULES[3*(2*q+s):3*(2*q+s+1)];assert rule!='---'
    w,d,q=rule;q=ord(q)-ord('A')
    if d=='R':return q,(r[0] if r else '0')+w+l[1:],r[1:]
    return q,l[1:],w+r

def trace(z,n,guard=False):
    out=[(0,z)]; minr=10000
    for i in range(1,n+1):
        minr=min(minr,len(z[2]))
        if guard:assert z[2],(i,z)
        z=step(z)
        if i%CHUNK==0 or i==n:out.append((i,z))
    print('min right',minr)
    return out

def num(s):return int('1'+s[::-1],2)
def packed(z):q,l,r=z;return f'⟨{q},{num(l)},{num(r)}⟩'
def bits(s):return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def literal(z):q,l,r=z;return f'⟨{q},{bits(l)},{bits(r)}⟩'

def split(path):
    path=Path(path)
    source=path.read_text()
    lines=source.splitlines()
    end='end BB6.Agent11Raw39LE4084Packed'
    header=lines[:5]
    base=lines[:next(i for i,l in enumerate(lines) if l.startswith('def entZ0'))]
    defs=[l for l in lines if re.match(r'def (ent|cyc)Z\d+ :',l)]
    chunks=[l.replace(':= by rfl',':= by decide +kernel') for l in lines if re.match(r'theorem (ent|cyc)C\d+ :',l)]
    joins=[]; active=False
    for l in lines:
        if re.match(r'theorem (ent|cyc)J\d+_\d+ :',l):active=True
        elif l.startswith('def family'):active=False
        elif l.startswith('def ') or re.match(r'theorem (ent|cyc)C\d+ :',l):active=False
        if active:joins.append(l)
    tail=lines[next(i for i,l in enumerate(lines) if l.startswith('def family')):]
    stem=path.stem
    b=stem+'Trace'
    path.with_name(b+'.lean').write_text('\n'.join(base+defs+[end])+'\n')
    names=[]
    for j in range(0,len(chunks),12):
        name=stem+f'Bank{j//12:02d}'
        path.with_name(name+'.lean').write_text('\n'.join(['import '+b]+header[1:]+chunks[j:j+12]+[end])+'\n')
        names.append(name)
    joined='\n'.join(['import '+n for n in names]+header[1:]+joins+tail)+'\n'
    signatures={}
    pattern=r'theorem ((?:ent|cyc)[CJ]\d+(?:_\d+)?) : (?:BB6.Agent11PackedPump.run|packedGuard) table (\d+) (\w+) = some (\w+)'
    for name,cost,a,b in re.findall(pattern,joined+'\n'+'\n'.join(chunks)):
        signatures[name]=(int(cost),a,b)
    def explicit(m):
        fn,l,r=m.groups();n,a,b=signatures[l];k,bb,c=signatures[r];assert b==bb
        return f'  exact @{fn} table {n} {k} {a} {b} {c} {l} {r}'
    joined=re.sub(r'  exact (BB6.Agent11PackedPump.join|guardJoin) (\w+) (\w+)',explicit,joined)
    joined=joined.replace('  apply run_sound\n  exact entJ0_150','  exact @run_sound table 153471 ⟨0,[],[]⟩ (family 0) entJ0_150').replace('  apply guard_sound\n  exact cycJ0_16','  exact @guard_sound table 15364 seed (appendR seed growthWord) cycJ0_16')
    path.write_text(joined)
    print('base',stem+'Trace','banks',len(names),'chunks',len(chunks),'join lines',len(joins))

def main(path):
    ent=trace((0,'',''),ENTRY);q,L,R=ent[-1][1];P,T=R[:PREFIX],R[PREFIX:]
    cyc=trace((q,L,P),PERIOD,True);q2,L2,R2=cyc[-1][1];Q=R2[PREFIX:];assert (q2,L2,R2[:PREFIX])==(q,L,P);assert Q=='000101000101000101'
    out=['import PackedPump','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent11Raw39LE4084Packed','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11PackedPump','', '/- Pump data discovered by Agent43, im-results/agent43-raw39-4084/generate_pump.py. -/','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    for i in range(12):
        tr=RULES[3*i:3*i+3]
        if tr=='---':continue
        w,d,q=tr;out.append(f'  | {i//2},{str(i%2==1).lower()} => some (some ⟨{str(w=="1").lower()},{str(d=="R").lower()},{ord(q)-65}⟩)')
    out+=['  | _,_ => none','',f'def seed : Z0 := {literal((0,L,P))}',f'def tailWord : List Bool := {bits(T)}',f'def growthWord : List Bool := {bits(Q)}','']
    def emit(name,rows,guard):
        run='packedGuard' if guard else 'BB6.Agent11PackedPump.run'
        join='guardJoin' if guard else 'BB6.Agent11PackedPump.join'
        for j,(_,z) in enumerate(rows):out.append(f'def {name}Z{j} : PZ := {packed(z)}')
        for j in range(len(rows)-1):
            n=rows[j+1][0]-rows[j][0];out.append(f'theorem {name}C{j} : {run} table {n} {name}Z{j} = some {name}Z{j+1} := by rfl')
        def combine(a,b):
            if a+1==b:return f'{name}C{a}'
            mid=(a+b)//2;l=combine(a,mid);r=combine(mid,b);th=f'{name}J{a}_{b}';cost=rows[b][0]-rows[a][0]
            out.append(f'theorem {th} : {run} table {cost} {name}Z{a} = some {name}Z{b} := by\n  exact {join} {l} {r}');return th
        return combine(0,len(rows)-1)
    e=emit('ent',ent,False);c=emit('cyc',cyc,True)
    out += ['','def family (n : Nat) : Z0 := appendR seed (rep growthWord n ++ tailWord)',f'theorem first : run0 table {ENTRY} ⟨0,[],[]⟩ = some (family 0) := by\n  apply run_sound\n  exact {e}',f'theorem cycle : guardRun table {PERIOD} seed = some (appendR seed growthWord) := by\n  apply guard_sound\n  exact {c}',f'theorem growth (n : Nat) : run0 table {PERIOD} (family n) = some (family (n+1)) := by\n  have h := guard_tail table {PERIOD} seed (appendR seed growthWord) (rep growthWord n ++ tailWord) cycle\n  simpa only [family,appendR,rep,List.append_assoc] using h',f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {ENTRY} (fun _ => {PERIOD}) first (by intro; decide) growth m hm','#print axioms first','#print axioms cycle','#print axioms never','end BB6.Agent11Raw39LE4084Packed']
    Path(path).write_text('\n'.join(out)+'\n')
    split(path)
if __name__=='__main__':main(sys.argv[1] if len(sys.argv)>1 else 'Raw39LE4084Packed.lean')
