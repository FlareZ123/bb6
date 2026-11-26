"""Generate kernel-checked certificates and exact source-tree shards.
The generated files are untrusted until Lean accepts Box4Closure.lean.
Run from the scratch directory containing greedyboxes.json and tree6..11.txt.
"""
import json,glob,sys,subprocess
from pathlib import Path
from collections import defaultdict
from finish import domain_for
from greedy import HERE,cert,compress,safe_mask,mask_domain
sys.path.insert(0,str(HERE.parent/'agent13-raw10-box17'))
from emit_all import partial
from emit_bitpacked import packstack
OUT=Path(sys.argv[1] if len(sys.argv)>1 else HERE/'generated').resolve()
OUT.mkdir(parents=True,exist_ok=True)
HEADER='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
OPEN='open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box\nopen BB6.Agent13.Box17 (index decode tableEq tableEq_sound)\nopen BB6.Agent13BitPacked BB6.Agent13DomainPacked\n'
def write(name,imports,body):
    (OUT/(name+'.lean')).write_text(''.join('import '+i+'\n' for i in sorted(set(imports)))+HEADER+body)
def bools(x):return str(bool(x)).lower()
def code_table(t):
    return ''.join('---' if v==0 else f'{(v-1)//2%2}'+('R' if (v-1)%2 else 'L')+chr(65+(v-1)//4) for v in t)

def stack_cert(i,entry,c):
    ds=mask_domain(entry['mask']);rows=[[] for _ in range(12)];r=len(c['edges'][1])
    for s,l,j in c['states']:rows[s].append(r*l+j)
    ns=f'BB6.Agent13.Box4.Safe{i}'
    text=f'namespace {ns}\n'+OPEN
    text+='def codes (i : Fin 12) : List (Fin 25) := match i.val with\n'
    for j,d in enumerate(ds[:-1]):text+=f'  | {j} => {list(d)}\n'
    text+=f'  | _ => {list(ds[-1])}\n'
    text+='def b : Box Slot Transition := fun s => (codes (index s)).map decode\n'
    chunks=[]
    for j,ss in enumerate(rows):
        ss=sorted(set(ss));ch=[ss[k:k+48] for k in range(0,len(ss),48)];chunks.append(ch)
        text+=f'def row{j} : Row := ⟨{ch},{hex(sum(1<<x for x in ss))}⟩\n'
    text+=f'def c : Cert := ⟨{packstack(c["edges"][0],c["pushes"][0])},{packstack(c["edges"][1],c["pushes"][1])},#[{",".join(f"row{j}" for j in range(12))}]⟩\n'
    if len(c['states'])<=100:
        text+='theorem checked : checkDomain b c = true := by decide\n'
    else:
        for j,ch in enumerate(chunks):
            q=j//2;a=bools(j%2);names=[]
            text+=f'theorem valid{j} : (row c {q} {a}).valid = true := by decide\n'
            for k,x in enumerate(ch):
                nm=f'chunk{j}_{k}';names.append(nm)
                text+=f'theorem {nm} : domainIndices b c {q} {a} {x} = true := by decide\n'
            text+=f'theorem checked{j} : domainRow b c {q} {a} = true := by\n  change (row c {q} {a}).valid && ({ch} : List (List Nat)).all (domainIndices b c {q} {a}) = true\n  rw [valid{j}]\n  simp only [List.all_cons,List.all_nil,Bool.and_self{"," if names else ""}{",".join(names)}] <;> rfl\n'
        text+='''theorem checked : checkDomain b c = true := by
  unfold checkDomain
  have hb : (decide (0 < c.left.size) && decide (0 < c.right.size) && (c.left.pop 0).contains (false,0) && (c.right.pop 0).contains (false,0) && stateOK c 0 false 0 0) = true := by decide
  rw [hb]
  have hr : ∀ (q : Fin 6) (a : Bool), domainRow b c q a = true := by
    intro q a
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with h|h|h|h|h|h <;> subst q <;> cases a
'''+''.join(f'    · exact checked{j}\n' for j in range(12))+'''  simp [hr]
'''
    text+='def safeBox : BB6.Agent13.Box4.SafeBox := ⟨b,neverDomain b c checked⟩\n'
    return text+f'end {ns}\n'

def bank_modules():
    entries=json.load(open('greedyboxes.json'))['boxes'];refs={};body=[];total=0;group=0
    def flush():
        nonlocal body,total,group
        if body:
            write(f'Box4Bank{group:04d}',['Box4Tree'],'\n'.join(body));body=[];total=0;group+=1
    for i,e in enumerate(entries):
        c=compress(cert(e['t'],e['param']))
        assert tuple(e['mask'])==safe_mask(c)
        n=len(c['states'])
        if total+n>3000 or len(body)>=25:flush()
        refs[i]=(f'Box4Bank{group:04d}',f'BB6.Agent13.Box4.Safe{i}.safeBox')
        body.append(stack_cert(i,e,c));total+=n
    flush()
    print('stack certificate modules',group,flush=True)
    return refs

def block_modules():
    B=HERE.parent/'agent13-block-far'
    sys.path.insert(0,str(B))
    from generate_multi import generate
    rows=json.load(open(HERE/'survivors.json'))['block']
    widths=sorted({p[0] for _,p in rows}-{3})
    if widths:subprocess.run([sys.executable,str(B/'specialize.py'),*map(str,widths)],check=True)
    refs={}
    for i,(t,p) in enumerate(rows):
        width,cap,mod,runs,flip,mode=p
        suffix='' if width==3 else str(width)
        name=f'Box4Block{i:02d}';ns=f'BB6BlockFAR{suffix}.{name}';base=f'BB6BlockFAR{suffix}'
        generate(code_table(t),OUT,width,cap,mod,runs,flip,name,minimize_left=True,left_mode=mode)
        imports=[name+'Proof','BlockFARBridge'+suffix,'Box4Tree']
        text=f'namespace BB6.Agent13.Box4.Block{i}\n'+OPEN
        if flip:
            imports.append('FARBi')
            text+=f'''open BB6Coverage.FAR
def table : PartialMachine := reflectPartial ({base}.partialTable {ns}.machine)
theorem reflect_table : reflectPartial table = {base}.partialTable {ns}.machine := by
  funext x
  rcases x with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, reflectPartial table (q,b) = {base}.partialTable {ns}.machine (q,b) := by decide
  exact h q b
theorem safe (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply reflectNever m
  apply {base}.transfer_never {ns}.machine (reflectTable m)
  · rw [← reflect_table]
    exact reflectCompatible table m hm
  · exact {ns}.never
'''
        else:
            text+=f'''def table : PartialMachine := {base}.partialTable {ns}.machine
theorem safe (m : Machine) (hm : compatible table m) : NeverHalts m :=
  {base}.transfer_never {ns}.machine m hm {ns}.never
'''
        target=t.index(0)
        text+=f'''def p : PartialMachine := {partial(t)}
theorem p_safe (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply safe m
  intro s v hv
  have h : ∀ (q : Fin 6) (a : Bool), (table (q,a)).isSome = true → table (q,a) = p (q,a) := by decide
  have he := h s.1 s.2 (by simpa [hv])
  exact hm s v (he.symm ▸ hv)
def known : BB6.Agent13.Box4.Known {target} := ⟨p,BB6.Agent13.Box4.good_never {target} p p_safe⟩
end BB6.Agent13.Box4.Block{i}
'''
        write(name,imports,text)
        refs[tuple(t)]=(name,f'BB6.Agent13.Box4.Block{i}.known')
    return refs

class Node:
    __slots__=('t','kind','args','kids','size')
    def __init__(self,t,kind,args=(),kids=()):
        self.t=t;self.kind=kind;self.args=args;self.kids=kids
        self.size=1+sum(c.size for _,c in kids)

def load_tree(target,long,block):
    ds=domain_for(target);root=tuple(d[0] if len(d)==1 else -1 for d in ds)
    f=iter(open(f'tree{target}.txt'))
    def parse(t):
        line=next(f).split();k=line[0];a=tuple(map(int,line[1:]))
        if k=='b':
            s=a[0];return Node(t,'b',a,[(v,parse(t[:s]+(v,)+t[s+1:])) for v in ds[s]])
        if k=='o':
            assert a==t
            if t in block:return Node(t,'known',block[t])
            w=long[t]
            if w[0]=='halt':return Node(t,'h',(w[1],))
            if w[0] in ('cycle','side'):return Node(t,'c',tuple(w[1:]))
            raise ValueError((t,w))
        return Node(t,k,a)
    result=parse(root);assert next(f,None) is None
    return result

def tree_modules(target,root,boxes):
    cap=384;group=0;serial=0;body=[];imports=set();size=0
    def flush():
        nonlocal group,body,imports,size
        if body:
            write(f'Box4T{target}G{group:04d}',imports|{'Box4Tree'},'namespace BB6.Agent13.Box4\n'+OPEN+'\n'.join(body)+'\nend BB6.Agent13.Box4\n')
            group+=1;body=[];imports=set();size=0
    def materialize(node):
        nonlocal serial,size,body,imports
        # Materialize the largest children until the remaining local tree is small.
        if node.size>cap:
            kids=list(node.kids);sz=node.size
            for j,c in sorted(enumerate(kids),key=lambda x:-x[1][1].size):
                if sz<=cap:break
                v,u=c;ref=materialize(u)
                kids[j]=(v,Node(u.t,'known',ref));sz-=u.size-1
            node=Node(node.t,'b',node.args,kids)
        if size+node.size>3000 or len(body)>=32:flush()
        name=f'T{target}N{serial:06d}';serial+=1;mod=f'Box4T{target}G{group:04d}'
        known={};bank={}
        def render(n):
            if n.kind=='b':
                return f'.branch {n.args[0]} ['+','.join(f'({v},{render(c)})' for v,c in n.kids)+']'
            if n.kind=='h':
                return f'.leaf (.{"exact" if n.args[0]+6>3640 else "short"} {n.args[0]})'
            if n.kind=='c':
                e,k,d,b=n.args
                return f'.leaf (.cycle {e} {k} {bools(d)} ({b}))'
            if n.kind=='a':
                i=n.args[0];return f'.leaf (.box {bank.setdefault(i,len(bank))})'
            if n.kind=='known':
                return f'.leaf (.known {known.setdefault(tuple(n.args),len(known))})'
            raise ValueError(n.kind)
        tree=render(node);bs=[boxes[i] for i in bank];ks=list(known)
        imports.update(m for m,_ in bs+ks if m!=mod)
        text=f'def p{name} : PartialMachine := {partial(node.t)}\n'
        text+=f'def b{name} : Bank {target} := ⟨#[{",".join(ref for _,ref in ks)}],#[{",".join(ref for _,ref in bs)}]⟩\n'
        text+=f'def t{name} : Tree := {tree}\n'
        text+=f'theorem ok{name} : audit b{name} 12 p{name} t{name} = true := by decide\n'
        text+=f'def {name} : Known {target} := certified b{name} p{name} t{name} ok{name}\n'
        body.append(text);size+=node.size
        return mod,'BB6.Agent13.Box4.'+name
    mod,ref=materialize(root);flush()
    write(f'Box4Slice{target}',[mod,'Box4Tree'],f'''namespace BB6.Agent13.Box4
open BB6Coverage
open BB6.Agent13.Box17 (tableEq tableEq_sound)
theorem slice{target} : Good {target} (root {target}) := by
  have he : {ref}.p = root {target} := tableEq_sound _ _ (by decide)
  exact he ▸ {ref}.good
#print axioms slice{target}
end BB6.Agent13.Box4
''')
    print('slice',target,'nodes',root.size,'proof shards',serial,'modules',group,flush=True)

def main():
    boxes=bank_modules();block=block_modules();long={}
    for f in sorted(glob.glob('long*.json')):
        for t,w in json.load(open(f))['out']:
            long[tuple(t)]=w
    for target in range(6,12):tree_modules(target,load_tree(target,long,block),boxes)
    write('Box4Closure',[f'Box4Slice{t}' for t in range(6,12)],'''namespace BB6.Agent13.Box4
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
theorem allSlices : ∀ t : Fin 12, 6 ≤ t.val → Good t (root t) := by
  intro t ht
  have h : t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 := by omega
  rcases h with h|h|h|h|h|h <;> subst t
  · exact slice6
  · exact slice7
  · exact slice8
  · exact slice9
  · exact slice10
  · exact slice11
theorem sourceBound : ∀ m, Fits raw10Remainder[4]! m → WeightedBound 3640 m :=
  source_upper allSlices
theorem sourceExact (B : Nat) :
    (∀ m, Fits raw10Remainder[4]! m → WeightedBound B m) ↔ 3640 ≤ B :=
  exact_of_slices allSlices B
#print axioms sourceBound
#print axioms sourceExact
end BB6.Agent13.Box4
''')
if __name__=='__main__':main()
