"""Emit a Lean proof for each exact independent-counter return."""
from independent import *
import sys

def bits(s):return '['+','.join('true' if b=='1' else 'false' for b in s)+']'
def app(*xs):return ' ++ '.join('('+x+')' for x in xs if x!='[]') or '[]'
def lw(w):return app(*(f'rep {bits(x.block)} {x.var}' if isinstance(x,Rep) else bits(x) for x in w))
def cfg(c):return '⟨'+str(c.q)+','+lw(c.l)+','+lw(c.r)+'⟩'
def context(q,l,r):return '⟨'+str(q)+','+l+','+r+'⟩'
def lsum(cs):return '+'.join(([str(cs[''])] if cs.get('',0) else [])+[v if k==1 else f'{k}*{v}' for v,k in sorted(cs.items()) if v and k]) or '0'
def tab(p):
    ls=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    for i,a in enumerate(p):
        if a!='---':ls.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
    return '\n'.join(ls+['  | _,_ => none'])
SIMP='List.append_assoc,List.cons_append,List.nil_append,List.append_nil'
def grouped(w):
    runs=[]
    def add(b,x):
        if runs and runs[-1][0]==b:runs[-1][1].append(x)
        else:runs.append((b,[x]))
    for x in w:
        if isinstance(x,Rep):
            assert len(set(x.block))==1
            add(x.block[0],f'rep (List.replicate {len(x.block)} {str(x.block[0]=="1").lower()}) {x.var}')
        else:
            for b,g in groupby(x):add(b,f'List.replicate {len(list(g))} {str(b=="1").lower()}')
    return app(*(app(*terms) for _,terms in runs))
def eq_family(name,c,a,b,args):
    assert c.q==5 and not c.l
    return f'''theorem {name} {args} : ({cfg(c)} : Z0) = family ({a}) ({b}) := by
  unfold family
  congr 1
  calc
    _ = {grouped(c.r)} := by first | rfl | simp only [List.append_assoc] <;> rfl
    _ = _ := by
      simp only [rep_uniform,List.replicate_append_replicate]
      congr 1 <;> congr 1 <;> omega'''
def emit_branch(p,i,start,ans,barg,free):
    hist,last,(aa,bb)=ans
    args='(a b : Nat)' if free else '(a : Nat)'; vals='a b' if free else 'a'; ls=[]
    pre=f'p{i}_'
    ls.append(eq_family(pre+'entry',start,'a',barg,args));ls.append(eq_family(pre+'exit',last,lsum(aa),lsum(bb),args))
    seg=[];j=0
    while j<len(hist):
        x=hist[j]
        if x[0]=='step':
            k=j+1
            while k<len(hist) and hist[k][0]=='step':k+=1
            seg.append(('fixed',x[1],hist[k-1][2],k-j));j=k
        else:seg.append(x);j+=1
    costs=[]
    for j,x in enumerate(seg):
        typ,c,d,k=x[:4];name=pre+f'phase{j}'
        if typ=='fixed':
            ls.append(f'theorem {name} {args} : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl');costs.append(str(k));continue
        _,_,_,_,side,rep,O,fr,op,tail,ot=x;I=rep.block
        if side=='L':
            lp,rp,L,R=fr,op,tail,ot
            src=context(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));dst=context(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
        else:
            lp,rp,L,R=op,fr,ot,tail
            src=context(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));dst=context(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
        ln=pre+f'local{j}'
        ls.append(f'theorem {ln} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
        ls.append(f'theorem {name} {args} : run0 table ({k}*{rep.var}) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} {ln} {rep.var} ({lw(L)}) ({lw(R)})')
        costs.append(f'{k}*{rep.var}')
    join=f'({pre}phase0 {vals})'
    for j in range(1,len(seg)):join=f'(join0 {join} ({pre}phase{j} {vals}))'
    ls.append(f'''theorem return{i} {args} : ∃ k z', 0 < k ∧ run0 table k (family a ({barg})) = some z' ∧ Inv z' := by
  have H := {join}
  rw [{pre}entry {vals}, {pre}exit {vals}] at H
  exact ⟨{'+'.join(costs)}, family ({lsum(aa)}) ({lsum(bb)}), by omega, H, ⟨{lsum(aa)},{lsum(bb)},rfl⟩⟩''')
    return '\n\n'.join(ls),costs

def emit_machine(i):
    p=parse(ROWS[i]);cut=next(c for c in [1,2,3,4] if test(i,4,1,c));res=test(i,4,1,cut)
    ls=[f'namespace M{i}',f'-- {ROWS[i]}',tab(p),'''def family (a b : Nat) : Z0 := ⟨5,[],List.replicate (4+a) false ++ List.replicate (1+b) true⟩
def Inv (z : Z0) : Prop := ∃ a b, z = family a b
theorem entry : ∃ t z, run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z :=
  ⟨10,family 0 0,by rfl,⟨0,0,rfl⟩⟩''']
    for j,(st,ans) in enumerate(res):
        code,costs=emit_branch(p,j,st,ans,f'b+{j}' if j==cut else str(j),j==cut);ls.append(code)
    pr='''theorem closed : ∀ z, Inv z → ∃ k z', 0 < k ∧ run0 table k z = some z' ∧ Inv z' := by
  rintro z ⟨a,b,rfl⟩'''
    indent='  '
    for j in range(cut):
        pr+=f'\n{indent}cases b with\n{indent}| zero => exact return{j} a\n{indent}| succ b =>';indent+='  '
    pr+=f'\n{indent}exact return{cut} a b'
    ls.append(pr)
    ls.append('''theorem unbounded : ∀ n, ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z :=
  closed_arbitrary table Inv entry closed
#print axioms unbounded''')
    if '--local' not in sys.argv:
        ls.append('''theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_closed table Inv entry closed m hm
#print axioms never''')
    ls.append(f'end M{i}')
    return '\n\n'.join(ls)
if __name__=='__main__':
    print('import IndependentSweepCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nnamespace BB6Coverage.Agent40Independent.Raw118\nopen BB6Coverage Agent31Pump Agent40Independent')
    for i in sorted(ROWS):print(emit_machine(i))
    print('end BB6Coverage.Agent40Independent.Raw118')
