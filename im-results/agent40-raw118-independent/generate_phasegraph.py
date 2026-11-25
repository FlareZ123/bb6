"""Generate independently checkable Lean phase graphs; discovery is untrusted."""
from phasegraph import *
from generate_independent import bits,app,lw,cfg,context,tab,SIMP
import sys

def fam_config(f,n='n'):
    w=app(bits(f.pre),f'rep {bits(f.block)} ({n}+{f.base})',bits(f.suf))
    return context(f.q,w if f.side=='L' else '[]',w if f.side=='R' else '[]')

def exit_eq(name,c,g,off):
    w=c.l or c.r;x=next(x for x in w if isinstance(x,Rep));i=w.index(x);pre=''.join(w[:i]);suf=''.join(w[i+1:]);a,b,s,k,rots=canon(pre,x.block,suf)
    assert (a,b,s)==(g.pre,g.block,g.suf) and k==off+g.base
    ls=[f'theorem {name} (n : Nat) : ({cfg(c)} : Z0) = {fam_config(g,f"n+{off}")} := by','  congr 1','  all_goals','    calc']
    for p,P,S in rots:
        bit=p[-1];newP=bit+P[:-1];newpre=p[:-1];newsuf=bit+S
        ls.append(f'      _ = {app(bits(newpre),f"rep {bits(newP)} n",bits(newsuf))} := by simpa only [{SIMP}] using moveCut {bits(newpre)} {bits(S)} {bits(P[:-1])} {str(bit=="1").lower()} n')
    target=app(bits(a),app(f'rep {bits(b)} n',f'rep {bits(b)} {k}'),bits(s))
    ls.append(f'      _ = {target} := by first | rfl | simp only [rep,{SIMP}] <;> rfl')
    ls.append(f'      _ = _ := by rw [← rep_add] <;> rfl')
    return '\n'.join(ls)

def emit_arc(j,arc,fs):
    f=fs[j];cut,st,hist,last,idx,off,branches=arc;g=fs[idx];pre=f'p{j}_';ls=[]
    ls.append(f'theorem {pre}entry (n : Nat) : ({cfg(st)} : Z0) = family {j} (n+{cut}) := by\n  first | rfl | simp only [family,rep,{SIMP}] <;> rfl')
    ls.append(exit_eq(pre+'exit',last,g,off))
    seg=[];j0=0
    while j0<len(hist):
        x=hist[j0]
        if x[0]=='step':
            k=j0+1
            while k<len(hist) and hist[k][0]=='step':k+=1
            seg.append(('fixed',x[1],hist[k-1][2],k-j0));j0=k
        else:seg.append(x);j0+=1
    costs=[]
    for k0,x in enumerate(seg):
        typ,c,d,k=x[:4];name=pre+f'phase{k0}'
        if typ=='fixed':
            ls.append(f'theorem {name} (n : Nat) : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl');costs.append(str(k));continue
        _,_,_,_,side,rep,O,fr,op,tail,ot=x;I=rep.block
        if side=='L':
            lp,rp,L,R=fr,op,tail,ot
            src=context(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));dst=context(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
        else:
            lp,rp,L,R=op,fr,ot,tail
            src=context(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));dst=context(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
        ln=pre+f'local{k0}'
        ls.append(f'theorem {ln} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
        ls.append(f'theorem {name} (n : Nat) : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} {ln} n ({lw(L)}) ({lw(R)})')
        costs.append(f'{k}*n')
    join=f'({pre}phase0 n)'
    for k0 in range(1,len(seg)):join=f'(join0 {join} ({pre}phase{k0} n))'
    ls.append(f'''theorem generic{j} (n : Nat) : ∃ k z', 0 < k ∧ run0 table k (family {j} (n+{cut})) = some z' ∧ Inv z' := by
  have H := {join}
  rw [{pre}entry n, {pre}exit n] at H
  exact ⟨{'+'.join(costs)}, family {idx} (n+{off}), by omega, H, ⟨{idx},n+{off},by decide,rfl⟩⟩''')
    ls.append(f'''theorem progress{j} (n : Nat) : ∃ k z', 0 < k ∧ run0 table k (family {j} n) = some z' ∧ Inv z' := by''')
    indent='  '
    for a,steps,ind,m in branches:
        ls.append(f'{indent}cases n with\n{indent}| zero => exact ⟨{steps},family {ind} {m},by decide,by rfl,⟨{ind},{m},by decide,rfl⟩⟩\n{indent}| succ n =>');indent+='  '
    ls.append(f'{indent}exact generic{j} n')
    return '\n\n'.join(ls[:-len(branches)-1])+'\n'+'\n'.join(ls[-len(branches)-1:]) if branches else '\n\n'.join(ls[:-1])+'\n'+ls[-1]

def emit_machine(i,ans):
    p=parse(ROWS[i]);t,n,fs,arcs=ans;K=len(fs);ls=[f'namespace M{i}',f'-- {ROWS[i]}',tab(p)]
    ls.append('def family (i n : Nat) : Z0 := match i with\n'+'\n'.join(f'  | {j} => {fam_config(f)}' for j,f in enumerate(fs))+'\n  | _ => ⟨0,[],[]⟩')
    ls.append(f'''def Inv (z : Z0) : Prop := ∃ i n, i < {K} ∧ z = family i n
theorem entry : ∃ t z, run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z :=
  ⟨{t},family 0 {n},by rfl,⟨0,{n},by decide,rfl⟩⟩''')
    for j,a in enumerate(arcs):ls.append(emit_arc(j,a,fs))
    pr='''theorem closed : ∀ z, Inv z → ∃ k z', 0 < k ∧ run0 table k z = some z' ∧ Inv z' := by
  rintro z ⟨i,n,hi,rfl⟩'''
    for j in range(K):pr+=f'\n  rcases i with _ | i\n  · exact progress{j} n'
    pr+='\n  omega';ls.append(pr)
    ls.append('''theorem unbounded : ∀ n, ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z :=
  closed_arbitrary table Inv entry closed
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_closed table Inv entry closed m hm
#print axioms never''');ls.append(f'end M{i}');return '\n\n'.join(ls)

HEADER='import IndependentSweepCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nnamespace BB6Coverage.Agent40PhaseGraph.Raw118\nopen BB6Coverage Agent31Pump Agent40Independent'
FOOTER='end BB6Coverage.Agent40PhaseGraph.Raw118'

def generate(i):
    ans,msg=closure(i,1)
    if not ans:ans,msg=closure(i,1,maxfam=250,require_sweep=False)
    assert ans,(i,msg)
    local.cache_clear()
    return HEADER+'\n'+emit_machine(i,ans)+'\n'+FOOTER+'\n'

if __name__=='__main__':
    if sys.argv[1:]==['--modules']:
        d=Path(__file__).parent
        names=[]
        for i in TARGETS:
            name=f'Raw118PhaseM{i}'
            (d/(name+'.lean')).write_text(generate(i))
            names.append(name)
        (d/'Raw118PhaseGraph.lean').write_text(''.join(f'import {name}\n' for name in names))
    else:
        for i in map(int,sys.argv[1:]):print(generate(i))
