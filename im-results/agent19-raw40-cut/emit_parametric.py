"""Generate the five universal 1RB residue-sweep proofs. Lean checks every macro."""
from parametric import parse,step,search

def bl(s):return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def cat(*xs):return ' ++ '.join(x for x in xs if x!='[]') or '[]'
def cfg(q,l,r):return f'⟨{q}, {l}, {r}⟩'
def table(p):
    return 'def table : PartialMachine := fun s =>\n  match s.1.val,s.2 with\n'+''.join(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(m[0]=="1").lower()},{str(m[1]=="R").lower()},{ord(m[2])-65}⟩)\n' for i,m in enumerate(p) if m!='---')+'  | _,_ => none\n'
def mkconf(c,s,repeat='n'):
    _,side,pos,I=s;q,l,r=c;w=[bl(l),bl(r)];a=c[side+1];w[side]=cat(bl(a[:pos]),f'rep {bl(I)} {repeat}',bl(a[pos:]));return cfg(q,*w)
def epoch(e):
    k=e['k'];name=f'e{k}';ss=e['steps'];out=[];hs=[];costs=[]
    for j,s in enumerate(ss):
        a,b=s['src'],s['dst'];_,side,pos,I=a;_,side2,pos2,O=b;q,l,r=s['cfg'];qq,ll,rr=s['out'];w=[l,r];z=[ll,rr];cost=s['edge'][1];nm=f'{name}m{j}';h=f'h{j}';hs.append(h)
        if s['edge'][0]=='step':
            assert side==side2 and I==O and w[side][pos:]==z[side][pos2:]
            x=list(map(bl,w));y=list(map(bl,z));x[side]=cat(bl(w[side][:pos]),'R');y[side]=cat(bl(z[side][:pos2]),'R');out.append(f'theorem {nm} (R : List Bool) : run0 table {cost} {cfg(q,*x)} = some {cfg(qq,*y)} := by rfl');hs[-1]=(h,f'{nm} ({cat(f"rep {bl(I)} n",bl(w[side][pos:]))})');costs.append(str(cost))
        else:
            assert side!=side2 and q==qq and w==z
            lp=bl(l[:pos if side==0 else pos2]);rp=bl(r[:pos if side==1 else pos2]);L=bl(l[pos if side==0 else pos2:]);R=bl(r[pos if side==1 else pos2:]);ib=bl(I);ob=bl(O)
            if side==0:x=cfg(q,cat(lp,ib,'L'),cat(rp,'R'));y=cfg(q,cat(lp,'L'),cat(rp,ob,'R'))
            else:x=cfg(q,cat(lp,'L'),cat(rp,ib,'R'));y=cfg(q,cat(lp,ob,'L'),cat(rp,'R'))
            out.append(f'theorem {nm} (L R : List Bool) : run0 table {cost} {x} = some {y} := by rfl');hs[-1]=(h,f'sweep{"L" if side==0 else "R"} table {q} {lp} {rp} {ib} {ob} {cost} {nm} n {L} {R}');costs.append(f'{cost}*n')
    out.append(f'theorem {name} (n : Nat) : run0 table ({e["base"]}+{e["coef"]}*n) (C (6*n+{k})) = some (C (6*n+{e["kout"]})) := by')
    for h,expr in hs:out.append(f'  have {h} := {expr}')
    out.append('  simp only [List.append_assoc,List.nil_append,List.append_nil] at '+' '.join(h for h,_ in hs))
    H=hs[0][0]
    for h,_ in hs[1:]:H=f'(join0 {H} {h})'
    out.append(f'  have H := {H}')
    a=ss[0]['src'];b=ss[-1]['dst'];start=ss[0]['cfg'];finish=ss[-1]['out'];cs=mkconf(start,a);ce=mkconf(finish,b);costexpr='+'.join(costs)
    out.append(f'  change run0 table ({costexpr}) {cs} = some {ce} at H')
    for nm,s,c,num in [('hs',a,start,k),('he',b,finish,e['kout'])]:
        _,side,pos,I=s;assert side==0 and I=='111111' and set(c[1])=={'1'}
        x=cat(bl(c[1][:pos]),f'rep {bl(I)} n',bl(c[1][pos:]));out.append(f'  have {nm} : {x} = U (6*n+{num}) := by\n    have h := insertU {pos} n {len(c[1])-pos}\n    change {bl(c[1][:pos])} ++ rep {bl(I)} n ++ {bl(c[1][pos:])} = U (6*n+{num}) at h\n    simpa only [List.nil_append,List.append_nil] using h')
    out.append(f'  rw [hs,he] at H\n  simpa only [C,show {costexpr} = {e["base"]}+{e["coef"]}*n by omega] using H')
    return '\n'.join(out)+'\n'
HEAD='''import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1LC1RB
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
abbrev U (n : Nat) := List.replicate n true
def C (k : Nat) : Z0 := ⟨0,U k,[true,true,true]⟩
theorem uAdd (a b : Nat) : U (a+b) = U a ++ U b := List.replicate_append_replicate.symm
theorem repSix (n : Nat) : rep [true,true,true,true,true,true] n = U (6*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 6*(n+1)=6+6*n by omega,uAdd]
    rfl
theorem insertU (a n b : Nat) : U a ++ rep [true,true,true,true,true,true] n ++ U b = U (6*n+(a+b)) := by
  rw [repSix,←uAdd,←uAdd]
  congr 1
  omega
theorem neverInvariant (table : PartialMachine) (entry k : Nat) (hk : 6≤k)
    (first : run0 table entry ⟨0,[],[]⟩ = some (C k))
    (progress : ∀ k, 6≤k → ∃ t k', 0<t ∧ 6≤k' ∧ run0 table t (C k) = some (C k'))
    (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ n, ∃ t k, n≤t ∧ 6≤k ∧ run0 table t ⟨0,[],[]⟩ = some (C k) := by
    intro n
    induction n with
    | zero => exact ⟨entry,k,by omega,hk,first⟩
    | succ n ih =>
      obtain ⟨t,k,ht,hk,hr⟩ := ih
      obtain ⟨t',k',ht',hk',hr'⟩ := progress k hk
      exact ⟨t+t',k',by omega,hk',join0 hr hr'⟩
  intro n
  obtain ⟨t,k,ht,_,hr⟩ := arbitrary n
  have hz : (zrun table t start).map project = some (C k) := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed,show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl
'''
TABLES={307:'1RB1LC_1RC1RB_0RD0RE_1LD1LA_1RF1LE_---0LD',666:'1RB1LC_1RC1RB_0RD1RE_1LD1LA_0RF0LD_---0LA',670:'1RB1LC_1RC1RB_0RD1RE_1LD1LA_0RF0LD_---1RD',679:'1RB1LC_1RC1RB_0RD1RE_1LD1LA_1RF0LD_---0LB',683:'1RB1LC_1RC1RB_0RD1RE_1LD1LA_1RF0LD_---1RC'}
def generate():
    out=[HEAD]
    for i,t in TABLES.items():
        p=parse(t);es=[search(p,k) for k in range(6,12)];q,l,r=0,'',''
        for j in range(2000):
            if q==0 and len(l)>=6 and set(l)=={'1'} and r=='111':break
            q,l,r=step(p,q,l,r)
        else:raise ValueError('no entry')
        out.extend([f'namespace Leaf{i}',table(p),f'theorem entry : run0 table {j} ⟨0,[],[]⟩ = some (C {len(l)}) := by rfl'])
        out.extend(epoch(e) for e in es)
        out.append('theorem progress (k : Nat) (hk : 6≤k) : ∃ t k\', 0<t ∧ 6≤k\' ∧ run0 table t (C k) = some (C k\') := by\n  let n := (k-6)/6\n  have h : '+' ∨ '.join(f'k=6*n+{e["k"]}' for e in es)+' := by dsimp [n]; omega\n  rcases h with '+'|'.join('h' for e in es))
        for e in es:out.append(f'  · rw [h]\n    exact ⟨{e["base"]}+{e["coef"]}*n,6*n+{e["kout"]},by omega,by omega,e{e["k"]} n⟩')
        out.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverInvariant table {j} {len(l)} (by decide) entry progress m hm\n#print axioms never\nend Leaf{i}')
    out.append('end BB6.Agent19Raw40.A1LC1RB');return '\n'.join(out)+'\n'
if __name__=='__main__':print(generate(),end='')
