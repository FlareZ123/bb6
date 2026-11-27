"""Specialize the checked single-triplet proof schema to paired banks.

The local identities and all generated induction theorems are kernel checked.
An extra D section accommodates the two reentrant terminal types; the
exceptional sibling88 b30 bridge consumes one unit of the exponent.
"""
from pathlib import Path
import re,sys,json
p=Path(__file__).resolve().parent
i=int(sys.argv[1]);N=f'Raw140{i}';A=N+'Arithmetic';inc=10 if i==88 else 12
ends=json.loads((p/f'raw140-{i}-paired-terminals.json').read_text()); rows={}
for n,e in ends.items():
 q,d,L,R=e['end'];m=re.match(r'[356]\^p\+(\d+)',L);assert m
 tag='d' if q==3 else 'b0' if q==1 else 'a2' if R=='2' else 'a0'
 rows[n]=(tag,int(m[1])-(25 if i==88 and n=='b30' else 24))
assert len(rows)==18
s=f'''import Std
namespace {A}
inductive Kind where | a0 | a2 | b0 | d deriving DecidableEq, Repr
abbrev Cfg := Kind × Nat
def next (s : Nat) := (s+1)%6
def carry (s : Nat) := if s=5 then 1 else 0
'''
for t in 'ABC':
 s+=f'def end{t} (p r s : Nat) : Cfg :=\n  match s with\n'
 for k in [1,3,5]:
  a,b=rows[t.lower()+str(k)+'0'],rows[t.lower()+str(k)+'1'];s+=f'  | {k} => if r=0 then (.{a[0]},p+{a[1]}) else (.{b[0]},p+{b[1]})\n'
 s+='  | _ => (.a0,p)\n'
 s=s.replace('p+-1','p-1')
 s+=f'def term{t} (p n s : Nat) : Cfg := end{t} (p+{inc}*(n/2)) (n%2) s\ntheorem end{t}_bound (p r s : Nat) : p ≤ (end{t} p r s).2 := by\n  unfold end{t}; split\n  all_goals (try split) <;> simp <;> omega\ntheorem term{t}_bound (p n s : Nat) : p ≤ (term{t} p n s).2 := by\n  have h := end{t}_bound (p+{inc}*(n/2)) (n%2) s\n  unfold term{t}; omega\n'
s+='''def dReturn (k : Nat) : Cfg :=
  let n := k/6; let s := k%6; let h := k+8
  if h%2=1 then termB (2*h+2) n s
  else termB (2*h+11) (n+carry s-2) (next s)
def ret : Kind → Nat → Cfg
  | .a2,p => dReturn (p-4)
  | .d,p => dReturn p
  | .a0,p =>
    let n := (p-5)/6; let s := (p-5)%6
    if p%2=0 then termC (2*p+6) n s
    else termC (2*p+15) (n+carry s-2) (next s)
  | .b0,p =>
    let n := (p-3)/6; let s := (p-3)%6
    let n' := n+carry s-1; let s' := next s
    if p%2=1 then termA (2*p+6) n' s'
    else termA (2*p+15) (n'+carry s'-2) (next s')
theorem dReturn_bound (k : Nat) : 2*k+18 ≤ (dReturn k).2 := by
  unfold dReturn; dsimp only; split
  · have h := termB_bound (2*(k+8)+2) (k/6) (k%6); omega
  · have h := termB_bound (2*(k+8)+11) (k/6+carry (k%6)-2) (next (k%6)); omega
theorem ret_growth (k : Kind) (p : Nat) (hp : 24 ≤ p) : 2*p ≤ (ret k p).2 := by
  cases k with
  | a2 => have h := dReturn_bound (p-4); simp only [ret]; omega
  | d => have h := dReturn_bound p; simp only [ret]; omega
  | a0 =>
    unfold ret; dsimp only; split
    · have h := termC_bound (2*p+6) ((p-5)/6) ((p-5)%6); omega
    · have h := termC_bound (2*p+15) ((p-5)/6+carry ((p-5)%6)-2) (next ((p-5)%6)); omega
  | b0 =>
    unfold ret; dsimp only; split
    · have h := termA_bound (2*p+6) ((p-3)/6+carry ((p-3)%6)-1) (next ((p-3)%6)); omega
    · have h := termA_bound (2*p+15) ((p-3)/6+carry ((p-3)%6)-1+carry (next ((p-3)%6))-2) (next (next ((p-3)%6))); omega
#print axioms ret_growth
'''
s+=f'end {A}\n'
if i==88: s=s.replace('p ≤ (endB','p-1 ≤ (endB').replace('p ≤ (termB','p-1 ≤ (termB').replace('2*k+18 ≤ (dReturn','2*k+17 ≤ (dReturn')
(p/(A+'.lean')).write_text(s)
for suf,T,rank in [('D','B','Raw140Double.rank'),('C','C','crank'),('B','A','arank')]:
 f=p/(N+suf+'.lean');s=f.read_text().replace('Raw14086Arithmetic',A)
 start=s.index('theorem '+T.lower()+'PumpAll');end=s.index('\ntheorem '+({'B':'rank_rho','C':'twoPumpAll','A':'onePumpAll'}[T]),start)
 if T=='B':
  cfg=lambda q,r:f'boundary 1 true (U 5 {q}) {r}'
  trip='TB';tail='Raw140Double.tailWord s';tname='Raw140Double.Tail';unfold='Raw140Double.tailWord,Raw140Double.rank';append='by simp only [TB,← word_append,← trips_add]';simp='tb_succ,trips,triple,word,Bool.false_eq_true,ite_true,ite_false,List.cons_append';pump='bPump'
 elif T=='C':
  cfg=lambda q,r:f'boundary 0 true (U 3 {q} ++ [S 2]) (S 2::({r}))'
  trip='T';tail='cword s';tname='CTail';unfold='cword,crank';append='by induction m with\n  | zero => simp [T,Raw14042Counter.T]\n  | succ m ih => simp [T,Raw14042Counter.T,ih,Nat.succ_add,List.cons_append,List.append_assoc]';simp='T,List.cons_append';pump='cPump'
 else:
  cfg=lambda q,r:f'boundary 0 true (U 3 {q} ++ [S 2]) {r}'
  trip='TA';tail='aword s';tname='ATail';unfold='aword,Raw140ERSuffix.tailWord,arank';append='by induction m with\n  | zero => simp [TA,Raw140VariantTransfer.trip]\n  | succ m ih => simp [TA,Raw140VariantTransfer.trip,ih,Nat.succ_add,List.cons_append,List.append_assoc]';simp='TA,Raw140VariantTransfer.trip,List.cons_append';pump='aPump'
 def C(q,r):return '('+cfg(q,r)+')'
 new=f'''theorem {trip}_appendPair (m n : Nat) : {trip} (m+n) = {trip} m ++ {trip} n := {append}

theorem {pump}AllPair (j p : Nat) (Y : List Sym) (hp : 24 ≤ p) :
    R {C('p',f'({trip} (2*j) ++ Y)')} {C(f'(p+{inc}*j)','Y')} := by
  induction j generalizing p with
  | zero => simpa [{trip},{'trips,word' if T=='B' else 'Raw14042Counter.T' if T=='C' else 'Raw14042Bank.T,Raw140VariantTransfer.trip'}] using Reach.refl M{i} {C('p','Y')}
  | succ j ih =>
    have h0 := rr ({pump} (p := p-24) ({trip} (2*j) ++ Y))
    have h1 : R {C('p',f'({trip} (2*(j+1)) ++ Y)')}
        {C(f'(p+{inc})',f'({trip} (2*j) ++ Y)')} := by
      simpa only [show 2*(j+1)=(2*j)+1+1 by omega,{simp},show p-24+24=p by omega,
        show p-24+{24+inc}=p+{inc} by omega] using h0
    simpa only [show p+{inc}+{inc}*j=p+{inc}*(j+1) by omega] using Reach.trans h1 (ih (p+{inc}) (by omega))

theorem terminal{T} (p r : Nat) (s : {tname}) (hp : 24 ≤ p) (hr : r < 2) (hodd : {rank} s % 2 = 1) :
    R {C('p',f'({trip} r ++ {tail})')} (cfg (end{T} p r ({rank} s))) := by
  cases s
'''
 for k in range(6):
  if k%2==0:new+=f'  · simp [{rank}] at hodd\n';continue
  new+='  · have h : r=0 ∨ r=1 := by omega\n    rcases h with rfl | rfl\n'
  for rem in range(2):
   name=T.lower()+str(k)+str(rem);tag,delta=rows[name];offset=25 if i==88 and name=='b30' else 24;exponent='p-1' if delta==-1 else f'p+{delta}';symbol={'a0':'A0','a2':'A2','b0':'B0','d':'D'}[tag]
   new+=f'    · simpa only [{trip},{simp},{unfold},end{T},cfg,{symbol},List.nil_append,List.cons_append,List.append_assoc,ite_true,ite_false,Nat.zero_ne_one,Nat.one_ne_zero,U,List.replicate_succ,List.replicate_zero,\n        show p-{offset}+{offset}=p by omega,show p-{offset}+{offset+delta}={exponent} by omega] using rr ({name} (p := p-{offset}))\n'
 new+=f'''
theorem drain{T} (p n : Nat) (s : {tname}) (hp : 24 ≤ p) (hodd : {rank} s % 2 = 1) :
    R {C('p',f'({trip} n ++ {tail})')} (cfg (term{T} p n ({rank} s))) := by
  have h0 := {pump}AllPair (n/2) p ({trip} (n%2) ++ {tail}) hp
  have h1 : R {C('p',f'({trip} n ++ {tail})')}
      {C(f'(p+{inc}*(n/2))',f'({trip} (n%2) ++ {tail})')} := by
    simpa only [← List.append_assoc,← {trip}_appendPair,show 2*(n/2)+n%2=n by omega] using h0
  exact Reach.trans h1 (terminal{T} _ _ s (by omega) (by omega) hodd)
'''
 if i==88 and T=='B':new=new.replace('(hp : 24 ≤ p) (hr :','(hp : 25 ≤ p) (hr :').replace('(hp : 24 ≤ p) (hodd :','(hp : 25 ≤ p) (hodd :').replace('hp\n  have h1 : R','(by omega)\n  have h1 : R')
 s=s[:start]+new+s[end:]
 if T=='B':
  ds=s.index('def D (k');de=s.index('\ntheorem dFront',ds);ddef=s[ds:de];s=s[:ds]+s[de:]
  s=s.replace('def cfg (c : Cfg)',ddef+'\ndef cfg (c : Cfg)').replace('| (.a0,p) => A0 p | (.a2,p) => A2 p | (.b0,p) => B0 p','| (.a0,p) => A0 p | (.a2,p) => A2 p | (.b0,p) => B0 p | (.d,p) => D p')
  ps=s.index('def Plus (a b');pe=s.index('\ntheorem a2Return',ps);plus=s[ps:pe];s=s[:ps]+s[pe:];s=s.replace('abbrev TB (n',plus+'\ntheorem Plus.reach {a b : Prim} (h : Plus a b) : R a b := by obtain ⟨n,_,h⟩ := h; exact ⟨n,h⟩\n\nabbrev TB (n')
  s=s.replace('theorem dFront (k : Nat) : R (D k)','theorem dFront (k : Nat) : Plus (D k)')
  old='''  have h2 := lift (dEndE (k+7) (TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2))
  have h3 : R (boundary 3 false [S 4]
    (U 4 (k+8) ++ TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2))
      (E 1 (k+7) (TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2)) := by
    simpa only [List.append_assoc,show k+7+1=k+8 by omega] using h2
  exact Reach.trans h1 h3'''
  new2=f'''  have h2 := run_ext M{i} ext _ _ _ (dEnd (U 4 (k+7) ++ TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2))
  have h3 : run M{i} 15 (boundary 3 false [S 4]
    (U 4 (k+8) ++ TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2)) = some
      (E 1 (k+7) (TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2)) := by
    simpa only [E,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc,show k+8=k+7+1 by omega] using h2
  obtain ⟨m,hm⟩ := h1
  exact ⟨m+15,by omega,join hm h3⟩'''
  assert old in s;s=s.replace(old,new2)
  s=s.replace('(ho : h%2=1) :','(ho : h%2=1) (hr : Raw140Double.rank s % 2 = 1) :').replace('(hn : 3 ≤ n) :','(hn : 3 ≤ n) (hr : Raw140Double.rank (Raw140Double.rho s) % 2 = 1) :')
  s=s.replace('termB (2*h+2+5*n)','termB (2*h+2) n').replace('termB (2*h+11+5*(n+Raw140Double.carry s-2))','termB (2*h+11) (n+Raw140Double.carry s-2)')
  s=s.replace('(drainB _ n s (by omega))','(drainB _ n s (by omega) hr)').replace('(drainB _ z _ (by omega))','(drainB _ z _ (by omega) hr)')
  s=s.replace('n t (by omega) hpar','n t (by omega) hpar (by omega)').replace('n t (by omega) (by omega) hn3','n t (by omega) (by omega) hn3 (by rw [rank_rho,hs]; unfold next; omega)')
  s=s.replace(' : R (D k) (cfg (dReturn k))',' : Plus (D k) (cfg (dReturn k))').replace('change R (D k) (E','change Plus (D k) (E').replace('have h := Reach.trans h0 h1','have h := Plus.transR h0 h1')
  s=s.replace('(dReturn_sound (p-4) (by omega))','(Plus.reach (dReturn_sound (p-4) (by omega)))')
 if T=='C':
  s=s.replace('n t (by omega)\n    simpa only [ret','n t (by omega) (by omega)\n    simpa only [ret').replace('(cn t) (by omega)\n    have h :=','(cn t) (by omega) (by rw [crank_next,hs]; unfold next; omega)\n    have h :=')
 if T=='A':
  s=s.replace('z t (by omega)\n    have h\'','z t (by omega) (by dsimp only [t]; rw [arank_next,hs]; unfold next; omega)\n    have h\'').replace('(an t) (by omega)\n    simp only','(an t) (by omega) (by dsimp only [t]; rw [arank_next,arank_next,hs]; unfold next; omega)\n    simp only')
 f.write_text(s)
f=p/(N+'Cover.lean');s=f.read_text().replace('Raw14086Arithmetic',A).replace('| b0 => exact b0Return p hp','| b0 => exact b0Return p hp\n  | d => exact dReturn_sound p (by omega)');f.write_text(s)
