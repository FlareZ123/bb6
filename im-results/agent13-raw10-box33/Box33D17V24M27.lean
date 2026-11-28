import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V24M27
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .D false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .B false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .F false c)
  | .E,false => some (right .F true c)
  | .E,true => some (left .B false c)
  | .F,false => some (right .A false c)
  | .F,true => none
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
abbrev C := cfg .C
abbrev p := rep [false,true]
abbrev rP := rep [false,false,false,true]
abbrev rQ := rep [false,false,false,true,true]
abbrev ones5 := rep [true,false,false,false,false]
abbrev zeros := rep [false]
abbrev zeros5 := rep [false,false,false,false,false]

theorem start (l : Stream) : run 2 (A l z) = some (C l (word [true,true] z)) := by
  simp [A,C,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem leftOne (l r : Stream) : run 4 (C (p 2 l) (word [true,true] r)) =
    some (C l (word [true,true] (rP 1 r))) := by
  simp [C,cfg,p,rP,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem leftSweep (m : Nat) (l r : Stream) : run (4*m) (C (p (2*m) l) (word [true,true] r)) =
    some (C l (word [true,true] (rP m r))) := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
    rw [show 4*(m+1)=4+4*m by omega,show 2*(m+1)=2+2*m by omega,show p (2+2*m) l = p 2 (p (2*m) l) from rep_add [false,true] 2 (2*m) l,run_add,leftOne,Option.bind_some,ih]
    rw [show rP (m+1) r = rP m (rP 1 r) from rep_add _ m 1 r]
theorem evenTurn (l r : Stream) : run 4 (C (word [false,false] l) (word [true,true] r)) =
    some (A (p 1 l) (word [false,true] r)) := by
  simp [A,C,cfg,p,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem oddTurn (l r : Stream) : run 5 (C (word [false,true,false,false,false] l) (word [true,true] r)) =
    some (A l (word [false,false,true] (rP 1 r))) := by
  simp [A,C,cfg,rP,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightOne (l r : Stream) : run 12 (A l (word [false,true] (rP 1 r))) =
    some (A (p 2 l) (word [false,true] r)) := by
  simp [A,cfg,p,rP,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightFinish (l : Stream) : run 12 (A l (word [false,true] z)) = some (A (p 2 l) z) := by
  simp [A,cfg,p,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightSweep (m : Nat) (l : Stream) : run (12*m+12) (A l (word [false,true] (rP m z))) =
    some (A (p (2*m+2) l) z) := by
  induction m generalizing l with
  | zero => exact rightFinish l
  | succ m ih =>
    rw [show 12*(m+1)+12=12+(12*m+12) by omega,run_add]
    change (run 12 (A l (word [false,true] (rP 1 (rP m z))))).bind _ = _
    rw [rightOne,Option.bind_some,ih,show 2*(m+1)+2=(2*m+2)+2 by omega,show p (2*m+2+2) l = p (2*m+2) (p 2 l) from rep_add [false,true] (2*m+2) 2 l]
theorem evenReturn (m : Nat) (l : Stream) :
    run (16*m+18) (A (p (2*m) (zeros 6 l)) z) = some (A (p (2*m+3) (zeros 4 l)) z) := by
  rw [show 16*m+18=2+4*m+4+(12*m+12) by omega,run_add (2+4*m+4) (12*m+12),run_add (2+4*m) 4,run_add 2 (4*m),start,Option.bind_some,leftSweep,Option.bind_some]
  change (run 4 (C (word [false,false] (zeros 4 l)) (word [true,true] (rP m z)))).bind _ = _
  rw [evenTurn,Option.bind_some,rightSweep,show 2*m+3=(2*m+2)+1 by omega,show p (2*m+2+1) (zeros 4 l) = p (2*m+2) (p 1 (zeros 4 l)) from rep_add [false,true] (2*m+2) 1 (zeros 4 l)]

theorem carryOne (l r : Stream) : run 7 (A (push false (ones5 1 l)) (word [false,false,true] r)) =
    some (A (push false l) (word [false,false,true] (rQ 1 r))) := by
  simp [A,cfg,ones5,rQ,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem carrySweep (k : Nat) (l r : Stream) : run (7*k) (A (push false (ones5 k l)) (word [false,false,true] r)) =
    some (A (push false l) (word [false,false,true] (rQ k r))) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show 7*(k+1)=7+7*k by omega,run_add]
    change (run 7 (A (push false (ones5 1 (ones5 k l))) (word [false,false,true] r))).bind _ = _
    rw [carryOne,Option.bind_some,ih,show rQ (k+1) r = rQ k (rQ 1 r) from rep_add _ k 1 r]
theorem carryZero (l r : Stream) : run 6 (A (push false (zeros5 1 l)) (word [false,false,true] r)) =
    some (A (word [false,true] (zeros 4 l)) (word [false,true,true] r)) := by
  simp [A,cfg,zeros5,zeros,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem restoreQ (l r : Stream) : run 13 (A l (word [false,true,true] (rQ 1 r))) =
    some (A (zeros5 1 l) (word [false,true,true] r)) := by
  simp [A,cfg,rQ,zeros5,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem restoreP (l r : Stream) : run 13 (A l (word [false,true,true] (rP 1 r))) =
    some (A (zeros5 1 l) (word [false,true] r)) := by
  simp [A,cfg,rP,zeros5,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem restoreSweep (k : Nat) (l r : Stream) : run (13*k) (A l (word [false,true,true] (rQ k r))) =
    some (A (zeros5 k l) (word [false,true,true] r)) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    rw [show 13*(k+1)=13+13*k by omega,run_add]
    change (run 13 (A l (word [false,true,true] (rQ 1 (rQ k r))))).bind _ = _
    rw [restoreQ,Option.bind_some,ih,show zeros5 (k+1) l = zeros5 k (zeros5 1 l) from rep_add _ k 1 l]
theorem zeros5_eq (k : Nat) (l : Stream) : zeros5 k l = zeros (5*k) l := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 5*(k+1)=5+5*k by omega,show zeros (5+5*k) l = zeros 5 (zeros (5*k) l) from rep_add [false] 5 (5*k) l]
    change zeros 5 (zeros5 k l) = _
    rw [ih]
theorem oddReturn (m k : Nat) (l : Stream) :
    run (16*m+20*k+54) (A (p (2*m+3) (zeros 4 (ones5 k (zeros5 1 l)))) z) =
      some (A (p (2*(m+2)) (zeros 6 (zeros5 k (push true (zeros 4 l))))) z) := by
  rw [show 16*m+20*k+54=2+4*(m+1)+5+7*k+6+13*k+13+(12*(m+1)+12) by omega]
  rw [run_add (2+4*(m+1)+5+7*k+6+13*k+13) (12*(m+1)+12),run_add (2+4*(m+1)+5+7*k+6+13*k) 13,run_add (2+4*(m+1)+5+7*k+6) (13*k),run_add (2+4*(m+1)+5+7*k) 6,run_add (2+4*(m+1)+5) (7*k),run_add (2+4*(m+1)) 5,run_add 2 (4*(m+1)),start,Option.bind_some]
  rw [show 2*m+3=2*(m+1)+1 by omega,show p (2*(m+1)+1) (zeros 4 (ones5 k (zeros5 1 l))) = p (2*(m+1)) (p 1 (zeros 4 (ones5 k (zeros5 1 l)))) from rep_add [false,true] _ _ _]
  rw [leftSweep,Option.bind_some]
  change ((((((run 5 (C (word [false,true,false,false,false] (push false (ones5 k (zeros5 1 l)))) (word [true,true] (rP (m+1) z)))).bind (run (7*k))).bind (run 6)).bind (run (13*k))).bind (run 13)).bind (run (12*(m+1)+12))) = _
  rw [oddTurn,Option.bind_some,carrySweep,Option.bind_some,carryZero,Option.bind_some,restoreSweep,Option.bind_some,restoreP,Option.bind_some,rightSweep]
  rw [show 2*(m+1)+2=2*(m+2) by omega]
  rw [zeros5_eq,zeros5_eq]
  change some (A (p (2*(m+2)) (zeros 5 (zeros (5*k) (zeros 1 (push true (zeros 4 l)))))) z) = _
  rw [zeros5_eq]
  rw [show zeros (5*k) (zeros 1 (push true (zeros 4 l))) = zeros (5*k+1) (push true (zeros 4 l)) from (rep_add [false] (5*k) 1 _).symm,show 5*k+1=1+5*k by omega,show zeros (1+5*k) (push true (zeros 4 l)) = zeros 1 (zeros (5*k) (push true (zeros 4 l))) from rep_add [false] 1 (5*k) _]
  rfl

def bits : List Bool → Stream
  | [] => z
  | b::bs => push b (zeros 4 (bits bs))
theorem splitBits (bs : List Bool) : ∃ k ds, bits bs = ones5 k (zeros5 1 (bits ds)) := by
  induction bs with
  | nil => exact ⟨0,[],by simp [bits,ones5,zeros5,rep,word]⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨0,bs,rfl⟩
    | true =>
      obtain ⟨k,ds,h⟩ := ih
      exact ⟨k+1,ds,by change push true (zeros 4 (bits bs)) = _; rw [h]; rfl⟩
theorem zeroBits (k : Nat) (bs : List Bool) : zeros5 k (push true (zeros 4 (bits bs))) = bits (List.replicate k false ++ true::bs) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep_succ,List.replicate_succ,List.cons_append,bits,←ih]; rfl
def phase (odd : Bool) (m : Nat) (bs : List Bool) : Config :=
  if odd then A (p (2*m+3) (zeros 4 (bits bs))) z else A (p (2*m) (zeros 6 (bits bs))) z
theorem progress (odd : Bool) (m : Nat) (bs : List Bool) :
    ∃ t m' bs', 0<t ∧ run t (phase odd m bs) = some (phase (!odd) m' bs') := by
  cases odd with
  | false => exact ⟨16*m+18,m,bs,by omega,evenReturn m (bits bs)⟩
  | true =>
    obtain ⟨k,ds,h⟩ := splitBits bs
    refine ⟨16*m+20*k+54,m+2,List.replicate k false ++ true::ds,by omega,?_⟩
    simp only [phase,Bool.true_eq,ite_true,Bool.not_true,Bool.false_eq_true,ite_false]
    rw [h,←zeroBits]
    exact oddReturn m k (bits ds)
theorem neverPhase (t : Nat) (odd : Bool) (m : Nat) (bs : List Bool) : run t (phase odd m bs) ≠ none := by
  induction t using Nat.strongRecOn generalizing odd m bs with
  | ind t ih =>
    intro h
    obtain ⟨s,m',bs',hs,he⟩ := progress odd m bs
    by_cases ht : t≤s
    · rw [←show t+(s-t)=s by omega,run_add,h] at he
      contradiction
    · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ _ _ h
theorem neverBlank (t : Nat) : run t (A z z) ≠ none := by
  have he : phase false 0 [] = A z z := by simp [phase,bits,p,zeros,rep,word]
  rw [←he]
  exact neverPhase t false 0 []
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,14,11,6,1,13,17,22,24,5,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)
theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map BB6.Agent13.Box33PrefixMacro.project = step (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never : NeverHalts table := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever table step project_step
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank n
def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V24M27
