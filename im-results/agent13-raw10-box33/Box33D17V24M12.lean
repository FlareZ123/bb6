import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V24M12
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .A false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .A false c)
  | .E,false => some (right .F true c)
  | .E,true => some (right .B false c)
  | .F,false => some (right .A true c)
  | .F,true => none
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
abbrev p := rep [true,false]
abbrev q := rep [false,true]
abbrev zeros := rep [false]
theorem leftOne (l r : Stream) : run 4 (A (p 1 l) (zeros 2 r)) = some (A l (zeros 2 (q 1 r))) := by
  simp [A,cfg,p,q,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem leftSweep (n : Nat) (l r : Stream) : run (4*n) (A (p n l) (zeros 2 r)) = some (A l (zeros 2 (q n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 4*(n+1)=4+4*n by omega,run_add]
    change (run 4 (A (p 1 (p n l)) (zeros 2 r))).bind _ = _
    rw [leftOne,Option.bind_some,ih,show q (n+1) r = q n (q 1 r) from rep_add _ n 1 r]
theorem turn0 (l r : Stream) : run 7 (A (word [false,true,true] l) (zeros 2 r)) = some (A l (word [true,false,true,false,true] r)) := by
  simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem turn1 (l r : Stream) : run 7 (A (word [false,true,false] l) (zeros 2 r)) = some (A l (word [false,false,true,false,true] r)) := by
  simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem turn11 (l r : Stream) : run 8 (A (word [true,true] l) (zeros 2 r)) = some (A (word [false,true,true,false] l) r) := by
  simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem turn00 (l r : Stream) : run 8 (A (zeros 2 l) (zeros 2 r)) = some (A (word [false,true,true,true] l) r) := by
  simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightP (l r : Stream) : run 2 (A l (p 1 r)) = some (A (p 1 l) r) := by
  simp [A,cfg,p,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rightQ (l r : Stream) : run 2 (A l (q 1 r)) = some (A (q 1 l) r) := by
  simp [A,cfg,q,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem sweepP (n : Nat) (l r : Stream) : run (2*n) (A l (p n r)) = some (A (p n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,run_add]
    change (run 2 (A l (p 1 (p n r)))).bind _ = _
    rw [rightP,Option.bind_some,ih,show p (n+1) l = p n (p 1 l) from rep_add _ n 1 l]
theorem sweepQ (n : Nat) (l r : Stream) : run (2*n) (A l (q n r)) = some (A (q n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,run_add]
    change (run 2 (A l (q 1 (q n r)))).bind _ = _
    rw [rightQ,Option.bind_some,ih,show q (n+1) l = q n (q 1 l) from rep_add _ n 1 l]
theorem shiftQ (n : Nat) (l : Stream) : q n (push false l) = push false (p n l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change push false (push true (q n (push false l))) = _
    rw [ih]
    rfl
theorem pqz (n : Nat) : push true (q n z) = p (n+1) z := by
  have h := shiftQ n z
  rw [BB6.Agent13.Box33D14Growth.z_push] at h
  rw [h]
  rfl
def P (a b : Nat) (u : Stream) : Config := A (p a (push false (p b (word [true,true] u)))) z
theorem phase0 (a : Nat) (u : Stream) : run (6*a+13) (P a 0 u) = some (A (p (a+3) u) z) := by
  rw [show 6*a+13=4*a+7+2*(a+3) by omega,run_add (4*a+7) (2*(a+3)),run_add (4*a) 7]
  change ((run (4*a) (A (p a (word [false,true,true] u)) z)).bind (run 7)).bind _ = _
  have hz : zeros 2 z = z := by simp [zeros,rep,word]
  have h := leftSweep a (word [false,true,true] u) z
  rw [hz] at h
  rw [h,Option.bind_some,turn0,Option.bind_some]
  change run (2*(a+3)) (A u (p 2 (push true (q a z)))) = _
  rw [pqz,show p 2 (p (a+1) z) = p (a+3) z by rw [show a+3=2+(a+1) by omega]; exact (rep_add [true,false] 2 (a+1) z).symm,sweepP]
theorem phaseSucc (a b : Nat) (u : Stream) : run (6*a+6*(b+1)+13) (P a (b+1) u) = some (P (a+2) b (push false u)) := by
  rw [show 6*a+6*(b+1)+13=4*a+7+4*b+8+2*b+2*(a+2) by omega]
  rw [run_add (4*a+7+4*b+8+2*b) (2*(a+2)),run_add (4*a+7+4*b+8) (2*b),run_add (4*a+7+4*b) 8,run_add (4*a+7) (4*b),run_add (4*a) 7]
  have hz : zeros 2 z = z := by simp [zeros,rep,word]
  have h := leftSweep a (word [false,true,false] (p b (word [true,true] u))) z
  rw [hz] at h
  change (((((run (4*a) (A (p a (word [false,true,false] (p b (word [true,true] u)))) z)).bind (run 7)).bind (run (4*b))).bind (run 8)).bind (run (2*b))).bind _ = _
  rw [h,Option.bind_some,turn1,Option.bind_some]
  change (((run (4*b) (A (p b (word [true,true] u)) (zeros 2 (p 1 (push true (q a z)))))).bind (run 8)).bind (run (2*b))).bind _ = _
  rw [leftSweep,Option.bind_some,turn11,Option.bind_some,sweepQ,Option.bind_some,pqz,show p 1 (p (a+1) z) = p (a+2) z by rw [show a+2=1+(a+1) by omega]; exact (rep_add [true,false] 1 (a+1) z).symm,sweepP]
  change some (A (p (a+2) (q b (push false (word [true,true,false] u)))) z) = _
  rw [shiftQ]
  rfl
theorem reset (a : Nat) (u : Stream) : run (6*a+8) (A (p a (zeros 2 u)) z) = some (P 0 a (push true u)) := by
  rw [show 6*a+8=4*a+8+2*a by omega,run_add (4*a+8) (2*a),run_add (4*a) 8]
  have hz : zeros 2 z = z := by simp [zeros,rep,word]
  have h := leftSweep a (zeros 2 u) z
  rw [hz] at h
  rw [h,Option.bind_some,turn00,Option.bind_some,sweepQ]
  change some (A (q a (push false (word [true,true,true] u))) z) = _
  rw [shiftQ]
  rfl
theorem fullSweep (a b : Nat) (u : Stream) : ∃ t, 0<t ∧ run t (P a b u) = some (A (p (a+2*b+3) (zeros b u)) z) := by
  induction b generalizing a u with
  | zero => exact ⟨6*a+13,by omega,by simpa using phase0 a u⟩
  | succ b ih =>
    obtain ⟨t,ht,h⟩ := ih (a+2) (push false u)
    refine ⟨6*a+6*(b+1)+13+t,by omega,?_⟩
    rw [run_add,phaseSucc,Option.bind_some,h,show a+2*(b+1)+3=a+2+2*b+3 by omega]
    rw [show zeros (b+1) u = zeros b (zeros 1 u) from rep_add _ b 1 u]
    rfl
theorem progress (b : Nat) (u : Stream) (hb : 2≤b) : ∃ t u', 0<t ∧ run t (P 0 b u) = some (P 0 (2*b+3) u') := by
  obtain ⟨t,ht,h⟩ := fullSweep 0 b u
  refine ⟨t+(6*(2*b+3)+8),push true (zeros (b-2) u),by omega,?_⟩
  rw [run_add,h,Option.bind_some]
  simp only [Nat.zero_add]
  rw [show zeros b u = zeros 2 (zeros (b-2) u) by exact (congrArg (fun n => zeros n u) (show b=2+(b-2) by omega)).trans (rep_add [false] 2 (b-2) u),reset]
theorem neverPhase (t b : Nat) (u : Stream) (hb : 2≤b) : run t (P 0 b u) ≠ none := by
  induction t using Nat.strongRecOn generalizing b u with
  | ind t ih =>
    intro h
    obtain ⟨s,u',hs,he⟩ := progress b u hb
    by_cases ht : t≤s
    · rw [←show t+(s-t)=s by omega,run_add,h] at he
      contradiction
    · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ _ (by omega) h
theorem init : run 53 (A z z) = some (P 0 4 (push true z)) := by
  have h8 : run 8 (A z z) = some (P 0 0 (push true z)) := by
    simp [P,A,cfg,p,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h13 := phase0 0 (push true z)
  have h16 : run 16 (A (p 3 (push true z)) z) = some (A z (word [false,false,false,true,false,true,false,true,false,true] z)) := by
    simp [A,cfg,p,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h16' : run 16 (A z (word [false,false,false,true,false,true,false,true,false,true] z)) = some (P 0 4 (push true z)) := by
    simp [P,A,cfg,p,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 53=8+13+16+16 by decide,run_add (8+13+16) 16,run_add (8+13) 16,run_add 8 13,h8,Option.bind_some,h13,Option.bind_some,h16,Option.bind_some,h16']
theorem neverBlank (t : Nat) : run t (A z z) ≠ none := by
  intro h
  by_cases ht : t≤53
  · have he := init
    rw [←show t+(53-t)=53 by omega,run_add,h] at he
    contradiction
  · rw [←show 53+(t-53)=t by omega,run_add,init,Option.bind_some] at h
    exact neverPhase _ 4 _ (by decide) h
#print axioms neverBlank
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,22,11,2,1,13,17,1,24,6,4,0]
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
end BB6.Agent13.Box33D17V24M12
