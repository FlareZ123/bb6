import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V18M2
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .E true c)
  | .E,false => some (right .E false c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .A false c)
  | .F,true => none
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
abbrev p := word [false,true,true]
abbrev L (n : Nat) := rep [false,true,true] n (push true z)
abbrev R10 := word [true,false]
abbrev R000 := word [false,false,false]
abbrev R010 := word [false,true,false]
abbrev R100 := word [true,false,false]
abbrev R110 := word [true,true,false]

theorem start110 (l r : Stream) : run 2 (A (p l) (R110 r)) = some (A (push true l) (R10 (R010 r))) := by
  simp [A,cfg,p,R110,R10,R010,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem start000 (l r : Stream) : run 10 (A (p l) (R000 r)) = some (A (push true l) (R10 (R110 r))) := by
  simp [A,cfg,p,R000,R10,R110,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem start100 (l r : Stream) : run 2 (A (p l) (R100 r)) = some (A (push true l) (R10 (R000 r))) := by
  simp [A,cfg,p,R100,R10,R000,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem startB (l r : Stream) : run 9 (A (push true (p l)) (R10 r)) = some (A (push true l) (R10 (R100 r))) := by
  simp [A,cfg,p,R10,R100,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem finish010 (l r : Stream) : run 3 (A l (R010 r)) = some (A (p l) r) := by
  simp [A,cfg,p,R010,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem base000 (r : Stream) : run 9 (A (L 0) (R000 r)) = some (A (L 1) r) := by
  simp [A,cfg,L,R000,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem baseB (r : Stream) : run 14 (A (push true (L 0)) (R10 r)) = some (A (L 1) r) := by
  have h : run 5 (A (push true (L 0)) (R10 r)) = some (A (L 0) (R000 r)) := by
    simp [A,cfg,L,R10,R000,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 14=5+9 by decide,run_add,h,Option.bind_some,base000]

def costB : Nat → Nat | 0 => 14 | n+1 => 4*costB n+26
def B (n : Nat) : Prop := ∀ r, run (costB n) (A (push true (L n)) (R10 r)) = some (A (L (n+1)) r)

theorem transfer110 (n : Nat) (h : B n) (r : Stream) : run (costB n+5) (A (L (n+1)) (R110 r)) = some (A (L (n+2)) r) := by
  rw [show costB n+5=2+costB n+3 by omega,run_add (2+costB n) 3,run_add 2 (costB n)]
  change ((run 2 (A (p (L n)) (R110 r))).bind (run (costB n))).bind (run 3) = _
  rw [start110,Option.bind_some,h,Option.bind_some,finish010]
  rfl

theorem transfer000 (n : Nat) (h : B n) (r : Stream) : run (2*costB n+15) (A (L (n+1)) (R000 r)) = some (A (L (n+2)) r) := by
  rw [show 2*costB n+15=10+costB n+(costB n+5) by omega,run_add (10+costB n) (costB n+5),run_add 10 (costB n)]
  change ((run 10 (A (p (L n)) (R000 r))).bind (run (costB n))).bind _ = _
  rw [start000,Option.bind_some,h,Option.bind_some,transfer110 n h]

theorem transfer100 (n : Nat) (h : B n) (r : Stream) : run (3*costB n+17) (A (L (n+1)) (R100 r)) = some (A (L (n+2)) r) := by
  rw [show 3*costB n+17=2+costB n+(2*costB n+15) by omega,run_add (2+costB n) (2*costB n+15),run_add 2 (costB n)]
  change ((run 2 (A (p (L n)) (R100 r))).bind (run (costB n))).bind _ = _
  rw [start100,Option.bind_some,h,Option.bind_some,transfer000 n h]

theorem transferB (n : Nat) : B n := by
  induction n with
  | zero => exact baseB
  | succ n ih =>
    intro r
    change run (4*costB n+26) (A (push true (p (L n))) (R10 r)) = some (A (L (n+2)) r)
    rw [show 4*costB n+26=9+costB n+(3*costB n+17) by omega,run_add (9+costB n) (3*costB n+17),run_add 9 (costB n),startB,Option.bind_some,ih,Option.bind_some,transfer100 n ih]

def cost : Nat → Nat | 0 => 9 | n+1 => 2*costB n+15

theorem epoch (n : Nat) : run (cost n) (A (L n) z) = some (A (L (n+1)) z) := by
  have hz : R000 z = z := by simp [R000,word]
  cases n with
  | zero => have h := base000 z; rw [hz] at h; exact h
  | succ n =>
    have h := transfer000 n (transferB n) z
    rw [hz] at h
    exact h

theorem neverPhase (t n : Nat) : run t (A (L n) z) ≠ none := by
  induction t using Nat.strongRecOn generalizing n with
  | ind t ih =>
    have hs : 0 < cost n := by cases n <;> simp [cost] <;> omega
    have he := epoch n
    intro h
    by_cases ht : t ≤ cost n
    · rw [←show t+(cost n-t)=cost n by omega,run_add,h] at he
      contradiction
    · rw [←show cost n+(t-cost n)=t by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ h

theorem init : run 8 (A z z) = some (A (L 0) z) := by
  simp [A,L,cfg,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem neverBlank (t : Nat) : run t (A z z) ≠ none := by
  intro h
  by_cases ht : t ≤ 8
  · have he := init
    rw [←show t+(8-t)=8 by omega,run_add,h] at he
    contradiction
  · rw [←show 8+(t-8)=t by omega,run_add,init,Option.bind_some] at h
    exact neverPhase _ _ h
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,9,11,24,1,13,17,19,18,4,2,0]
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
end BB6.Agent13.Box33D17V18M2
