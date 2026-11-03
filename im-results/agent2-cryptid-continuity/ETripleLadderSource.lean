import Lean.Elab.Tactic.Omega
import ETripleFullSource

namespace BB6.ETripleLadderSource
open CryptidBoundary
open BB6.CryptidETriplePairsFirstReturn
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def stage (k q p : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false :: (pairs q ++ (List.replicate (3*p+3) true ++ false::ys)))

def cost (k q : Nat) : Nat := 12*k*k+49*k+58+6*q

private theorem replicate_three (p : Nat) :
    List.replicate (3*(p+1)+3) true =
      [true,true,true] ++ List.replicate (3*p+3) true := by
  rw [show 3*(p+1)+3=3+(3*p+3) by omega,
    ←List.replicate_append_replicate]
  rfl

private theorem shift_pairs (q : Nat) (ys : List Bool) :
    oppairs q ++ false::ys = false::(pairs q ++ ys) := by
  induction q with
  | zero => simp [oppairs,pairs]
  | succ q ih =>
    simp only [oppairs,pairs,List.cons_append]
    rw [ih]

/-- The actual source machine takes one E step between consecutive
    synthetic sections when k = 3v+2. -/
theorem stage_step (v q p : Nat) (ys : List Bool) :
    run (cost (3*v+2) q) (stage (3*v+2) q (p+1) ys) =
      stage (8*v+7) (q+2) p ys ∧
    ∀ t, 0<t → t<cost (3*v+2) q →
      ¬ IsPhysicalReturn (run t (stage (3*v+2) q (p+1) ys)) := by
  have hinput : stage (3*v+2) q (p+1) ys =
      init (List.replicate (3*(3*v+2)+2) true ++
        false :: (pairs q ++ ([true,true,true] ++
          (List.replicate (3*p+3) true ++ false::ys)))) := by
    simp [stage,replicate_three]
  have h := full_E_triple_pairs_first_return
    (3*v+2) q (List.replicate (3*p+3) true ++ false::ys)
  constructor
  · rw [hinput]
    change run (12*(3*v+2)*(3*v+2)+49*(3*v+2)+58+6*q) _ = _
    rw [h.1]
    simp [stage,init,shift_pairs]
    have hlen : 8*(3*v+2)+9 = 2+(3*(8*v+7)+2) := by omega
    rw [hlen, ← List.replicate_append_replicate]
    rfl
  · intro t hpos ht
    rw [hinput]
    exact h.2 t hpos ht

/-- A prefix index with guaranteed E-branch divisibility, avoiding Nat subtraction. -/
def kIndex : Nat → Nat → Nat
  | 0, u => u
  | m+1, u => 3*kIndex m u+2

private theorem kIndex_next (m u : Nat) :
    kIndex m (8*u+7) = 8*kIndex m u+7 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [kIndex,ih]
    omega

def level (m u q : Nat) (ys : List Bool) : Cfg :=
  stage (kIndex m u) q m ys

/-- First actual physical return of any E-ladder stage. -/
theorem level_step (m u q : Nat) (ys : List Bool) :
    run (cost (kIndex (m+1) u) q) (level (m+1) u q ys) =
      level m (8*u+7) (q+2) ys ∧
    ∀ t, 0<t → t<cost (kIndex (m+1) u) q →
      ¬IsPhysicalReturn (run t (level (m+1) u q ys)) := by
  simpa [level,kIndex,kIndex_next] using (stage_step (kIndex m u) q m ys)

def totalCost : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | m+1, u, q => cost (kIndex (m+1) u) q + totalCost m (8*u+7) (q+2)

def endU : Nat → Nat → Nat
  | 0, u => u
  | m+1, u => endU m (8*u+7)

/-- Exact original-source primitive total for an arbitrary-depth chain. -/
theorem level_run (m u q : Nat) (ys : List Bool) :
    run (totalCost m u q) (level m u q ys) =
      level 0 (endU m u) (q+2*m) ys := by
  induction m generalizing u q with
  | zero => simp [totalCost,level,endU,run]
  | succ m ih =>
    change run (cost (kIndex (m+1) u) q + totalCost m (8*u+7) (q+2))
      (level (m+1) u q ys) = _
    rw [run_add,(level_step m u q ys).1,ih]
    change level 0 (endU m (8*u+7)) ((q+2)+2*m) ys =
      level 0 (endU m (8*u+7)) (q+2*(m+1)) ys
    congr 1
    omega

/-- Recursive exact timestamps of successive physical F/0 returns. -/
def ReturnTime : Nat → Nat → Nat → Nat → Prop
  | 0, _, _, _ => False
  | m+1, u, q, t =>
      t=cost (kIndex (m+1) u) q ∨
      ∃ s, 0<s ∧ ReturnTime m (8*u+7) (q+2) s ∧
        t=cost (kIndex (m+1) u) q+s

/-- The source machine has physical returns at precisely the recursively
    enumerated checkpoints of an arbitrary-depth synthetic E ladder, through
    and including its terminal return time. -/
theorem level_returns_exact (m u q : Nat) (ys : List Bool) :
    ∀ t, 0<t → t≤totalCost m u q →
      (IsPhysicalReturn (run t (level m u q ys)) ↔
        ReturnTime m u q t) := by
  induction m generalizing u q with
  | zero =>
    intro t hpos hle
    simp [totalCost] at hle
    omega
  | succ m ih =>
    intro t hpos hle
    let a := cost (kIndex (m+1) u) q
    let b := totalCost m (8*u+7) (q+2)
    have htime : totalCost (m+1) u q=a+b := rfl
    rw [htime] at hle
    have hs := level_step m u q ys
    by_cases hbefore : t<a
    · constructor
      · intro hp
        exact False.elim ((hs.2 t hpos hbefore) hp)
      · intro hret
        change t=a ∨ ∃ s, 0<s ∧ ReturnTime m (8*u+7) (q+2) s ∧ t=a+s at hret
        rcases hret with heq | ⟨s,_,_,heq⟩
        all_goals omega
    · by_cases heq : t=a
      · subst t
        constructor
        · intro _
          change a=a ∨ _
          exact Or.inl rfl
        · intro _
          rw [hs.1]
          simp [IsPhysicalReturn,level,stage,init]
      · have hgreater : a<t := by omega
        have hdecomp : t=a+(t-a) := by omega
        have hremaining : 0<t-a := by omega
        have hbnd : t-a≤b := by omega
        rw [hdecomp,run_add,hs.1]
        have ih' := ih (8*u+7) (q+2) (t-a) hremaining hbnd
        constructor
        · intro hp
          have hrest := ih'.mp hp
          rw [←hdecomp]
          exact Or.inr ⟨t-a,hremaining,hrest,hdecomp⟩
        · intro hret
          have hr : ReturnTime m (8*u+7) (q+2) (t-a) := by
            rw [←hdecomp] at hret
            change t=a ∨ ∃ s, 0<s ∧ ReturnTime m (8*u+7) (q+2) s ∧ t=a+s at hret
            rcases hret with heq | ⟨s,_,hrest,hsum⟩
            · omega
            · have hsame : s=t-a := by omega
              rwa [hsame] at hrest
          exact ih'.mpr hr

#print axioms level_returns_exact
#print axioms stage_step
#print axioms level_step
#print axioms level_run
end BB6.ETripleLadderSource
