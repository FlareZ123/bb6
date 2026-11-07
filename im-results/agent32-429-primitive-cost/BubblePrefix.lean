import BubbleExact
import Lean.Elab.Tactic.Omega

namespace BB6Bubble
open BB6Coverage

def negFillTest (j : Nat) (x : Int) : Prop :=
  -2*(j:Int) ≤ x ∧ x < 0 ∧ x % 2 = 0

instance negFillDecidable (j : Nat) (x : Int) : Decidable (negFillTest j x) := by
  unfold negFillTest
  infer_instance

def negFill (t : Int → Bool) (j : Nat) : Int → Bool :=
  fun x => if negFillTest j x then true else t x

theorem negFill_zero (t : Int → Bool) : negFill t 0 = t := by
  funext x
  have hh : ¬negFillTest 0 x := by unfold negFillTest; omega
  simp [negFill,hh]

theorem negFill_outside (t : Int → Bool) (j : Nat) (x : Int)
    (hl : x < -2*(j:Int)) : negFill t j x = t x := by
  have hh : ¬negFillTest j x := by unfold negFillTest; omega
  simp [negFill,hh]

theorem negFill_next (t : Int → Bool) (j : Nat) :
    negFill t (j+1) = fun x => if x = -2*((j+1:Nat):Int) then true else negFill t j x := by
  funext x
  by_cases hx : x = -2*((j+1:Nat):Int)
  · have hh : negFillTest (j+1) x := by
      subst x
      unfold negFillTest
      omega
    simp only [negFill, if_pos hh, if_pos hx]
  · have heq : negFillTest (j+1) x ↔ negFillTest j x := by
      unfold negFillTest
      omega
    by_cases ht : negFillTest j x
    · have hn : negFillTest (j+1) x := heq.mpr ht
      simp only [negFill, if_pos ht, if_pos hn, if_neg hx]
    · have hn : ¬negFillTest (j+1) x := fun v=>ht (heq.mp v)
      simp only [negFill, if_neg ht, if_neg hn, if_neg hx]

/-- General all-parameter multi-hole prefix invariant: successive exact
    A/F-A/B zigzags fill negative even holes and advance the head 2 cells.
    All other tape cells remain unchanged. -/
theorem multi_bubble_prefix (m : Machine) (u j : Nat) (t : Int → Bool)
    (hju : j ≤ u)
    (hmA1 : m (A,true)=some ⟨false,false,F⟩)
    (hmF1 : m (F,true)=some ⟨true,false,A⟩)
    (hmA0 : m (A,false)=some ⟨true,true,B⟩)
    (hmB1 : m (B,true)=some ⟨true,true,A⟩)
    (hz : ∀ i : Nat, i < u → t (-2*((i+1:Nat):Int))=false)
    (ho : ∀ x : Int, -2*(u:Int) < x → x<0 → x%2≠0 → t x=true)
    (hr : ∀ x : Int, 0≤x → x≤2*(u:Int) → t x=true) :
    run m (4*j*j+2*j) {state:=A,head:=0,tape:=t} =
      some {state:=A,head:=2*(j:Int),tape:=negFill t j} := by
  induction j with
  | zero => simp [run,negFill_zero]
  | succ j ih =>
    have hlt : j < u := by omega
    have hj : j ≤ u := by omega
    have hp := ih hj
    let h : Int := 2*(j:Int)
    let l : Int := -2*((j+1:Nat):Int)
    have hl : l = h-2*((2*j+1:Nat):Int) := by dsimp [h,l]; omega
    have hzj : negFill t j l=false := by
      have hs : l < -2*(j:Int) := by dsimp [l]; omega
      rw [negFill_outside t j l hs]
      exact hz j hlt
    have hoStage : ∀ x : Int, l<x → x≤h+1 → negFill t j x=true := by
      intro x hlo hhi
      by_cases hn : x<0
      · by_cases he : x%2=0
        · have ht : negFillTest j x := by
            unfold negFillTest
            dsimp [l,h] at hlo hhi
            omega
          simp [negFill,ht]
        · have ht : ¬negFillTest j x := by unfold negFillTest; omega
          rw [show negFill t j x = t x from by simp [negFill,ht]]
          apply ho x
          · dsimp [l] at hlo
            omega
          · exact hn
          · exact he
      · have ht : ¬negFillTest j x := by unfold negFillTest; omega
        rw [show negFill t j x = t x from by simp [negFill,ht]]
        apply hr x
        · omega
        · dsimp [h] at hhi
          omega
    have hb := bubble_exact m h l (2*j+1) (negFill t j)
      hmA1 hmF1 hmA0 hmB1 hl hzj hoStage
    have htime : 4*(j+1)*(j+1)+2*(j+1) = (4*j*j+2*j) + (4*(2*j+1)+2) := by
      simp [Nat.add_mul, Nat.mul_add]
      omega
    rw [htime, run_add', hp]
    simp only [Option.bind_some]
    have hhead : (2*(j:Int)) = h := by rfl
    have hb' : run m (4*(2*j+1)+2) {state:=A,head:=2*(j:Int),tape:=negFill t j} =
      some {state:=A,head:=h+2,tape:=fun x=>if x=l then true else negFill t j x} := by
        simpa only [hhead] using hb
    rw [hb']
    apply congrArg some
    dsimp [h,l]
    congr 1
    have hc : ((j+1:Nat):Int) = (j:Int)+1 := by omega
    simpa only [hc] using (negFill_next t j).symm

#print axioms multi_bubble_prefix
end BB6Bubble
