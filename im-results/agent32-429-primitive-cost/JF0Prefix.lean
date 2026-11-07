import JPhysicalPrefix
import Lean.Elab.Tactic.Omega

namespace BB429JPhysical
open BB6Coverage BB6Bubble BB429PhysicalFrontier

private theorem j_filled_one (u w : Nat) (hw : 2*u ≤ w+1) (x : Int)
    (hl : -2*(u:Int)-6 ≤ x) (hh : x ≤ 2*(u:Int)) :
    negFill (jTape u w) u x = true := by
  by_cases hf : negFillTest u x
  · simp [negFill,hf]
  · have hJ : jMark u w x := by
      unfold jMark jHole
      left
      refine ⟨by omega, by omega, ?_⟩
      intro hx
      have hF : negFillTest u x := by
        unfold negFillTest at *
        omega
      exact hf hF
    simp [negFill,hf,jTape,hJ]

private theorem j_step_ones (u w : Nat) (hw : 2*u ≤ w+1)
    (i : Nat) (hi : i < 2*(2*u+3)) :
    negFill (jTape u w) u (2*(u:Int)-(i:Int)) = true := by
  apply j_filled_one u w hw
  · omega
  · omega

/-- All-param exact left sweep from end of the bubble prefix. -/
theorem j_left_sweep (u w : Nat) (hw : 2*u ≤ w+1) :
    run target429 (4*u*u+6*u+6)
      {state := BB6Bubble.A, head := 0, tape := jTape u w} =
    some {state := BB6Bubble.A, head := -2*(u:Int)-6,
          tape := zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3)} := by
  have hfirst := j_prefix_exact u w hw
  have hsweep := AF_sweep target429 (2*(u:Int)) (negFill (jTape u w) u)
    (2*u+3) (by decide) (by decide) (j_step_ones u w hw)
  have hn : 4*u*u+6*u+6 = (4*u*u+2*u) + 2*(2*u+3) := by omega
  rw [hn,run_add',hfirst]
  simp only [Option.bind_some]
  rw [hsweep]
  apply congrArg some
  dsimp
  congr 1
  omega

private theorem j_endpoint_one (u w : Nat) (hw : 2*u ≤ w+1) :
    (zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3))
       (-2*(u:Int)-6) = true := by
  have hneg : zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3)
      (-2*(u:Int)-6) = negFill (jTape u w) u (-2*(u:Int)-6) := by
    apply zeroPaint_outside
    omega
  rw [hneg]
  exact j_filled_one u w hw (-2*(u:Int)-6) (by omega) (by omega)

private theorem F_head_zero (u w : Nat) (hw : 2*u ≤ w+1) :
  ((applyMove
    {state:=BB6Bubble.A, head:=-2*(u:Int)-6,
     tape:=zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3)}
    ⟨false,false,BB6Bubble.F⟩).tape) (-2*(u:Int)-7)=false := by
  have h : jTape u w (-2*(u:Int)-7)=false := by
    have hh : ¬jMark u w (-2*(u:Int)-7) := by unfold jMark jHole; omega
    simp [jTape,hh]
  have hF : negFill (jTape u w) u (-2*(u:Int)-7)=jTape u w (-2*(u:Int)-7) := by
    apply negFill_outside
    omega
  have hZ : zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3)
      (-2*(u:Int)-7)=negFill (jTape u w) u (-2*(u:Int)-7) := by
    apply zeroPaint_outside
    omega
  simp [applyMove,hZ,hF,h]

/-- All-param original raw prefix reaches F/0 exactly after a quadratic number
    of primitive steps. The untouched leftmost zero is physically verified. -/
theorem j_F0_prefix (u w : Nat) (hw : 2*u ≤ w+1) :
  ∃ c, run target429 (4*u*u+6*u+7)
      {state:=BB6Bubble.A, head:=0, tape:=jTape u w} = some c ∧
      c.state=BB6Bubble.F ∧ c.head=-2*(u:Int)-7 ∧ c.tape c.head=false := by
  have hp := j_left_sweep u w hw
  let c : Config :=
    applyMove
      {state:=BB6Bubble.A, head:=-2*(u:Int)-6,
       tape:=zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3)}
      ⟨false,false,BB6Bubble.F⟩
  have hone := j_endpoint_one u w hw
  have hs : readSlot
      {state:=BB6Bubble.A, head:=-2*(u:Int)-6,
       tape:=zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3)} = (BB6Bubble.A,true) := by
    exact Prod.ext rfl hone
  have htime : 4*u*u+6*u+7 = (4*u*u+6*u+6)+1 := by omega
  have hrun : run target429 (4*u*u+6*u+7)
      {state:=BB6Bubble.A, head:=0, tape:=jTape u w} = some c := by
    rw [htime]
    change (run target429 (4*u*u+6*u+6)
      {state:=BB6Bubble.A, head:=0, tape:=jTape u w}).bind (rawStep target429)=some c
    rw [hp]
    have hA1 : target429 (BB6Bubble.A,true) =
        some ⟨false,false,BB6Bubble.F⟩ := by decide
    simp [rawStep,hs,hA1,c]
  refine ⟨c,hrun,?_,?_,?_⟩
  · rfl
  · dsimp [c,applyMove]
    omega
  · have hz := F_head_zero u w hw
    have he : c.head = -2*(u:Int)-7 := by
      dsimp [c,applyMove]
      omega
    rw [he]
    exact hz

#print axioms j_left_sweep
#print axioms j_F0_prefix
end BB429JPhysical
