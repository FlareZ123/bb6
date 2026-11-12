import HeadDisplacement
import BubblePrefix
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB6Bubble

open BB6Coverage BB429HeadDisplacement

/-- Every primitive prefix of the multi-bubble construction stays at or
    behind its final head.  The proof uses only the exact bubble-prefix
    theorem, the extremal left sweep in the next bubble, and the fact that
    each primitive transition moves the head by one cell. -/
theorem multi_bubble_prefix_head_bound
    (m : Machine) (u j t : Nat) (tape : Int → Bool)
    (hju : j ≤ u)
    (hmA1 : m (A,true)=some ⟨false,false,F⟩)
    (hmF1 : m (F,true)=some ⟨true,false,A⟩)
    (hmA0 : m (A,false)=some ⟨true,true,B⟩)
    (hmB1 : m (B,true)=some ⟨true,true,A⟩)
    (hz : ∀ i : Nat, i < u → tape (-2*((i+1:Nat):Int))=false)
    (ho : ∀ x : Int, -2*(u:Int) < x → x<0 → x%2≠0 → tape x=true)
    (hr : ∀ x : Int, 0≤x → x≤2*(u:Int) → tape x=true)
    (ht : t ≤ 4*j*j+2*j) :
    ∃ c', run m t {state:=A,head:=0,tape:=tape}=some c' ∧
      c'.head ≤ 2*(j:Int) := by
  induction j generalizing u t tape with
  | zero =>
      have ht0 : t = 0 := by omega
      subst t
      refine ⟨{state:=A,head:=0,tape:=tape}, ?_, by simp⟩
      simp [BB6Coverage.run]
  | succ j ih =>
      have hj : j ≤ u := by omega
      let c0 : Config := {state:=A,head:=0,tape:=tape}
      let cStage : Config := {state:=A,head:=2*(j:Int),tape:=negFill tape j}
      let cFinal : Config := {state:=A,head:=2*((j+1:Nat):Int),tape:=negFill tape (j+1)}
      have hStage : run m (4*j*j+2*j) c0 = some cStage := by
        simpa [c0,cStage] using
          multi_bubble_prefix m u j tape hj hmA1 hmF1 hmA0 hmB1 hz ho hr
      have hFull : run m (4*(j+1)*(j+1)+2*(j+1)) c0 = some cFinal := by
        simpa [c0,cFinal] using
          multi_bubble_prefix m u (j+1) tape hju hmA1 hmF1 hmA0 hmB1 hz ho hr
      have htime :
          4*(j+1)*(j+1)+2*(j+1) =
            (4*j*j+2*j) + (4*(2*j+1)+2) := by omega
      have hBubble : run m (4*(2*j+1)+2) cStage = some cFinal := by
        have hcomp := run_add' m (4*j*j+2*j) (4*(2*j+1)+2) c0
        rw [← htime] at hFull
        rw [hcomp, hStage] at hFull
        simpa using hFull
      have hAFones : ∀ i : Nat, i < 2*(2*j+1) →
          negFill tape j (2*(j:Int)-(i:Int)) = true := by
        intro i hi
        let x : Int := 2*(j:Int)-(i:Int)
        have hxlo : -2*((j+1):Int) < x := by
          dsimp [x]
          omega
        have hxhi : x ≤ 2*(j:Int) := by
          dsimp [x]
          omega
        change negFill tape j x = true
        by_cases hxpos : 0 ≤ x
        · have hval : tape x = true := hr x hxpos (by omega)
          unfold negFill
          have hnot : ¬negFillTest j x := by
            unfold negFillTest
            omega
          simp [hnot,hval]
        · have hxneg : x < 0 := by omega
          by_cases hxeven : x % 2 = 0
          · have hfill : negFillTest j x := by
              unfold negFillTest
              omega
            unfold negFill
            simp [hfill]
          · have hval : tape x = true := ho x (by omega) hxneg (by omega)
            have hnot : ¬negFillTest j x := by
              unfold negFillTest
              omega
            unfold negFill
            simp [hnot,hval]
      let c1 : Config :=
        {state:=A,
         head:=2*(j:Int)-2*((2*j+1:Nat):Int),
         tape:=zeroPaint (negFill tape j) (2*(j:Int)) (2*j+1)}
      have hAF : run m (2*(2*j+1)) cStage = some c1 := by
        simpa [cStage,c1] using
          AF_sweep m (2*j+1) (2*(j:Int)) (negFill tape j)
            hmA1 hmF1 hAFones
      have hAFhead : c1.head = cStage.head - 2*(2*j+1) := by
        simp [c1,cStage]
      by_cases hOld : t ≤ 4*j*j+2*j
      · obtain ⟨d,hpre,hbound⟩ :=
          ih u t tape hj hmA1 hmF1 hmA0 hmB1 hz ho hr hOld
        exact ⟨d,hpre,by omega⟩
      · let s : Nat := t-(4*j*j+2*j)
        have hs : s ≤ 4*(2*j+1)+2 := by
          dsimp [s]
          omega
        obtain ⟨d,hseg⟩ :=
          run_prefix_exists m (4*(2*j+1)+2) s cStage cFinal hBubble hs
        have htime2 : t = (4*j*j+2*j)+s := by
          dsimp [s]
          omega
        have hpre : run m t c0 = some d := by
          rw [htime2, run_add', hStage]
          simpa using hseg
        have hbound := bubble_macro_prefix_head_bound m (2*j+1) s
          cStage c1 cFinal d hAF hAFhead hBubble
          (by simp [cStage,cFinal] <;> omega) hs hseg
        exact ⟨d,hpre,by simpa [cStage] using hbound⟩

#print axioms multi_bubble_prefix_head_bound

end BB6Bubble
