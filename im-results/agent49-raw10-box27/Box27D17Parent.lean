import Box27SliceSource
import Box27Slice03Source
import Box27Slice22Source
import Box27Slice23Source
import Box27Slice24Source
import Box27EasyE0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27D17Parent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

/-- All 25 values of E0, rather than one selected five-hole slice, are covered.
    The original Raw10 Box27 domain and D0/D1 restrictions are explicit. -/
private theorem widen (B : Nat) (hB : B ≤ 255) (m : Machine)
    (h : WeightedBound B m) : WeightedBound 255 m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hB

theorem bound255 (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode 14) (hd1 : m (3,true) = decode 17) :
    WeightedBound 255 m := by
  obtain ⟨e,he⟩ := BB6.Agent49.Box27Slice.decode_surjective (m (4,false))
  have heval : m (4,false) = decode e := he.symm
  by_cases hEasy : e ∈ BB6.Agent49.Box27EasyE0.easy
  · exact widen 108 (by decide) m
      (BB6.Agent49.Box27EasyE0.source_bound m hm hd0 hd1 ⟨e,hEasy,heval⟩)
  · have hother : e=3 ∨ e=21 ∨ e=22 ∨ e=23 ∨ e=24 := by
      change e ∉ ([0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] :
        List (Fin 25)) at hEasy
      simp only [List.mem_cons] at hEasy
      have hsmall := e.isLt
      omega
    rcases hother with h3|h21|h22|h23|h24
    · have h : m (4,false) = decode 3 := by simpa [h3] using heval
      exact widen 141 (by decide) m
        (BB6.Agent49.Box27Slice03.parent_bound m hm hd0 hd1 h)
    · have h : m (4,false) = decode 21 := by simpa [h21] using heval
      exact widen 108 (by decide) m
        (BB6.Agent49.Box27Slice.parent_bound m hm hd0 hd1 h)
    · have h : m (4,false) = decode 22 := by simpa [h22] using heval
      exact widen 149 (by decide) m
        (BB6.Agent49.Box27Slice22.all_parent_bound m hm hd0 hd1 h)
    · have h : m (4,false) = decode 23 := by simpa [h23] using heval
      exact widen 143 (by decide) m
        (BB6.Agent49.Box27Slice23.parent_bound m hm hd0 hd1 h)
    · have h : m (4,false) = decode 24 := by simpa [h24] using heval
      exact BB6.Agent49.Box27Slice24.parent_bound m hm hd0 hd1 h

/-- E0=24 provides the sharp halting lower witness for the entire D0/D1 slice. -/
theorem attainer_fits :
    Fits raw10Remainder[27]! BB6.Agent49.Box27Slice24.attainer := by
  intro s
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem attainer_d0 :
    BB6.Agent49.Box27Slice24.attainer (3,false) = decode 14 := by decide
theorem attainer_d1 :
    BB6.Agent49.Box27Slice24.attainer (3,true) = decode 17 := by decide

theorem exact_weighted (B : Nat) :
    (∀ m, Fits raw10Remainder[27]! m →
       m (3,false) = decode 14 → m (3,true) = decode 17 → WeightedBound B m) ↔
      255 ≤ B := by
  constructor
  · intro h
    have hd : 0 ∈ BB6.Agent13BlankDelay.delays
        (BB6.Agent13BlankDelay.zeroNext BB6.Agent49.Box27Slice24.attainer) 0 := by decide
    have hb := h BB6.Agent49.Box27Slice24.attainer attainer_fits
      attainer_d0 attainer_d1 254 0 BB6.Agent49.Box27Slice24.attainer_halts hd
    omega
  · intro h m hm hd0 hd1 k d hk hd
    have hb := bound255 m hm hd0 hd1 k d hk hd
    omega

#print axioms bound255
#print axioms attainer_fits
#print axioms exact_weighted
end BB6.Agent49.Box27D17Parent
