import SheepFaninSource
import EvenEdge

namespace SheepFaninOriginal

open SheepBoostSourceModel

/-- Convert the source-formula edge into the unchanged published
    SheepEven.EvenEdge constructors, with exact first-even semantics. -/
theorem published_edge_to_source {a v y : Nat}
    (h : EvenGenericEdge a v y) :
    SheepEven.EvenEdge (2^a*v) y := by
  obtain ⟨ha,hvodd,hvmin,h,q,hqodd,hF,hy⟩ := h
  have hs : SheepEven.Step (2^a*v) (1+2^h*q) := by
    rw [←hF]
    exact SheepEven.Step.generic a v hvodd hvmin
  have hz5 : 5 ≤ 1+2^h*q := by
    have hp : 0 < 2^a := Nat.pow_pos (by decide)
    have hmul := Nat.mul_le_mul_right v (show 1 ≤ 2^a by omega)
    have hx : 5 ≤ 2^a*v := by omega
    dsimp [GenericF] at hF
    omega
  exact ⟨1+2^h*q,h,q,hs,hz5,hqodd,rfl,hy⟩

theorem a3_even_actual (s t q : Nat)
    (hq : 3^(16*t+10)*q+1=2^(2*9^s)) (hmin : 7≤q) :
    ∃ v, SheepEven.EvenEdge (8*v) (2^(2*9^s)) := by
  obtain ⟨v,hedge⟩ := SheepFaninSource.a3_even_edge s t q hq hmin
  exact ⟨v,by simpa only [show (2:Nat)^3=8 by decide] using
    published_edge_to_source hedge⟩

theorem a3_odd_actual (s t q : Nat)
    (hq : 3^(16*t+14)*q+1=2^(2*(3*9^s))) (hmin : 7≤q) :
    ∃ v, SheepEven.EvenEdge (8*v) (2^(2*(3*9^s))) := by
  obtain ⟨v,hedge⟩ := SheepFaninSource.a3_odd_edge s t q hq hmin
  exact ⟨v,by simpa only [show (2:Nat)^3=8 by decide] using
    published_edge_to_source hedge⟩

theorem a6_actual (m t q : Nat)
    (hq : 3^(21*t+20)*q+1=2^(2*3^(6*m))) (hmin : 7≤q) (hq3 : q%3=0) :
    ∃ v, SheepEven.EvenEdge (64*v) (2^(2*3^(6*m))) := by
  obtain ⟨v,hedge⟩ := SheepFaninSource.a6_edge m t q hq hmin hq3
  exact ⟨v,by simpa only [show (2:Nat)^6=64 by decide] using
    published_edge_to_source hedge⟩

theorem a7_even_actual (s t q : Nat)
    (hq : 3^(256*t+221)*q+1=2^(2*9^s)) (hmin : 7≤q) :
    ∃ v, SheepEven.EvenEdge (128*v) (2^(2*9^s)) := by
  obtain ⟨v,hedge⟩ := SheepFaninSource.a7_even_edge s t q hq hmin
  exact ⟨v,by simpa only [show (2:Nat)^7=128 by decide] using
    published_edge_to_source hedge⟩

theorem a7_odd_actual (s t q : Nat)
    (hq : 3^(256*t+83)*q+1=2^(2*(3*9^s))) (hmin : 7≤q) :
    ∃ v, SheepEven.EvenEdge (128*v) (2^(2*(3*9^s))) := by
  obtain ⟨v,hedge⟩ := SheepFaninSource.a7_odd_edge s t q hq hmin
  exact ⟨v,by simpa only [show (2:Nat)^7=128 by decide] using
    published_edge_to_source hedge⟩

#print axioms published_edge_to_source
#print axioms a3_even_actual
#print axioms a3_odd_actual
#print axioms a6_actual
#print axioms a7_even_actual
#print axioms a7_odd_actual
end SheepFaninOriginal
