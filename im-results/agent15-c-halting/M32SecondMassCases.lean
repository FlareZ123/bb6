import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace BB6.Agent15

/-- The eight original-source-certified M32 cells, replicated here solely
    as a finite arithmetic predicate for an independently audited pullback. -/
def m32Cylinder (x y : Nat) : Prop :=
    (x%32=27 ∧ y%32=28) ∨
    (x%32=19 ∧ y%32=16) ∨
    (x%32=3 ∧ y%32=20) ∨
    (x%32=11 ∧ y%32=0) ∨
    (x%32=3 ∧ y%32=16) ∨
    (x%32=11 ∧ y%32=12) ∨
    (x%32=19 ∧ y%32=4) ∨
    (x%32=27 ∧ y%32=0)

/-- The 32 explicit residue classes extending the old m%16=11
    second-family exclusion to ALL m≡3 mod4 index sectors. -/
def m32SecondMassClass (m r q : Nat) : Prop :=
  (m%16=3 ∧ (
    (r%4=0 ∧ (q%8=3 ∨ q%8=4)) ∨
    (r%4=1 ∧ (q%8=6 ∨ q%8=7)) ∨
    (r%4=2 ∧ (q%8=0 ∨ q%8=3)) ∨
    (r%4=3 ∧ (q%8=2 ∨ q%8=7)))) ∨
  (m%16=7 ∧ (
    (r%4=0 ∧ (q%8=2 ∨ q%8=7)) ∨
    (r%4=1 ∧ (q%8=3 ∨ q%8=4)) ∨
    (r%4=2 ∧ (q%8=6 ∨ q%8=7)) ∨
    (r%4=3 ∧ (q%8=0 ∨ q%8=3)))) ∨
  (m%16=11 ∧ (
    (r%4=0 ∧ (q%8=0 ∨ q%8=3)) ∨
    (r%4=1 ∧ (q%8=2 ∨ q%8=7)) ∨
    (r%4=2 ∧ (q%8=3 ∨ q%8=4)) ∨
    (r%4=3 ∧ (q%8=6 ∨ q%8=7)))) ∨
  (m%16=15 ∧ (
    (r%4=0 ∧ (q%8=6 ∨ q%8=7)) ∨
    (r%4=1 ∧ (q%8=0 ∨ q%8=3)) ∨
    (r%4=2 ∧ (q%8=2 ∨ q%8=7)) ∨
    (r%4=3 ∧ (q%8=3 ∨ q%8=4))))

/-- A finite 32-case modular certificate. Its only assumptions are
    exact source weighted-mass and depth/odd-part congruences. -/
theorem m32_mass_class_to_cells (mass m r q Q : Nat)
    (hMass : (mass+6*m+7)%32=0)
    (hQ : (Q+q+1)%8=0)
    (hclass : m32SecondMassClass m r q) :
    m32Cylinder ((mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32) ((4*Q)%32) := by
  unfold m32SecondMassClass at hclass
  rcases hclass with ⟨hm,hc⟩ | ⟨hm,hc⟩ | ⟨hm,hc⟩ | ⟨hm,hc⟩
  · rcases hc with ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=12 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=4 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=28 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=20 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
  · rcases hc with ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=20 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=12 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=4 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=28 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
  · rcases hc with ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=28 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=20 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=12 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=4 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
  · rcases hc with ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩ | ⟨hr,hq⟩
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=4 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=27 := by omega
        have hy : (4*Q)%32%32=28 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=19 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=20 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=0 := by omega
        unfold m32Cylinder
        omega
    · rcases hq with hq | hq
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=3 := by omega
        have hy : (4*Q)%32%32=16 := by omega
        unfold m32Cylinder
        omega
      · have hx : (mass+32*(2*r+1+Q+1)-4*(2*r+1)-8*Q)%32%32=11 := by omega
        have hy : (4*Q)%32%32=12 := by omega
        unfold m32Cylinder
        omega

#print axioms m32_mass_class_to_cells
end BB6.Agent15
