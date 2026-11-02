import Std

namespace SheepBridge

abbrev State := Nat × Nat

/-- Copied verbatim (up to pair notation) from the published certified counter accelerator. -/
def nextA : State → Option State
  | (0, 0) => some (0, 2)
  | (0, k + 1) => some (2, k)
  | (1, _) => none
  | (m + 2, k) =>
      if m % 2 = 0 then
        some (3 * (m / 2) + k + 3, 1)
      else
        some (m / 2, m / 2 + k + 4)

inductive Steps : State → State → Prop where
  | refl (s : State) : Steps s s
  | cons {x y z : State} : nextA x = some y → Steps y z → Steps x z

theorem Steps.trans {x y z : State} (h : Steps x y) (h2 : Steps y z) : Steps x z := by
  induction h with
  | refl _ => exact h2
  | @cons x mid y hstep hrest ih => exact Steps.cons hstep (ih h2)

private theorem odd_drop (m k : Nat) :
    nextA (2*m+3,k) = some (m,m+k+4) := by
  have hm : 2*m+3 = (2*m+1)+2 := by omega
  rw [hm]
  have ho : (2*m+1)%2=1 := by omega
  have hd : (2*m+1)/2=m := by omega
  simp only [nextA, ho, hd]
  simp

private theorem half_one (n k : Nat) (hn : 3 ≤ n) :
    nextA (2*n-3,k) = some (n-3,n+k+1) := by
  have he : 2*n-3=2*(n-3)+3 := by omega
  rw [he, odd_drop]
  have he2 : n+k+1 = n-3+k+4 := by omega
  rw [he2]

private theorem pow_two_step (a : Nat) : 2^(a+1) = 2*2^a := by
  rw [Nat.pow_succ]
  omega

/-- Every even-stripping run is a sequence of genuine published counter transitions. -/
theorem halve_iter (a u k : Nat) (hu : 3 ≤ u) :
    Steps (2^a*u-3,k) (u-3,k+(2^a-1)*u+a) := by
  induction a generalizing k with
  | zero =>
      simpa using (Steps.refl (u-3,k))
  | succ a ih =>
      have hpos : 0 < 2^a := Nat.pow_pos (by decide)
      have hn : 3 ≤ 2^a*u := by
        have hh := Nat.mul_le_mul_right u (Nat.one_le_iff_ne_zero.mpr (by omega : 2^a ≠ 0))
        omega
      have hp : 2^(a+1) = 2*2^a := pow_two_step a
      have hinput : 2^(a+1)*u-3 = 2*(2^a*u)-3 := by
        rw [hp, Nat.mul_assoc]
      have hd : nextA (2^(a+1)*u-3,k) = some (2^a*u-3,2^a*u+k+1) := by
        rw [hinput]
        exact half_one (2^a*u) k hn
      have hr := ih (2^a*u+k+1)
      have hmul : (2^(a+1)-1)*u = 2^a*u + (2^a-1)*u := by
        rw [hp]
        have he : 2*2^a-1 = 2^a+(2^a-1) := by omega
        rw [he,Nat.add_mul]
      have hs : (2^a*u+k+1)+(2^a-1)*u+a = k+(2^(a+1)-1)*u+(a+1) := by
        rw [hmul]
        omega
      rw [←hs]
      exact Steps.cons hd hr


private theorem even_gain (r k : Nat) :
    nextA (2*r+2,k) = some (3*r+k+3,1) := by
  have he : (2*r+2)=(2*r)+2 := by omega
  rw [he]
  have hmod : (2*r)%2=0 := by omega
  have hdiv : (2*r)/2=r := by omega
  simp [nextA,hmod,hdiv]

private theorem power_minus_one (a u : Nat) :
    (2^a-1)*u + u = 2^a*u := by
  have hp : 1 ≤ 2^a := Nat.one_le_iff_ne_zero.mpr
    (by have hh:0<2^a:=Nat.pow_pos (by decide); omega)
  have he : (2^a-1)+1=2^a := by omega
  calc
    (2^a-1)*u+u = ((2^a-1)+1)*u := by simp [Nat.add_mul]
    _ = 2^a*u := by rw [he]

/-- Every general nonhalting section edge can be expanded to counter steps. -/
theorem general_section (a u : Nat) (hu : 5 ≤ u) (hodd : u%2=1) :
    Steps (2^a*u-3,1)
      (2^a*u+a+(u-1)/2-3,1) := by
  obtain ⟨r,rfl⟩ : ∃ r, u=2*r+5 := ⟨(u-5)/2,by omega⟩
  let u := 2*r+5
  let k := 1+(2^a-1)*u+a
  have first : Steps (2^a*u-3,1) (u-3,k) := by
    simpa [k] using (halve_iter a u 1 (by dsimp [u]; omega))
  have even : u-3=2*r+2 := by dsimp [u]; omega
  have second : nextA (u-3,k) = some (3*r+k+3,1) := by
    rw [even]
    exact even_gain r k
  have hsum := power_minus_one a u
  have hhalf : (u-1)/2 = r+2 := by dsimp [u]; omega
  have hfinal : 3*r+k+3 = 2^a*u+a+(u-1)/2-3 := by
    dsimp [k,u] at *
    omega
  rw [←hfinal]
  exact Steps.trans first (Steps.cons second (Steps.refl _))

/-- Each exceptional odd part 3 edge is also a genuine finite counter path. -/
theorem triple_section (a : Nat) :
    Steps (3*2^a-3,1) (3*2^a+a,1) := by
  let k := 1+(2^a-1)*3+a
  have first : Steps (2^a*3-3,1) (0,k) := by
    simpa [k, Nat.mul_comm] using (halve_iter a 3 1 (by omega))
  have hpos : 1 ≤ k := by dsimp [k]; omega
  obtain ⟨b,hb⟩ : ∃ b,k=b+1 := ⟨k-1,by omega⟩
  have next0 : nextA (0,k)=some (2,k-1) := by
    rw [hb]
    simp [nextA]
  have next2 : nextA (2,k-1)=some (k+2,1) := by
    simp [nextA]
    omega
  have hsum := power_minus_one a 3
  have hfinal : k+2=3*2^a+a := by dsimp [k]; omega
  have hw := Steps.cons next0 (Steps.cons next2 (Steps.refl (k+2,1)))
  rw [hfinal] at hw
  simpa [Nat.mul_comm] using (Steps.trans first hw)


/-- Exactly the same one-variable return-edge graph used by Agent 14's preimage proofs. -/
inductive SectionNext : Nat → Nat → Prop where
  | triple (a : Nat) : SectionNext (3*2^a) (3*2^a+a+3)
  | general (a u : Nat) (hu : 5 ≤ u) (hodd : u%2=1) :
      SectionNext (2^a*u) (2^a*u+a+(u-1)/2)

/-- Kernel-checked forward simulation of EVERY published one-variable return edge
    by a finite sequence in the independently copied two-counter accelerator. -/
theorem section_edge_counter_sound {t v : Nat} (h : SectionNext t v) :
    Steps (t-3,1) (v-3,1) := by
  cases h with
  | triple a =>
      simpa [Nat.add_sub_assoc] using (triple_section a)
  | general a u hu hodd =>
      exact general_section a u hu hodd

#print axioms SheepBridge.halve_iter
#print axioms SheepBridge.general_section
#print axioms SheepBridge.triple_section
#print axioms SheepBridge.section_edge_counter_sound

end SheepBridge
