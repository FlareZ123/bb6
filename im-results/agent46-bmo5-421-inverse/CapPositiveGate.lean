import CapForwardMacroReach

namespace CapSieve
open Bmo

def positiveCount (k q : Nat) : Nat := CapMacro.tripleCount (2*P k-2) q

def positiveProduct (k q : Nat) : Nat := 3^(positiveCount k q+1)*q

def positiveNext (k q : Nat) : Nat := positiveProduct k q+3-2*P k

theorem positive_product_spec {k q : Nat} (hq : 0<q) (hb : q≤2*P k-2) :
    let z := 3^(positiveCount k q)*q
    q≤z ∧ z≤2*P k-2 ∧ 2*P k-1≤positiveProduct k q ∧
    positiveProduct k q≤6*P k-6 ∧ positiveProduct k q=3*z := by
  dsimp
  have h := CapMacro.positive_window (p:=P k) hq hb
  change q≤3^(positiveCount k q)*q ∧ 3^(positiveCount k q)*q≤2*P k-2 ∧
    2*P k-1≤3*(3^(positiveCount k q)*q) ∧ 3*(3^(positiveCount k q)*q)≤6*P k-6 ∧ _ at h
  have he : positiveProduct k q=3*(3^(positiveCount k q)*q) := by
    unfold positiveProduct; rw [Nat.pow_succ]; ac_rfl
  rw [he]
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,rfl⟩

theorem positive_next_bounds {k q : Nat} (hq : 0<q) (hb : q≤2*P k-2) :
    2≤positiveNext k q ∧ positiveNext k q≤2*P (k+1)-2 := by
  have h := positive_product_spec hq hb
  unfold positiveNext
  rw [p_succ]
  have hp := p_ge k
  omega

theorem positive_next_equation {k q : Nat} (hq : 0<q) (hb : q≤2*P k-2) :
    positiveNext k q + 2*P k = positiveProduct k q+3 := by
  have h := positive_product_spec hq hb
  unfold positiveNext
  have hp := p_ge k
  omega

theorem positive_next_parity {k q : Nat} (hq : 0<q) (hb : q≤2*P k-2)
    (hp : q%2=k%2) : positiveNext k q%2=(k+1)%2 := by
  have he := positive_next_equation hq hb
  have hpow : ∀ n : Nat, 3^n%2=1 := by
    intro n; induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ,Nat.mul_mod,ih]
  have hpar : positiveProduct k q%2=q%2 := by
    unfold positiveProduct
    rw [Nat.mul_mod,hpow]; simp
  omega

/-- If the positive exit clears the next band's lower threshold, the full
    four-way macro takes exactly that regular one-band transition. -/
theorem positive_gate_pass {k q : Nat} (hq : 0<q) (hb : q≤2*P k-2)
    (hpass : k+7≤positiveNext k q) : bandMacro k q=some (k+1,positiveNext k q) := by
  obtain ⟨hlo,hhi,hUlo,hUhi,hU⟩ := positive_product_spec hq hb
  have he := positive_next_equation hq hb
  have hcross : 2*P k+k+2<positiveProduct k q := by omega
  have hpow : bandCount k q=positiveCount k q := by
    unfold bandCount
    apply CapMacro.triple_window_unique hq
    · exact CapMacro.tripleCount_spec hq (by omega)
    · exact ⟨by omega,hcross⟩
  have hz : bandLastQ k q=3^(positiveCount k q)*q := by unfold bandLastQ; rw [hpow]
  unfold bandMacro
  dsimp
  rw [hz]
  rw [if_neg (by omega : 3^(positiveCount k q)*q≠2*P k+k)]
  rw [if_neg (by omega : 3^(positiveCount k q)*q≠2*P k+k+2)]
  rw [←hU,if_pos (by omega : positiveProduct k q≤6*P k+k)]
  rfl

/-- Failure of the lower threshold is an authentic first negative-coordinate
    event inside the current band (including its terminal/special endpoints). -/
theorem positive_gate_fail {k x : Nat} (hx : Band k x)
    (hb : Q k x≤2*P k-2) (hfail : positiveNext k (Q k x)<k+7) :
    ∃ y, SameRun k (positiveCount k (Q k x)+1) x y ∧
      Q k y=positiveProduct k (Q k x) ∧ 2*P k-1≤Q k y := by
  have hqb := q_bounds hx
  have hq : 0<Q k x := by omega
  have h := positive_product_spec hq hb
  have he := positive_next_equation hq hb
  have hp : Q k x%2=k%2 := by unfold Q; omega
  have hn := positive_next_parity hq hb hp
  have hUhi : positiveProduct k (Q k x)≤2*P k+k+2 := by omega
  have hUlo : k+6≤positiveProduct k (Q k x) := by
    have hpos : 0<3^(positiveCount k (Q k x)+1) := Nat.pow_pos (by decide)
    have hm := Nat.le_mul_of_pos_left (Q k x) hpos
    change Q k x≤positiveProduct k (Q k x) at hm
    omega
  have hUpar : positiveProduct k (Q k x)%2=k%2 := by omega
  obtain ⟨y,hy,hyq⟩ := q_realize hUlo hUhi hUpar
  exact ⟨y,same_run_of_q hx hy hyq,hyq,by omega⟩

def positiveOrbit (k q : Nat) : Nat → Nat
  | 0 => q
  | n+1 => positiveNext (k+n) (positiveOrbit k q n)

theorem positive_orbit_shift (k q n : Nat) :
    positiveOrbit k q (n+1)=positiveOrbit (k+1) (positiveNext k q) n := by
  induction n with
  | zero => simp [positiveOrbit]
  | succ n ih =>
    change positiveNext (k+(n+1)) (positiveOrbit k q (n+1)) =
      positiveNext (k+1+n) (positiveOrbit (k+1) (positiveNext k q) n)
    rw [ih,show k+(n+1)=k+1+n by omega]

theorem positive_orbit_upper {k q : Nat} (hlo : 0<q) (hhi : q≤2*P k-2) :
    ∀ n, 0<positiveOrbit k q n ∧ positiveOrbit k q n≤2*P (k+n)-2 := by
  intro n; induction n with
  | zero => simpa [positiveOrbit] using And.intro hlo hhi
  | succ n ih =>
    have h := positive_next_bounds ih.1 ih.2
    simp only [positiveOrbit]
    rw [show k+(n+1)=k+n+1 by omega]
    omega

/-- An all-time lower-bound proof for the relaxed arithmetic orbit would
    establish the exact bounded graph test is false for every limit. -/
theorem positive_orbit_nohalt {limit k q : Nat} (hlo : k+6≤q) (hhi : q≤2*P k-2)
    (hall : ∀ n, k+n+6≤positiveOrbit k q n) : bandHaltBy limit k q=false := by
  rw [bandHaltBy]
  by_cases hkl : k>limit
  · rw [if_pos hkl]
  · rw [if_neg hkl]
    have hnext : k+7≤positiveNext k q := by simpa [positiveOrbit] using hall 1
    rw [positive_gate_pass (by omega) hhi hnext]
    change (if k<k+1 then bandHaltBy limit (k+1) (positiveNext k q) else false)=false
    rw [if_pos (by omega : k<k+1)]
    have hh := positive_next_bounds (by omega : 0<q) hhi
    apply positive_orbit_nohalt hnext hh.2
    intro n
    rw [←positive_orbit_shift]
    have h := hall (n+1)
    omega
termination_by limit+1-k
decreasing_by omega

/-- The concrete three all-time obligations imply their exact graph
    nonhalting assertions, with no assumption about other graph nodes. -/
theorem positive_root_two_nohalt
    (h : ∀ n, n+6≤positiveOrbit 0 6 n) : ¬∃ i, AReach 2 (T i) := by
  intro he
  obtain ⟨limit,hl⟩ := macro_root_two.mpr he
  have hh := positive_orbit_nohalt (limit:=limit) (k:=0) (q:=6) (by decide) (by unfold P; decide) (by simpa using h)
  simp [hh] at hl

theorem positive_root_three_nohalt
    (h : ∀ n, n+6≤positiveOrbit 0 8 n) : ¬∃ i, AReach 3 (T i) := by
  intro he
  obtain ⟨limit,hl⟩ := macro_root_three.mpr he
  have hh := positive_orbit_nohalt (limit:=limit) (k:=0) (q:=8) (by decide) (by unfold P; decide) (by simpa using h)
  simp [hh] at hl

theorem positive_root_one_nohalt
    (h : ∀ n, n+7≤positiveOrbit 1 15 n) : ¬∃ i, AReach 1 (T i) := by
  intro he
  obtain ⟨limit,hl⟩ := macro_root_one.mpr he
  have hh := positive_orbit_nohalt (limit:=limit) (k:=1) (q:=15) (by decide) (by unfold P; decide) (by intro n; have := h n; omega)
  have hmacro : bandMacro 0 12=some (1,15) := by
    simp [bandMacro,bandLastQ,bandCount,P,CapMacro.tripleCount]
  rw [bandHaltBy,if_neg (by omega : ¬0>limit),hmacro] at hl
  simp [hh] at hl

#print axioms positive_gate_pass
#print axioms positive_gate_fail
#print axioms positive_orbit_nohalt
#print axioms positive_root_two_nohalt
#print axioms positive_root_three_nohalt
#print axioms positive_root_one_nohalt
end CapSieve
