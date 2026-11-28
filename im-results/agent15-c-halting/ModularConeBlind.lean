import ModularCone
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent15Research
open BB6.Agent42ModularCone

/-- A residue 2 modulo 4 has truncated two-adic valuation exactly one. -/
theorem valuation_mod4_two (b : Nat) (z : Int) (hb : 2 ≤ b) (hz : z % 4 = 2) :
    valuation b z = 1 := by
  obtain ⟨n,rfl⟩ : ∃ n, b = n+2 := ⟨b-2, by omega⟩
  have he : z % 2 = 0 := by omega
  have ho : (z / 2) % 2 = 1 := by omega
  simp [valuation, he, ho]

theorem I_ge4 (b : Nat) (hb : 2 ≤ b) : (4:Int) ≤ I b := by
  have h : 4 ≤ P b := by
    unfold P
    exact Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hb
  unfold I
  omega

theorem I_mod4_zero (b : Nat) (hb : 2 ≤ b) : I b % 4 = 0 := by
  obtain ⟨n,rfl⟩ : ∃ n, b = n+2 := ⟨b-2, by omega⟩
  simp [I, P, Nat.pow_add]

theorem I_mod2_zero (b : Nat) (hb : 1 ≤ b) : I b % 2 = 0 := by
  obtain ⟨n,rfl⟩ : ∃ n, b = n+1 := ⟨b-1, by omega⟩
  simp [I, P, Nat.pow_add]

/-- The canonical residue of -2 at any precision at least two. -/
theorem negTwo_mod_I (b : Nat) (hb : 2 ≤ b) : (-2 : Int) % I b = I b - 2 := by
  have hI := I_ge4 b hb
  have hc : Cong b (-2) (I b-2) := by
    unfold Cong
    refine ⟨(-1:Int),?_⟩
    omega
  have hm := cong_mod hc
  have hr : (I b-2)%I b=I b-2 := Int.emod_eq_of_lt (by omega) (by omega)
  rw [hr] at hm
  exact hm

/-- Canonical representatives of the modular-cone direct-chain blind cylinder. -/
def Blind (b : Nat) (s : Pair) : Prop := s.x % 4 = 3 ∧ s.y = I b - 2

theorem blind_y_even {b : Nat} {s : Pair} (hb : 2≤b) (hs : Blind b s) : s.y % 2 = 0 := by
  have hI2 := I_mod2_zero b (by omega)
  rcases hs with ⟨hx,hy⟩
  rw [hy]
  omega

theorem blind_y_mod4 {b : Nat} {s : Pair} (hb : 2≤b) (hs : Blind b s) : s.y % 4 = 2 := by
  have hI4 := I_mod4_zero b hb
  rcases hs with ⟨hx,hy⟩
  rw [hy]
  omega

theorem blind_sum_odd {b : Nat} {s : Pair} (hb : 2≤b) (hs : Blind b s) : (s.x+s.y)%2=1 := by
  have hy := blind_y_even hb hs
  have hx := hs.1
  omega

theorem blind_q_mod4 {b : Nat} {s : Pair} (hb : 2≤b) (hs : Blind b s) : q s % 4 = 2 := by
  have hy4 := blind_y_mod4 hb hs
  have hx4 := hs.1
  have ho := blind_sum_odd hb hs
  unfold q odd
  rw [show (s.x+s.y)%2=1 from ho]
  omega

theorem blind_not_bad {b : Nat} {s : Pair} (hb : 2≤b) (hs : Blind b s) : ¬ Bad s := by
  intro h
  unfold Bad at h
  have hy := blind_y_even hb hs
  omega

theorem blind_val {b : Nat} {s : Pair} (hb : 2≤b) (hs : Blind b s) : valuation b (q s) = 1 :=
  valuation_mod4_two b (q s) hb (blind_q_mod4 hb hs)

theorem blind_valvalid {b : Nat} {s : Pair} (hb : 2≤b) (hs : Blind b s) :
    ValValid b s 1 := by
  constructor
  · omega
  · have hq := blind_q_mod4 hb hs
    simpa [I,P] using hq

theorem four_dvd_I (b : Nat) (hb : 2≤b) : (4:Int) ∣ I b := by
  obtain ⟨n,rfl⟩ : ∃ n, b=n+2 := ⟨b-2,by omega⟩
  refine ⟨((2^n:Nat):Int),?_⟩
  simp [I,P,Nat.pow_add]
  ac_rfl

theorem I_succ (b : Nat) : I (b+1) = 2*I b := by
  simp [I,P,Nat.pow_succ]
  ac_rfl

theorem blind_direct_step (n : Nat) (s : Pair) (hs : Blind (n+3) s) :
    Blind (n+2) (residue (n+2) (direct s)) := by
  have hb3 : 2≤n+3 := by omega
  have hb2 : 2≤n+2 := by omega
  have hy4 := blind_y_mod4 hb3 hs
  have hI : I (n+3)=2*I (n+2) := by
    have h := I_succ (n+2)
    rw [show n+2+1=n+3 by omega] at h
    exact h
  have hIge := I_ge4 (n+2) hb2
  have hdiv := four_dvd_I (n+2) hb2
  constructor
  · change ((s.x+s.y-2) % I (n+2)) % 4 = 3
    rw [Int.emod_emod_of_dvd (s.x+s.y-2) hdiv]
    have hx := hs.1
    omega
  · change ((s.y-2)/2) % I (n+2) = I (n+2)-2
    have hy := hs.2
    have hhalf : (s.y-2)/2 = I (n+2)-2 := by
      rw [hy,hI]
      omega
    rw [hhalf]
    apply Int.emod_eq_of_lt
    · omega
    · omega

/-- The checker deterministically follows direct parents down to precision one,
    where it rejects the cylinder rather than certifying exclusion. -/
theorem blind_check_false (n : Nat) (s : Pair) (hs : Blind (n+2) s) :
    check (n+2) (n+2) s = false := by
  induction n generalizing s with
  | zero =>
      have hb : 2≤0+2 := by omega
      have hbad := blind_not_bad hb hs
      have hval := blind_val hb hs
      have hvv := blind_valvalid hb hs
      have hy := blind_y_even hb hs
      rw [check]
      simp [hbad, hval, hvv, hy, Allowed]
      rw [check]
      simp
  | succ n ih =>
      have hb : 2≤n+1+2 := by omega
      have hbad := blind_not_bad hb hs
      have hval := blind_val hb hs
      have hvv := blind_valvalid hb hs
      have hy := blind_y_even hb hs
      have hchild : Blind (n+2) (residue (n+2) (direct s)) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using blind_direct_step n s hs
      have hrec := ih (residue (n+2) (direct s)) hchild
      rw [check]
      simp [hbad, hval, hvv, hy, Allowed, hrec]

/-- Every residue cylinder whose canonical representative has x=3 mod 4 and
    y=2^b-2 is invisible to the executable modular exclusion checker. -/
theorem blind_excluded_false (b : Nat) (s : Pair) (hb : 2≤b) (hs : Blind b (residue b s)) :
    excluded b s = false := by
  obtain ⟨n,rfl⟩ : ∃n,b=n+2 := ⟨b-2,by omega⟩
  exact blind_check_false n (residue (n+2) s) hs

/-- Congruence-form interface to the blind cylinder. -/
theorem blind_of_congruences (b : Nat) (s : Pair) (hb : 2≤b)
    (hx : s.x%4=3) (hy : Cong b s.y (-2)) : Blind b (residue b s) := by
  have h4 := four_dvd_I b hb
  constructor
  · change (s.x%I b)%4=3
    rw [Int.emod_emod_of_dvd _ h4]
    exact hx
  · change s.y%I b=I b-2
    have hm := cong_mod hy
    rw [hm, negTwo_mod_I b hb]

/-- Any state congruent to the blind cylinder is accepted as unresolved by
    the executable modular exclusion checker. -/
theorem excluded_false_of_congruences (b : Nat) (s : Pair) (hb : 2≤b)
    (hx : s.x%4=3) (hy : Cong b s.y (-2)) : excluded b s=false :=
  blind_excluded_false b s hb (blind_of_congruences b s hb hx hy)

#print axioms excluded_false_of_congruences
#print axioms blind_check_false
#print axioms blind_excluded_false

end BB6.Agent15Research
