import Std

namespace FatalResidues

/-- A finite list of length m cannot inject into m-1 positive residues. -/
theorem positive_collision (m : Nat) (hm : 1 < m) (f : Nat → Nat)
    (hf : ∀ n, n < m → 0 < f n ∧ f n < m) :
    ∃ i j, i < j ∧ j < m ∧ f i = f j := by
  classical
  apply Classical.byContradiction
  intro h
  let xs := (List.range m).map (fun n => f n - 1)
  have hn : xs.Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map]
    apply (List.pairwise_iff_getElem).mpr
    intro i j hi hj hij
    simp only [List.getElem_range]
    have hfi := hf i (by simpa using hi)
    have hfj := hf j (by simpa using hj)
    intro he
    exact h ⟨i, j, hij, by simpa using hj, by omega⟩
  have hsub : xs ⊆ List.range (m-1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hh := hf i (List.mem_range.mp hi)
    exact List.mem_range.mpr (by omega)
  have hl := List.Nodup.length_le_of_subset hn hsub
  simp [xs] at hl
  omega

/-- Multiplication modulo m has a repeat with positive gap strictly below m. -/
theorem short_repeat (a b m : Nat) (hm : 1 < m) :
    ∃ i t, 0 < t ∧ t < m ∧ (a*b^(i+t))%m = (a*b^i)%m := by
  by_cases hz : ∃ n, (a*b^n)%m = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨i,1,by omega,hm,?_⟩
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod, hi]
    simp
  · obtain ⟨i,j,hij,hjm,he⟩ := positive_collision m hm (fun n => (a*b^n)%m) (by
      intro n hn
      have hp := Nat.mod_lt (a*b^n) (by omega : 0<m)
      have hne : (a*b^n)%m ≠ 0 := fun h => hz ⟨n,h⟩
      omega)
    refine ⟨i,j-i,by omega,by omega,?_⟩
    rw [show i+(j-i)=j by omega, he]

/-- A repeated modular power can be extended by any exponent increment. -/
theorem repeat_shift (a b m i t : Nat)
    (h : (a*b^(i+t))%m=(a*b^i)%m) (s : Nat) :
    (a*b^(i+s+t))%m=(a*b^(i+s))%m := by
  rw [show i+s+t=i+t+s by omega, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_mod, h]
  rw [Nat.pow_add, ← Nat.mul_assoc]
  simp

/-- Every positive modulus has a short eventual period in a modular exponential. -/
theorem repeat_multiple (a b m i t : Nat)
    (h : (a*b^(i+t))%m=(a*b^i)%m) (c : Nat) (hc : i ≤ c) (j : Nat) :
    (a*b^(c+t*j))%m=(a*b^c)%m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    have hs := repeat_shift a b m i t h (c+t*j-i)
    rw [show i+(c+t*j-i)=c+t*j by omega] at hs
    exact hs.trans ih


/-- Extended Euclidean identity without external libraries. -/
theorem bezout (m n : Nat) : ∃ u v : Int, (Nat.gcd m n : Int) = (m : Int)*u+(n : Int)*v := by
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      exact ⟨1, 0, by simp⟩
    · obtain ⟨u,v,he⟩ := ih (m%n) (Nat.mod_lt _ (by omega)) n
      refine ⟨v,u-(m/n : Nat)*v,?_⟩
      rw [Nat.gcd_comm m n, Nat.gcd_rec]
      have hmod : ((m%n : Nat) : Int) = (m : Int) - (n : Int)*(m/n : Nat) := by
        have h := congrArg (fun z : Nat => (z : Int)) (Nat.mod_add_div m n)
        simp only [Int.natCast_add, Int.natCast_mul] at h
        omega
      rw [hmod] at he
      grind


/-- Congruent natural residues imply integer divisibility of the difference. -/
theorem dvd_sub_of_mod_eq {x y m : Nat} (h : x%m=y%m) : (m : Int) ∣ (x : Int)-(y : Int) := by
  refine ⟨(x/m : Nat)-(y/m : Nat),?_⟩
  have hx := congrArg (fun z : Nat => (z : Int)) (Nat.mod_add_div x m)
  have hy := congrArg (fun z : Nat => (z : Int)) (Nat.mod_add_div y m)
  simp only [Int.natCast_add, Int.natCast_mul] at hx hy
  rw [h] at hx
  grind

/-- A signed exponential minus its exponent and a constant. -/
def gate (a b : Nat) (c : Int) (n : Nat) : Int := (a*b^n : Nat) - (n : Int) - c

/-- EVERY residue modulo EVERY positive modulus occurs arbitrarily late.
    No coprimality, factorization, or growth assumptions on a,b are needed. -/
theorem gate_dense (a b : Nat) (c : Int) (m : Nat) (hm : 0<m) (r : Int) (N : Nat) :
    ∃ n, N ≤ n ∧ (m : Int) ∣ gate a b c n-r := by
  induction m using Nat.strongRecOn generalizing r N with
  | ind m ih =>
    by_cases h1 : m=1
    · subst m
      exact ⟨N,Nat.le_refl _,by simp⟩
    · obtain ⟨i,t,ht,htm,hrep⟩ := short_repeat a b m (by omega)
      let d := Nat.gcd m t
      have hd : 0<d := Nat.gcd_pos_of_pos_left t hm
      have hdm : d<m := Nat.lt_of_le_of_lt (Nat.gcd_le_right m ht) htm
      obtain ⟨k,hk,w,hw⟩ := ih d hdm hd r (max N i)
      obtain ⟨u,v,hbez⟩ := bezout m t
      let z : Int := (v*w)%(m : Int)
      let j : Nat := z.toNat
      have hj : (j : Int)=z := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
      have hdiv : (m : Int) ∣ v*w-(j : Int) := by
        rw [hj]
        exact Int.dvd_self_sub_of_emod_eq rfl
      obtain ⟨q,hq⟩ := hdiv
      have hlin : (m : Int) ∣ gate a b c k-r-(t : Int)*(j : Int) := by
        refine ⟨u*w+(t : Int)*q,?_⟩
        change (Nat.gcd m t : Int) = _ at hbez
        change gate a b c k-r = (Nat.gcd m t : Int)*w at hw
        rw [hw,hbez]
        grind
      have hpow := dvd_sub_of_mod_eq (repeat_multiple a b m i t hrep k (by omega) j)
      refine ⟨k+t*j,by omega,?_⟩
      have hs := Int.dvd_add hlin hpow
      have he : gate a b c (k+t*j)-r = gate a b c k-r-(t : Int)*(j : Int) + ((a*b^(k+t*j) : Nat) : Int) - ((a*b^k : Nat) : Int) := by
        simp only [gate,Int.natCast_add,Int.natCast_mul]
        omega
      rw [he]
      simpa only [Int.add_sub_assoc] using hs

/-- Fatal height for the #746 reset map. -/
def fatal (n : Nat) : Nat := 4*2^n-n-4

theorem fatal_lower (n : Nat) : n+4 ≤ 4*2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

theorem fatal_cast (n : Nat) : (fatal n : Int) = gate 4 2 4 n := by
  unfold fatal gate
  have h := fatal_lower n
  rw [Int.natCast_sub (by omega), Int.natCast_sub (by omega)]
  rfl

theorem fatal_unbounded (n : Nat) : n ≤ fatal (n+1) := by
  have h := fatal_lower n
  unfold fatal
  rw [Nat.pow_succ, ← Nat.mul_assoc]
  omega

theorem fatal_dense (m : Nat) (hm : 0<m) (r N : Nat) :
    ∃ n, N ≤ n ∧ (fatal n)%m=r%m := by
  obtain ⟨n,hn,hd⟩ := gate_dense 4 2 4 m hm (r : Int) N
  rw [← fatal_cast] at hd
  have he := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)
  exact ⟨n,hn,by omega⟩

#print axioms gate_dense
#print axioms fatal_dense

/-- Finite-state iteration must repeat a state. A list enumeration avoids
    assuming a particular automaton representation or finiteness library. -/
theorem finite_repeat {S : Type} (xs : List S) (f : Nat → S)
    (hf : ∀ n, f n ∈ xs) : ∃ i t, 0<t ∧ f (i+t)=f i := by
  classical
  apply Classical.byContradiction
  intro h
  let ys := (List.range (xs.length+1)).map f
  have hn : ys.Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij he
    simp only [List.getElem_range] at he
    exact h ⟨i,j-i,by omega,by rw [show i+(j-i)=j by omega, he]⟩
  have hsub : ys ⊆ xs := by
    intro y hy
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp hy
    exact hf n
  have hl := List.Nodup.length_le_of_subset hn hsub
  simp [ys] at hl
  omega

theorem finite_repeat_shift {S : Type} (f : Nat → S) (next : S → S)
    (step : ∀ n, f (n+1)=next (f n)) (i t : Nat)
    (h : f (i+t)=f i) (s : Nat) : f (i+s+t)=f (i+s) := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
    rw [show i+(s+1)+t=i+s+t+1 by omega,step,show i+(s+1)=i+s+1 by omega,step,ih]

theorem finite_repeat_multiple {S : Type} (f : Nat → S) (next : S → S)
    (step : ∀ n, f (n+1)=next (f n)) (i t : Nat)
    (h : f (i+t)=f i) (k : Nat) (hk : i≤k) (j : Nat) : f (k+t*j)=f k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    have hs := finite_repeat_shift f next step i t h (k+t*j-i)
    rw [show i+(k+t*j-i)=k+t*j by omega] at hs
    exact hs.trans ih

/-- An unbounded finite-state accepted subset of the reset-height line
    cannot avoid the direct fatal heights. -/
theorem finite_state_hits_fatal {S : Type} (xs : List S) (f : Nat → S)
    (next : S → S) (accept : S → Prop) (hf : ∀ n, f n ∈ xs)
    (step : ∀ n, f (n+1)=next (f n))
    (unbounded : ∀ N, ∃ h, N≤h ∧ accept (f h)) : ∃ n, accept (f (fatal n)) := by
  obtain ⟨i,t,ht,he⟩ := finite_repeat xs f hf
  obtain ⟨h,hh,ha⟩ := unbounded i
  obtain ⟨n,hn,hr⟩ := fatal_dense t ht h (h+1)
  have hle : h≤fatal n := by
    have h' := fatal_unbounded (n-1)
    rw [show n-1+1=n by omega] at h'
    omega
  have hd := dvd_sub_of_mod_eq hr
  rw [← Int.natCast_sub hle,Int.ofNat_dvd] at hd
  obtain ⟨j,hj⟩ := hd
  have hF : fatal n=h+t*j := by omega
  exact ⟨n,by rwa [hF,finite_repeat_multiple f next step i t he h hh j]⟩

/-- General form: if every reachable-reset safety predicate must be unbounded
    and exclude direct fatal heights, no finite-state representation exists. -/
theorem no_finite_state_safety {S : Type} (xs : List S) (f : Nat → S)
    (next : S → S) (accept : S → Prop) (hf : ∀ n, f n ∈ xs)
    (step : ∀ n, f (n+1)=next (f n))
    (unbounded : ∀ N, ∃ h, N≤h ∧ accept (f h))
    (fatal_bad : ∀ n, ¬ accept (f (fatal n))) : False := by
  obtain ⟨n,hn⟩ := finite_state_hits_fatal xs f next accept hf step unbounded
  exact fatal_bad n hn

#print axioms finite_state_hits_fatal
#print axioms no_finite_state_safety

/-- Source-independent interface: total first-return semantics, strict growth,
    direct fatal heights, and an initial accepted reset suffice to refute
    every finite-state inductive safety predicate. -/
theorem no_finite_state_inductive {S : Type} (xs : List S) (f : Nat → S)
    (next : S → S) (accept : S → Prop) (hf : ∀ n, f n ∈ xs)
    (step : ∀ n, f (n+1)=next (f n))
    (R : Nat → Nat → Prop) (Halt : Nat → Prop)
    (total : ∀ h, Halt h ∨ ∃ u, R h u)
    (growth : ∀ h u, R h u → h<u)
    (fatal_halt : ∀ n, Halt (fatal n))
    (start : Nat) (root : accept (f start))
    (closed : ∀ h u, accept (f h) → R h u → accept (f u))
    (safe : ∀ h, accept (f h) → ¬ Halt h) : False := by
  have hu : ∀ N, ∃ h, N≤h ∧ accept (f h) := by
    intro N
    induction N with
    | zero => exact ⟨start, Nat.zero_le _, root⟩
    | succ N ih =>
      obtain ⟨h,hh,ha⟩ := ih
      rcases total h with hs | ⟨u,hu⟩
      · exact False.elim (safe h ha hs)
      · have hg := growth h u hu
        exact ⟨u,by omega,closed h u ha hu⟩
  exact no_finite_state_safety xs f next accept hf step hu
    (fun n ha => safe (fatal n) ha (fatal_halt n))

#print axioms no_finite_state_inductive
end FatalResidues
