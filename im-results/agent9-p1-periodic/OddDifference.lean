import Std

namespace BB6.Agent9CrossFeeder

/-- Elementary pigeonhole over a finite interval, with explicit indices. -/
theorem bounded_nat_repeat (B : Nat) (f : Nat → Nat)
    (hb : ∀ n, f n ≤ B) :
    ∃ i j : Nat, i < j ∧ j ≤ B+1 ∧ f i = f j := by
  by_cases hnone : ∃ i j : Nat, i < j ∧ j ≤ B+1 ∧ f i = f j
  · exact hnone
  · exfalso
    let xs : List Nat := List.ofFn (fun i : Fin (B+2) => f i)
    have hnodup : xs.Nodup := by
      apply List.nodup_iff_eq_of_getElem_eq.mpr
      intro i j hi hj heq
      have hi' : i < B+2 := by simpa [xs] using hi
      have hj' : j < B+2 := by simpa [xs] using hj
      have hiElem : xs[i] = f i := by
        change (List.ofFn (fun k : Fin (B+2) => f k))[i] = f i
        rw [List.getElem_ofFn]
      have hjElem : xs[j] = f j := by
        change (List.ofFn (fun k : Fin (B+2) => f k))[j] = f j
        rw [List.getElem_ofFn]
      have hfeq : f i = f j := by
        rw [hiElem,hjElem] at heq
        exact heq
      by_cases hneq : i = j
      · exact hneq
      · exfalso
        rcases Nat.lt_or_gt_of_ne hneq with hlt | hgt
        · exact hnone ⟨i,j,hlt,by omega,hfeq⟩
        · exact hnone ⟨j,i,hgt,by omega,hfeq.symm⟩
    have hsub : xs ⊆ List.range (B+1) := by
      intro x hx
      rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
      exact List.mem_range.mpr (by have := hb i; omega)
    have hlen := hnodup.length_le_of_subset hsub
    have hh : xs.length = B+2 := List.length_ofFn
    simp [hh] at hlen

/-- A uniformly bounded integer sequence repeats within a computable prefix. -/
theorem bounded_int_repeat (M : Nat) (D : Nat → Int)
    (hb : ∀ n, -(M:Int) ≤ D n ∧ D n ≤ (M:Int)) :
    ∃ i j : Nat, i < j ∧ j ≤ 2*M+1 ∧ D i = D j := by
  let f : Nat → Nat := fun n => (D n + (M:Int)).toNat
  have hf : ∀ n, f n ≤ 2*M := by
    intro n
    apply Int.toNat_le.mpr
    dsimp [f]
    have h := hb n
    omega
  obtain ⟨i,j,hij,hj,heq⟩ := bounded_nat_repeat (2*M) f hf
  refine ⟨i,j,hij,by omega,?_⟩
  have hnonnegI : 0 ≤ D i + (M:Int) := by have h:=hb i; omega
  have hnonnegJ : 0 ≤ D j + (M:Int) := by have h:=hb j; omega
  have heqInt := congrArg (fun x : Nat => (x:Int)) heq
  dsimp [f] at heqInt
  rw [Int.toNat_of_nonneg hnonnegI,Int.toNat_of_nonneg hnonnegJ] at heqInt
  omega

/-- A scaled integer with multiplier at least one has at least the original
magnitude, expressed without an absolute-value library dependency. -/
theorem scaled_integer_bound (P M K : Int) (hp : 1 ≤ P)
    (hl : -M ≤ P*K) (hu : P*K ≤ M) : -M ≤ K ∧ K ≤ M := by
  have hpid : P*K-K=(P-1)*K := by
    rw [Int.sub_mul]; simp
  by_cases hk : 0 ≤ K
  · have hpone : 0 ≤ P-1 := by omega
    have hnonneg := Int.mul_nonneg hpone hk
    omega
  · have hk' : K ≤ 0 := by omega
    have hpos : 0 ≤ -K := by omega
    have hpone : 0 ≤ P-1 := by omega
    have hnonneg := Int.mul_nonneg hpone hpos
    have hneg : (P-1)*K ≤ 0 := by
      have hdist : (P-1)*(-K)= -((P-1)*K) := by simp [Int.mul_neg]
      omega
    omega

/-- The odd-difference shadow edge remains in a fixed finite integer interval. -/
theorem odd_difference_bound_step (M : Nat) (B D D' : Int) (t : Nat)
    (hB : -(M:Int) ≤ B ∧ B ≤ (M:Int))
    (hD : -(M:Int) ≤ D ∧ D ≤ (M:Int))
    (hstep : D=(2:Int)^t*(2*D'-B)) :
    -(M:Int) ≤ D' ∧ D' ≤ (M:Int) := by
  let P : Int := (2:Int)^t
  have hp : 1 ≤ P := by
    have hpow : 0 < (2:Int)^t := Int.pow_pos (by decide)
    omega
  have hK := scaled_integer_bound P (M:Int) (2*D'-B) hp
    (by simpa [P,hstep] using hD.1) (by simpa [P,hstep] using hD.2)
  omega

/-- Iterated boundedness for arbitrary depth streams. -/
theorem odd_difference_bound_all (M : Nat) (B : Int) (D : Nat → Int)
    (t : Nat → Nat)
    (hB : -(M:Int) ≤ B ∧ B ≤ (M:Int))
    (hD0 : -(M:Int) ≤ D 0 ∧ D 0 ≤ (M:Int))
    (hstep : ∀ n, D n=(2:Int)^(t n)*(2*D (n+1)-B)) :
    ∀ n, -(M:Int) ≤ D n ∧ D n ≤ (M:Int) := by
  intro n
  induction n with
  | zero => exact hD0
  | succ n ih => exact odd_difference_bound_step M B (D n) (D (n+1)) (t n) hB ih (hstep n)

/-- In an odd-parameter affine difference edge the dyadic depth is unique. -/
theorem odd_scaled_power_unique (B D a b : Int) (t s : Nat)
    (hB : B % 2 = 1)
    (ht : D = (2:Int)^t*(2*a-B))
    (hs : D = (2:Int)^s*(2*b-B)) : t=s := by
  have hodd : ∀ y : Int, ¬(2:Int) ∣ (2*y-B) := by
    intro y hy
    have hd : (2*y-B) % 2 = 0 := Int.emod_eq_zero_of_dvd hy
    omega
  have hkey : ∀ (x y : Int) (i j : Nat), i<j →
      D = (2:Int)^i*(2*x-B) →
      D = (2:Int)^j*(2*y-B) → False := by
    intro x y i j hij hi hj
    have hidx : j = i+1+(j-i-1) := by omega
    rw [hidx, Int.pow_add, Int.pow_succ] at hj
    have hfact : (2:Int)^i*(2*x-B) =
        (2:Int)^i*(2*((2:Int)^(j-i-1)*(2*y-B))) := by
      calc
        _ = D := hi.symm
        _ = (2:Int)^i*2*((2:Int)^(j-i-1)*(2*y-B)) := by
          rw [hj]; ac_rfl
        _ = _ := by ac_rfl
    have hcoeff : 2*x-B = 2*((2:Int)^(j-i-1)*(2*y-B)) :=
      Int.eq_of_mul_eq_mul_left (Int.pow_ne_zero (by decide : (2:Int)≠0)) hfact
    apply hodd x
    exact ⟨(2:Int)^(j-i-1)*(2*y-B), hcoeff⟩
  by_cases heq : t=s
  · exact heq
  rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
  · exact False.elim (hkey a b t s hlt ht hs)
  · exact False.elim (hkey b a s t hgt hs ht)

/-- When the source-level L-offset difference is odd, a common current
integer shadow difference fixes both the next depth and the next difference. -/
theorem odd_difference_deterministic (B D a b : Int) (t s : Nat)
    (hB : B%2=1)
    (ht : D=(2:Int)^t*(2*a-B))
    (hs : D=(2:Int)^s*(2*b-B)) : t=s ∧ a=b := by
  have he : t=s := odd_scaled_power_unique B D a b t s hB ht hs
  subst s
  have hp : (2:Int)^t ≠0 := Int.pow_ne_zero (by decide)
  have hfac : (2:Int)^t*(2*a-B)=(2:Int)^t*(2*b-B) := by
    rw [←ht,←hs]
  have hh : 2*a-B=2*b-B := Int.eq_of_mul_eq_mul_left hp hfac
  constructor
  · rfl
  · omega

/-- Once an odd-offset shared-depth integer difference repeats, all future
integer differences and depths repeat with the same lag. -/
theorem odd_difference_repeat_tail (B : Int) (D : Nat → Int)
    (t : Nat → Nat) (hB : B%2=1)
    (hstep : ∀ n, D n=(2:Int)^(t n)*(2*D (n+1)-B))
    (i j : Nat) (heq : D i=D j) :
    ∀ n, D (i+n)=D (j+n) ∧ t (i+n)=t (j+n) := by
  have hvalues : ∀ n, D (i+n)=D (j+n) := by
    intro n
    induction n with
    | zero => simpa using heq
    | succ n ih =>
        have hi := hstep (i+n)
        have hj := hstep (j+n)
        rw [ih] at hi
        have hdet := odd_difference_deterministic B (D (j+n))
          (D (i+n+1)) (D (j+n+1))
          (t (i+n)) (t (j+n)) hB hi hj
        simpa [Nat.add_assoc] using hdet.2
  intro n
  have hi := hstep (i+n)
  have hj := hstep (j+n)
  rw [hvalues n] at hi
  have hdet := odd_difference_deterministic B (D (j+n))
    (D (i+n+1)) (D (j+n+1))
    (t (i+n)) (t (j+n)) hB hi hj
  exact ⟨hvalues n,hdet.1⟩

/-- Finite-state deterministic shared-depth streams have an explicit
nonempty eventual period. No appeal to periodicity is assumed. -/
theorem odd_difference_has_period (M : Nat) (B : Int)
    (D : Nat → Int) (t : Nat → Nat)
    (hB : B%2=1)
    (hBoundB : -(M:Int) ≤ B ∧ B ≤ (M:Int))
    (hBound0 : -(M:Int) ≤ D 0 ∧ D 0 ≤ (M:Int))
    (hstep : ∀ n, D n=(2:Int)^(t n)*(2*D (n+1)-B)) :
    ∃ (N d : Nat) (w : List Nat), 0<d ∧ w.length=d ∧
      ∀ (n k : Nat) (hk : k<w.length),
        t (N+n*d+k) = w.get ⟨k,hk⟩ := by
  have hall := odd_difference_bound_all M B D t hBoundB hBound0 hstep
  obtain ⟨i,j,hij,hj,heq⟩ := bounded_int_repeat M D hall
  let d := j-i
  have hd : 0<d := by dsimp [d]; omega
  have hjid : j=i+d := by dsimp [d]; omega
  let w : List Nat := List.ofFn (fun k : Fin d => t (i+k))
  have hwlen : w.length=d := List.length_ofFn
  have hshift : ∀ k, t (i+k)=t (i+d+k) := by
    intro k
    have h := (odd_difference_repeat_tail B D t hB hstep i j heq k).2
    rwa [hjid] at h
  have hblocks : ∀ n k, t (i+n*d+k)=t (i+k) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
        intro k
        have hs := hshift (n*d+k)
        have hEq : i+(n+1)*d+k = i+d+(n*d+k) := by
          simp [Nat.succ_mul]; omega
        rw [hEq]
        calc
          t (i+d+(n*d+k)) = t (i+(n*d+k)) := hs.symm
          _ = t (i+k) := by simpa [Nat.add_assoc] using ih k
  refine ⟨i,d,w,hd,hwlen,?_⟩
  intro n k hk
  have hget : w.get ⟨k,hk⟩=t (i+k) := by
    change (List.ofFn (fun j : Fin d => t (i+j)))[k] = t (i+k)
    rw [List.getElem_ofFn]
  rw [hget]
  exact hblocks n k

#print axioms bounded_nat_repeat
#print axioms bounded_int_repeat
#print axioms odd_difference_bound_all
#print axioms odd_difference_deterministic
#print axioms odd_difference_has_period

end BB6.Agent9CrossFeeder
