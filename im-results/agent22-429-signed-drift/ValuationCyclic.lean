import ValuationPrimitive

namespace ValuationPacking

private theorem periodic_nat_mul (N : Int) (f : Int → Nat)
    (hperiod : ∀ i : Int, f (i+N) = f i)
    (x : Int) : ∀ k : Nat, f (x+(k:Int)*N) = f x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hh : x+((k+1:Nat):Int)*N = (x+(k:Int)*N)+N := by
      have hcast : ((k+1:Nat):Int) = (k:Int)+1 := by omega
      rw [hcast, Int.add_mul]
      omega
    rw [hh,hperiod,ih]

private theorem periodic_nat_sub (N : Int) (f : Int → Nat)
    (hperiod : ∀ i : Int, f (i+N) = f i)
    (x : Int) : ∀ k : Nat, f (x-(k:Int)*N) = f x := by
  have hback : ∀ y : Int, f (y-N) = f y := by
    intro y
    have hp := hperiod (y-N)
    have heq : y-N+N=y := by omega
    rw [heq] at hp
    exact hp.symm
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hh : x-((k+1:Nat):Int)*N = (x-(k:Int)*N)-N := by
      have hcast : ((k+1:Nat):Int) = (k:Int)+1 := by omega
      rw [hcast, Int.add_mul]
      omega
    rw [hh,hback,ih]

private theorem periodic_int_mul (N : Int) (f : Int → Nat)
    (hperiod : ∀ i : Int, f (i+N) = f i)
    (x q : Int) : f (x+q*N) = f x := by
  cases q with
  | ofNat k => exact periodic_nat_mul N f hperiod x k
  | negSucc k =>
      have hh : x+(Int.negSucc k)*N = x-((k+1:Nat):Int)*N := by
        rw [Int.negSucc_eq]
        have hcast : (k:Int)+1 = ((k+1:Nat):Int) := by omega
        rw [hcast, Int.neg_mul]
        omega
      rw [hh]
      exact periodic_nat_sub N f hperiod x (k+1)

theorem periodic_past_constant (n : Nat) (f : Int → Nat)
    (hn : 0 < n)
    (hper : ∀ i : Int, f (i+(n:Int))=f i)
    (a : Int) (c : Nat)
    (hall : ∀ k : Nat, 0 < k → f (a-(k:Int))=c) :
    ∀ i : Int, f i=c := by
  intro i
  let N : Int := (n:Int)
  let w : Int := a-1-i
  let rem : Int := w%N
  let q : Int := w/N
  have hNpos : 0 < N := by dsimp [N]; omega
  have hr0 : 0 ≤ rem := Int.emod_nonneg w (by omega : N ≠ 0)
  have hrlt : rem < N := Int.emod_lt_of_pos w hNpos
  let k : Nat := rem.toNat+1
  have hkpos : 0 < k := by dsimp [k]; omega
  have hcast : (rem.toNat:Int)=rem := Int.toNat_of_nonneg hr0
  have hdiv : w=rem+q*N := by
    have he := Int.emod_def w N
    have hc := Int.mul_comm N (w/N)
    dsimp [rem,q] at *
    omega
  have ha : a-(k:Int)=i+q*N := by
    dsimp [k,w] at *
    omega
  have hv := hall k hkpos
  rw [ha] at hv
  have hp := periodic_int_mul N f hper i q
  rw [hp] at hv
  exact hv

def MinimalPeriod (n : Nat) (j : Int → Nat) : Prop :=
  ∀ d : Nat, 0 < d → d < n →
    ∃ i : Int, j (i+(d:Int)) ≠ j i

theorem minimal_period_backward_primitive (n : Nat) (j : Int → Nat)
    (hn : 0 < n)
    (hper : ∀ i : Int, j (i+(n:Int)) = j i)
    (hmin : MinimalPeriod n j) : BackwardPrimitive n j := by
  intro a b hab hbn
  let d : Nat := b-a
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdlt : d < n := by dsimp [d]; omega
  obtain ⟨i,hneq⟩ := hmin d hdpos hdlt
  let N : Int := (n:Int)
  let w : Int := ((a:Int)-1-i)
  let rem : Int := w%N
  let q : Int := w/N
  have hNpos : 0 < N := by dsimp [N]; omega
  have hNne : N ≠ 0 := by omega
  have hr0 : 0 ≤ rem := by
    dsimp [rem]
    exact Int.emod_nonneg w hNne
  have hrlt : rem < N := by
    dsimp [rem]
    exact Int.emod_lt_of_pos w hNpos
  let k : Nat := rem.toNat+1
  have hcast : (rem.toNat:Int)=rem := Int.toNat_of_nonneg hr0
  have hkpos : 0 < k := by dsimp [k]; omega
  have hkle : k ≤ n := by dsimp [k,N] at *; omega
  have hdiv : w = rem + q*N := by
    have he := Int.emod_def w N
    have hc := Int.mul_comm N (w/N)
    dsimp [rem,q] at *
    omega
  have ha : (a:Int)-(k:Int) = i+q*N := by
    dsimp [k,w] at *
    omega
  have hb : (b:Int)-(k:Int) = (i+(d:Int))+q*N := by
    dsimp [d,k,w] at *
    omega
  have hA := periodic_int_mul N j hper i q
  have hB := periodic_int_mul N j hper (i+(d:Int)) q
  refine ⟨k,hkpos,hkle,?_⟩
  intro he
  rw [ha,hb,hA,hB] at he
  exact hneq he.symm

private theorem le_sum_of_mem (x : Nat) (l : List Nat) (hx : x ∈ l) :
    x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.sum_cons]
    rcases hx with he | ht
    · subst y
      omega
    · have hh := ih ht
      omega

theorem no_primitive_periodic_slope (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hn : 0 < n)
    (hper : ∀ i : Int, j (i+(n:Int)) = j i)
    (hmin : MinimalPeriod n j)
    (hK : K ≤ 6 * ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum) : False := by
  have hprim := minimal_period_backward_primitive n j hn hper hmin
  let l : List Nat := (List.finRange n).map (fun s : Fin n => j (s.val:Int))
  have hmem : j (0:Int) ∈ l := by
    let s0 : Fin n := ⟨0,hn⟩
    exact List.mem_map.mpr ⟨s0,List.mem_finRange s0, by rfl⟩
  have hp : 0 < j (0:Int) := (h (0:Int)).2.2.1
  have hpos : 0 < l.sum := by
    have hh := le_sum_of_mem (j (0:Int)) l hmem
    omega
  exact no_primitive_window K n v j h hprim hpos hK

#print axioms periodic_past_constant
#print axioms no_primitive_periodic_slope
#print axioms minimal_period_backward_primitive
end ValuationPacking
