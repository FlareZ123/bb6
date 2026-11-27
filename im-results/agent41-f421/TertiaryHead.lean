import Std
namespace F421TertiaryHead

def drain (h : Nat) : List Nat → List Nat × Nat
  | [] => ([], h)
  | u :: us =>
    if u ≤ h then drain (h+u) us
    else
      let (ys, H) := drain (2*h) us
      ((u-h) :: ys, H)

def boost (s : Nat) : List Nat → List Nat
  | [] => []
  | u::us => (u+s)::boost (2*s) us

def step (us : List Nat) : List Nat :=
  let (as, A) := drain 2 us
  let (bs, B) := drain 2 as
  boost 1 bs ++ [2^bs.length+A+B]

theorem drainMass (us : List Nat) (h : Nat) :
    (drain h us).1.sum + (drain h us).2 = us.sum+h := by
  induction us generalizing h with
  | nil => simp [drain]
  | cons u us ih =>
    by_cases hu : u ≤ h
    · simp only [drain,ite_eq_left hu,List.sum_cons]
      rw [ih]
      omega
    · simp only [drain,ite_eq_right hu]
      rcases he : drain (2*h) us with ⟨ys,H⟩
      have hh := ih (2*h)
      rw [he] at hh
      simp only [List.sum_cons] at hh ⊢
      omega

theorem drainLength (us : List Nat) (h : Nat) : (drain h us).1.length ≤ us.length := by
  induction us generalizing h with
  | nil => simp [drain]
  | cons u us ih =>
    by_cases hu : u ≤ h
    · simp [drain,hu]
      exact Nat.le_succ_of_le (ih (h+u))
    · rcases he : drain (2*h) us with ⟨ys,H⟩
      have hh := ih (2*h)
      rw [he] at hh
      simp only [drain,ite_eq_right hu,he,List.length_cons]
      exact Nat.succ_le_succ hh

theorem boostLength (us : List Nat) (s : Nat) : (boost s us).length = us.length := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih => simp [boost,ih]

theorem boostMass (us : List Nat) (s : Nat) :
    (boost s us).sum + s = us.sum + s*2^us.length := by
  induction us generalizing s with
  | nil => simp [boost]
  | cons u us ih =>
    have hh := ih (2*s)
    simp only [boost,List.sum_cons,List.length_cons,Nat.pow_succ]
    have eq : 2*s*2^us.length = s*(2^us.length*2) := by ac_rfl
    rw [eq] at hh
    omega

theorem stepMass (us : List Nat) :
    (step us).sum = us.sum+3+2^((step us).length) := by
  rcases ha : drain 2 us with ⟨as,A⟩
  rcases hb : drain 2 as with ⟨bs,B⟩
  have hA := drainMass us 2
  have hB := drainMass as 2
  rw [ha] at hA
  rw [hb] at hB
  change as.sum + A = us.sum+2 at hA
  change bs.sum + B = as.sum+2 at hB
  have hC := boostMass bs 1
  simp only [Nat.one_mul] at hC
  simp only [step,ha,hb,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,
    List.length_append,List.length_cons,List.length_nil,boostLength,Nat.pow_succ]
  omega

theorem stepLength (us : List Nat) : (step us).length ≤ us.length+1 := by
  rcases ha : drain 2 us with ⟨as,A⟩
  rcases hb : drain 2 as with ⟨bs,B⟩
  have hA := drainLength us 2
  have hB := drainLength as 2
  rw [ha] at hA
  rw [hb] at hB
  change as.length ≤ us.length at hA
  change bs.length ≤ as.length at hB
  simp only [step,ha,hb,List.length_append,List.length_cons,List.length_nil,boostLength]
  omega

theorem firstSurvives (u : Nat) (us : List Nat) (hu : 4 < u) :
    (step (u::us)).head? = some (u-3) := by
  have h1 : ¬u ≤ 2 := by omega
  have h2 : ¬u-2 ≤ 2 := by omega
  rcases ha : drain 4 us with ⟨as,A⟩
  rcases hb : drain 4 as with ⟨bs,B⟩
  simp [step,drain,h1,h2,ha,hb,boost]
  omega

theorem zeroCross (B q : Nat) (hB : 1 ≤ B) (hq : 2+2*B ≤ q) :
    3 ≤ q-(2*B-1) := by omega

theorem zeroNearest (M N H r : Nat) (hN : N ≤ 2*M)
    (hH : N ≤ H+1) : N ≤ 2*M+H+r-(N-1) := by omega

theorem zeroLeading (N H : Nat) (hN : N ≤ H+1) :
    3*N-1 ≤ N+1+2*H := by omega

theorem farPIncrease (p B : Nat) (hp : 1 ≤ p) (hB : 1 ≤ B) :
    p-1+2*(2*B)-(2*B-1) = p+2*B := by omega

theorem zeroFarP (p B : Nat) (hp : 1 ≤ p) (hB : 1 ≤ B) :
    p-1+2*B-(2*B-1) = p := by omega

#print axioms drainMass
#print axioms stepMass
#print axioms stepLength
#print axioms firstSurvives
#print axioms zeroCross
#print axioms zeroNearest
#print axioms zeroLeading
#print axioms farPIncrease
#print axioms zeroFarP
end F421TertiaryHead
