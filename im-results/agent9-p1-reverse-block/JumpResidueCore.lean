import ReverseBlock

namespace BB6.Agent9JumpResidue
open BB6.Agent45ReverseBlock (corr)

/-- Extending a word by a leading zero adds one to the correction weight
    of every existing bit. -/
theorem corr_extend_zero (k B : Nat) (hB : B < 2^k) :
    corr (k+1) B = corr k B + B := by
  induction k generalizing B with
  | zero =>
    have h : B = 0 := by simpa using hB
    simp [h, corr]
  | succ k ih =>
    have h : B/2 < 2^k := by rw [Nat.pow_succ] at hB; omega
    have he := ih (B/2) h
    change 2*corr (k+1) (B/2)+(k+2)*(B%2) =
      (2*corr k (B/2)+(k+1)*(B%2))+B
    rw [he, show k+2=(k+1)+1 by omega, Nat.add_mul, Nat.one_mul]
    omega

/-- Setting the newly added top bit contributes precisely its place value
    to the correction. -/
theorem corr_extend_one (k B : Nat) (hB : B < 2^k) :
    corr (k+1) (B+2^k) = corr (k+1) B + 2^k := by
  induction k generalizing B with
  | zero =>
    have h : B = 0 := by simpa using hB
    simp [h, corr]
  | succ k ih =>
    have h : B/2 < 2^k := by rw [Nat.pow_succ] at hB; omega
    have hd : (B+2^(k+1))/2 = B/2+2^k := by rw [Nat.pow_succ]; omega
    have hm : (B+2^(k+1))%2 = B%2 := by rw [Nat.pow_succ]; omega
    change 2*corr (k+1) ((B+2^(k+1))/2)+(k+2)*((B+2^(k+1))%2) =
      2*corr (k+1) (B/2)+(k+2)*(B%2)+2^(k+1)
    rw [hd,hm,ih (B/2) h,Nat.pow_succ]
    omega

/-- Signed weighted contribution. The sign is useful because the jump
    generator uses subtraction modulo a fixed power of two. -/
def weight (q k B : Nat) : Int := ((q+k)*B : Nat) - (corr k B : Int)

theorem weight_zero (q k B : Nat) (hB : B < 2^k) :
    weight q (k+1) B = weight q k B := by
  unfold weight
  rw [corr_extend_zero k B hB, show q+(k+1)=q+k+1 by omega, Nat.add_mul, Nat.one_mul]
  simp only [Int.natCast_add]
  omega

theorem weight_one (q k B : Nat) (hB : B < 2^k) :
    weight q (k+1) (B+2^k) = weight q k B + ((q+k)*2^k : Nat) := by
  unfold weight
  rw [corr_extend_one k B hB, corr_extend_zero k B hB,
    Nat.mul_add, show q+(k+1)=q+k+1 by omega]
  rw [Nat.add_mul (q+k) 1 B,Nat.add_mul (q+k) 1 (2^k)]
  simp only [Nat.one_mul,Int.natCast_add]
  omega

/-- Low-bit-first set construction: duplicates are immaterial to membership.
    The actual C++ loop appends only shifts not already seen. -/
def residues (M : Int) (q : Nat) (Y : Int) : Nat → List Int
  | 0 => [Y % M]
  | j+1 => let old := residues M q Y j
           old ++ old.map (fun x => (x - ((q+j)*2^j : Nat)) % M)

/-- Exact membership after j iterations; M is fixed independently of j. -/
theorem mem_residues_iff (M : Int) (q : Nat) (Y x : Int) (j : Nat) :
    x ∈ residues M q Y j ↔
      ∃ B, B < 2^j ∧ x = (Y-weight q j B)%M := by
  induction j generalizing x with
  | zero =>
    simp only [residues,List.mem_singleton,Nat.pow_zero,Nat.lt_one_iff]
    constructor
    · intro h
      exact ⟨0,rfl,by simpa [weight,corr] using h⟩
    · rintro ⟨B,rfl,h⟩
      simpa [weight,corr] using h
  | succ j ih =>
    simp only [residues,List.mem_append,List.mem_map]
    constructor
    · rintro (h|⟨a,ha,rfl⟩)
      · obtain ⟨B,hB,hx⟩ := (ih x).1 h
        exact ⟨B,by rw [Nat.pow_succ]; omega,by rw [weight_zero q j B hB]; exact hx⟩
      · obtain ⟨B,hB,hx⟩ := (ih a).1 ha
        refine ⟨B+2^j,by rw [Nat.pow_succ]; omega,?_⟩
        rw [hx,Int.emod_sub_emod,weight_one q j B hB]
        congr 1
        omega
    · rintro ⟨B,hB,rfl⟩
      by_cases hlo : B<2^j
      · left
        exact (ih _).2 ⟨B,hlo,by rw [weight_zero q j B hlo]⟩
      · right
        let b := B-2^j
        have hb : b<2^j := by rw [Nat.pow_succ] at hB; dsimp [b]; omega
        have hEq : B=b+2^j := by dsimp [b]; omega
        refine ⟨(Y-weight q j b)%M,(ih _).2 ⟨b,hb,rfl⟩,?_⟩
        rw [Int.emod_sub_emod,hEq,weight_one q j b hb]
        congr 1
        omega

/-- Deduplication at each round models the `seen` table: membership is
    independent of the order or multiplicity of the old residues. -/
def residuesUnique (M : Int) (q : Nat) (Y : Int) : Nat → List Int
  | 0 => [Y % M]
  | j+1 => let old := residuesUnique M q Y j
           (old ++ old.map (fun x => (x - ((q+j)*2^j : Nat)) % M)).eraseDups

theorem mem_residuesUnique_iff (M : Int) (q : Nat) (Y x : Int) (j : Nat) :
    x ∈ residuesUnique M q Y j ↔ x ∈ residues M q Y j := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [residuesUnique,residues,List.mem_eraseDups,List.mem_append,List.mem_map,ih]

theorem residue_range (M : Int) (q : Nat) (Y x : Int) (j : Nat)
    (hM : 0 < M) (hx : x ∈ residuesUnique M q Y j) : 0 ≤ x ∧ x < M := by
  obtain ⟨B,_,rfl⟩ := (mem_residues_iff M q Y x j).1
    ((mem_residuesUnique_iff M q Y x j).1 hx)
  exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hM⟩

#print axioms mem_residues_iff
#print axioms mem_residuesUnique_iff
#print axioms residue_range
end BB6.Agent9JumpResidue
