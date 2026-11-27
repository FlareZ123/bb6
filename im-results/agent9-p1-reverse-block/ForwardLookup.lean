import PlaneReverseSource
namespace BB6.Agent9ForwardLookup
open BB6.Agent45ReverseBlock
open BB6.Agent9PlaneReverse (wordWeight wordWeight_add_corr target_lt terminal_lt)

/-- The weighted word's residue depends only on the low k clock bits. -/
theorem weight_mod_clock (q k B : Nat) :
    wordWeight q k B % 2^k = wordWeight (q%2^k) k B % 2^k := by
  unfold wordWeight
  calc
    (q*B+BB6.Agent45WeightedDigitGap.digitWeight k B)%2^k =
      ((q*B)%2^k+BB6.Agent45WeightedDigitGap.digitWeight k B%2^k)%2^k := Nat.add_mod _ _ _
    _ = (((q%2^k)*B)%2^k+BB6.Agent45WeightedDigitGap.digitWeight k B%2^k)%2^k := by
      congr 2
      rw [Nat.mul_mod q B (2^k), Nat.mul_mod (q%2^k) B (2^k), Nat.mod_mod]
    _ = ((q%2^k)*B+BB6.Agent45WeightedDigitGap.digitWeight k B)%2^k := (Nat.add_mod _ _ _).symm

/-- The table row indexed by q mod 2^k and (Y-c) mod 2^k. -/
def words (q k c Y : Nat) : List Nat :=
  (List.range (2^k)).filter fun B =>
    decide (wordWeight (q%2^k) k B % 2^k = (Y+2^k-c%2^k)%2^k)

theorem mod_sum_eq (M a b Y : Nat) (ha : a<M) (hb : b<M) (hY : Y<M) :
    b=(Y+M-a)%M ↔ (a+b)%M=Y := by
  have hsum : (a+b)%M=if a+b<M then a+b else a+b-M := by
    split
    · exact Nat.mod_eq_of_lt (by assumption)
    · rename_i hn
      have he : a+b=M+(a+b-M) := by omega
      calc
        (a+b)%M = (M+(a+b-M))%M := congrArg (· % M) he
        _ = a+b-M := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  by_cases h : a≤Y
  · have he : Y+M-a=M+(Y-a) := by omega
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega : Y-a<M),hsum]
    split <;> omega
  · rw [Nat.mod_eq_of_lt (by omega : Y+M-a<M),hsum]
    split <;> omega

/-- Membership in the modular table is equivalent to the endpoint equation
    being divisible by the block radix. -/
theorem words_mem (q k c Y B : Nat) (hY : Y<2^k) :
    B∈words q k c Y ↔ B<2^k ∧ (c+wordWeight q k B)%2^k=Y := by
  have hp : 0<2^k := Nat.two_pow_pos _
  have hc := Nat.mod_lt c hp
  have hw := Nat.mod_lt (wordWeight q k B) hp
  simp only [words,List.mem_filter,List.mem_range,decide_eq_true_eq,←weight_mod_clock]
  rw [Nat.add_mod c (wordWeight q k B)]
  exact and_congr_right fun _ => mod_sum_eq _ _ _ _ hc hw hY

/-- Enumerate only the table's candidates, and reject negative/out-of-range
    quotients. There is no fitted-block hypothesis. -/
def forward (q k c Y : Nat) : List Nat :=
  ((words q k c Y).filterMap fun B =>
    let X := c+wordWeight q k B
    if Y≤X ∧ (X-Y)/2^k<q+k then some ((X-Y)/2^k) else none)

theorem forward_iff_walk (q c z : Nat) (ys : List Nat)
    (hys : ∀ y∈ys,y≤1) (hc : c<q) :
    z∈forward q ys.length c (digits ys) ↔ Walk (q+ys.length) z ys c := by
  have hY := target_lt ys hys
  constructor
  · intro h
    obtain ⟨B,hB,hval⟩ := List.mem_filterMap.mp h
    have hres := (words_mem q ys.length c (digits ys) B hY).mp hB
    dsimp only at hval
    split at hval
    · rename_i hh
      have hz : (c+wordWeight q ys.length B-digits ys)/2^ys.length=z := by
        simpa using hval
      have hD := Nat.div_add_mod (c+wordWeight q ys.length B) (2^ys.length)
      have hEq : c+wordWeight q ys.length B=2^ys.length*z+digits ys := by
        rw [hres.2] at hD
        have hsub : c+wordWeight q ys.length B-digits ys=2^ys.length*((c+wordWeight q ys.length B)/2^ys.length) := by omega
        rw [hsub,Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)] at hz
        rw [hz] at hD
        omega
      apply walk_of_eq (q+ys.length) z ys B c hys hres.1 (by omega)
      have hW := wordWeight_add_corr q ys.length B hres.1
      omega
    · simp at hval
  · intro h
    obtain ⟨B,hB,hEq⟩ := eq_of_walk h
    have hW := wordWeight_add_corr q ys.length B hB
    have hEq' : c+wordWeight q ys.length B=2^ys.length*z+digits ys := by omega
    have hres : (c+wordWeight q ys.length B)%2^ys.length=digits ys := by
      rw [hEq',Nat.mul_add_mod,Nat.mod_eq_of_lt hY]
    have hm := (words_mem q ys.length c (digits ys) B hY).mpr ⟨hB,hres⟩
    apply List.mem_filterMap.mpr
    refine ⟨B,hm,?_⟩
    have hZ := terminal_lt h
    have hquot : (c+wordWeight q ys.length B-digits ys)/2^ys.length=z := by
      rw [hEq',Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    simp [show digits ys≤c+wordWeight q ys.length B by omega,hquot,hZ]

#print axioms weight_mod_clock
#print axioms words_mem
#print axioms forward_iff_walk
end BB6.Agent9ForwardLookup
