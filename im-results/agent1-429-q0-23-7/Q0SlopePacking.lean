import Q0MacroCore
import Lean.Elab.Tactic.Omega
import Init.Data.List.Perm

namespace BB429Q0Macro
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The strict-interior signed graph is a forest directed toward increasing p:
a destination has at most one interior predecessor, even across digits. -/
theorem interior_predecessor_unique
    (d e : Digit) (p q y z P Y : Nat)
    (hy : 0 < y) (hz : 0 < z) (hpy : 3*y < p) (hqz : 3*z < q)
    (hp : nextP d p = P) (hq : nextP e q = P)
    (hd : num d p y = 16*Y) (he : num e q z = 16*Y) :
    d=e ∧ p=q ∧ y=z := by
  cases d <;> cases e <;> simp [nextP,cost,num,digit,offset] at * <;> omega

/-- Possible destination slopes of a constant-p difference walk are in
four short, disjoint bands. Each band needs at most L/48+1 integers. -/
def slopeBand (L d : Nat) : List Nat :=
  (List.range (L/48+1)).map (fun i => (d*L+15)/16+i)

def slopeBands (L : Nat) : List Nat :=
  slopeBand L 0 ++ slopeBand L 1 ++ slopeBand L 4 ++ slopeBand L 5

theorem mem_slopeBand (L d a b : Nat)
    (ha : 3*a≤L) (h : 16*b=a+d*L) :
    b ∈ slopeBand L d := by
  let lo := (d*L+15)/16
  have hlo : lo≤b := by dsimp [lo]; omega
  have hhi : b-lo<L/48+1 := by dsimp [lo]; omega
  simp only [slopeBand,List.mem_map,List.mem_range]
  exact ⟨b-lo,hhi,by dsimp [lo] at hlo ⊢; omega⟩

theorem mem_slopeBands (L a b : Nat) (d : Digit)
    (ha : 3*a≤L) (h : 16*b=a+digit d*L) :
    b ∈ slopeBands L := by
  have hmem := mem_slopeBand L (digit d) a b ha h
  cases d <;> simp [digit] at hmem <;> simp only [slopeBands,List.mem_append]
  · exact Or.inl (Or.inl (Or.inl hmem))
  · exact Or.inl (Or.inl (Or.inr hmem))
  · exact Or.inl (Or.inr hmem)
  · exact Or.inr hmem

theorem length_slopeBands (L : Nat) :
    (slopeBands L).length=4*(L/48+1) := by
  simp [slopeBands,slopeBand]
  omega

/-- Packing lemma for distinct integer slopes along a primitive
constant-p-difference cycle. Strict cost bound holds unless every digit is 5. -/
theorem slope_packing (L : Nat) (ts : List Nat)
    (hn : ts.Nodup) (hL : L<6*ts.length)
    (hm : ∀ t∈ts, t∈slopeBands L) : ts.length≤4 := by
  have h := List.Nodup.length_le_of_subset hn hm
  rw [length_slopeBands] at h
  have h8 : ts.length≤8 := by omega
  have h48 : L<48 := by omega
  have hdiv : L/48=0 := by omega
  omega

def costSum : List Digit → Nat
  | [] => 0
  | d::ds => cost d+costSum ds

def digitWord : List Digit → Nat
  | [] => 0
  | d::ds => digit d+16*digitWord ds

theorem costSum_le (ds : List Digit) : costSum ds≤6*ds.length := by
  induction ds with
  | nil => simp [costSum]
  | cons d ds ih => cases d <;> simp [costSum,cost] <;> omega

theorem costSum_lt (ds : List Digit)
    (h : ¬ ∀ d∈ds, d=Digit.five) :
    costSum ds<6*ds.length := by
  induction ds with
  | nil => simp at h
  | cons d ds ih =>
    have htail := costSum_le ds
    by_cases hd : d=Digit.five
    · subst d
      have h' : ¬ ∀ d∈ds, d=Digit.five := by
        intro hgood
        apply h
        intro e he
        rcases List.mem_cons.mp he with h0|h0
        · exact h0
        · exact hgood e h0
      have hh := ih h'
      simp [costSum,cost]
      omega
    · cases d <;> simp [costSum,cost] at * <;> omega

/-- A cyclic difference walk. ts contains the successive destination slopes. -/
inductive SlopeWalk (L : Nat) : List Digit → List Nat → Nat → Nat → Prop where
  | nil (a : Nat) : SlopeWalk L [] [] a a
  | cons {d : Digit} {ds : List Digit} {ts : List Nat} {a b c : Nat}
      (h : 16*b=a+digit d*L) (tail : SlopeWalk L ds ts b c) :
      SlopeWalk L (d::ds) (b::ts) a c

theorem walk_length {L ds ts a b} (h : SlopeWalk L ds ts a b) :
    ts.length=ds.length := by
  induction h with
  | nil => rfl
  | cons h tail ih => simp [ih]

theorem slope_step_bound (L a b : Nat) (d : Digit)
    (ha : 3*a≤L) (h : 16*b=a+digit d*L) : 3*b≤L := by
  cases d <;> simp [digit] at h <;> omega

theorem walk_bands {L ds ts a b} (h : SlopeWalk L ds ts a b)
    (ha : 3*a≤L) : ∀ t∈ts, t∈slopeBands L := by
  induction h with
  | nil => simp
  | @cons d ds ts a b c hstep tail ih =>
    intro t ht
    rcases List.mem_cons.mp ht with he|he
    · subst t
      exact mem_slopeBands L a b d ha hstep
    · exact ih (slope_step_bound L a b d ha hstep) t he

theorem walk_equation {L ds ts a b} (h : SlopeWalk L ds ts a b) :
    16^ds.length*b=a+L*digitWord ds := by
  induction h with
  | nil => simp [digitWord]
  | @cons d ds ts a b c hstep tail ih =>
    simp only [List.length_cons,Nat.pow_succ,digitWord]
    calc
      16^ds.length*16*c=16*(16^ds.length*c) := by ac_rfl
      _=16*(b+L*digitWord ds) := by rw [ih]
      _=a+L*(digit d+16*digitWord ds) := by
        rw [Nat.mul_add,Nat.mul_add,hstep,Nat.mul_comm (digit d) L]
        rw [Nat.mul_left_comm 16 L]
        omega

def allDigits : List Digit := [.zero,.one,.four,.five]

def allWords : Nat → List (List Digit)
  | 0 => [[]]
  | n+1 => allDigits.flatMap (fun d => (allWords n).map (d::·))

theorem allWords_complete (ds : List Digit) :
    ds∈allWords ds.length := by
  induction ds with
  | nil => simp [allWords]
  | cons d ds ih =>
    simp only [List.length_cons,allWords,List.mem_flatMap,List.mem_map]
    exact ⟨d,by cases d <;> simp [allDigits],ds,ih,rfl⟩

def constantEndpoint (ds : List Digit) : Bool :=
  ds.all (· == .zero) || ds.all (· == .five) ||
    (ds.length == 3 && ds.all (· == .one))

def smallOK (ds : List Digit) : Bool :=
  ((digitWord ds * costSum ds) % (16^ds.length-1) != 0) || constantEndpoint ds

theorem small_check :
    ((allWords 1 ++ allWords 2 ++ allWords 3 ++ allWords 4).all smallOK)=true := by decide

theorem small_slope (ds : List Digit) (hpos : 0<ds.length)
    (hlen : ds.length≤4)
    (hdiv : (digitWord ds*costSum ds)%(16^ds.length-1)=0) :
    ((∀ d∈ds,d=Digit.zero) ∨ (∀ d∈ds,d=Digit.five)) ∨
      (ds.length=3 ∧ ∀ d∈ds,d=Digit.one) := by
  have hm := allWords_complete ds
  have hcases : ds.length=1 ∨ ds.length=2 ∨ ds.length=3 ∨ ds.length=4 := by omega
  have hmem : ds ∈ allWords 1 ++ allWords 2 ++ allWords 3 ++ allWords 4 := by
    simp only [List.mem_append]
    rcases hcases with h|h|h|h <;> rw [h] at hm
    · exact Or.inl (Or.inl (Or.inl hm))
    · exact Or.inl (Or.inl (Or.inr hm))
    · exact Or.inl (Or.inr hm)
    · exact Or.inr hm
  have hc := List.all_eq_true.mp small_check ds hmem
  simp [smallOK,hdiv,constantEndpoint,List.all_eq_true] at hc
  exact hc

theorem all_one_cost (ds : List Digit) (h : ∀ d∈ds,d=Digit.one) :
    costSum ds=5*ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht : ∀ e∈ds,e=Digit.one := by
      intro e he
      exact h e (by simp [he])
    rw [hd,costSum,cost,ih ht]
    simp
    omega

theorem all_one_digit (ds : List Digit) (h : ∀ d∈ds,d=Digit.one) :
    15*digitWord ds+1=16^ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht : ∀ e∈ds,e=Digit.one := by
      intro e he
      exact h e (by simp [he])
    rw [hd,digitWord,digit,List.length_cons,Nat.pow_succ,← ih ht]
    omega

theorem all_one_walk {L ds ts a b} (h : SlopeWalk L ds ts a b)
    (hone : ∀ d∈ds,d=Digit.one) (ha : 15*a=L) :
    ∀ t∈ts,t=a := by
  induction h with
  | nil => simp
  | @cons d ds ts a b c hstep tail ih =>
    have hd := hone d (by simp)
    rw [hd,digit] at hstep
    have hab : b=a := by omega
    have ht : ∀ e∈ds,e=Digit.one := by
      intro e he
      exact hone e (by simp [he])
    intro t hmem
    rcases List.mem_cons.mp hmem with he|he
    · omega
    · have h' := ih ht (by omega) t he
      omega

theorem nodup_constant_le_one (ts : List Nat) (a : Nat)
    (hn : ts.Nodup) (h : ∀ t∈ts,t=a) : ts.length≤1 := by
  have hsub : ∀ t∈ts,t∈[a] := by
    intro t ht
    simpa using h t ht
  simpa using List.Nodup.length_le_of_subset hn hsub

/-- No nonconstant primitive integer slope cycle has total drift equal
to the sum of the digit costs. The small cases are kernel-decided. -/
theorem simple_slope_cycle {L a : Nat} {ds : List Digit} {ts : List Nat}
    (h : SlopeWalk L ds ts a a) (ha : 3*a≤L)
    (hn : ts.Nodup) (hpos : 0<ds.length) (hcost : L=costSum ds) :
    (∀ d∈ds,d=Digit.zero) ∨ (∀ d∈ds,d=Digit.five) := by
  by_cases h5 : ∀ d∈ds,d=Digit.five
  · exact Or.inr h5
  · have hlen := walk_length h
    have hlt := costSum_lt ds h5
    have hbound := slope_packing L ts hn (by omega) (walk_bands h ha)
    have he := walk_equation h
    have hpow : 0<16^ds.length := Nat.pow_pos (by decide)
    have hM : (16^ds.length-1)*a= L*digitWord ds := by
      rw [Nat.sub_mul,Nat.one_mul]
      omega
    have hdiv : (digitWord ds*costSum ds)%(16^ds.length-1)=0 := by
      rw [←hcost,Nat.mul_comm (digitWord ds) L,←hM,Nat.mul_mod_right]
    rcases small_slope ds hpos (by omega) hdiv with hh|⟨h3,h1⟩
    · exact hh
    · have hcost1 := all_one_cost ds h1
      have hd1 := all_one_digit ds h1
      rw [h3] at hcost1 hd1 he
      have hL15 : L=15 := by omega
      have hD : digitWord ds=273 := by omega
      rw [hL15,hD] at he
      have ha1 : 15*a=L := by omega
      have hc := nodup_constant_le_one ts a hn (all_one_walk h h1 ha1)
      omega

#print axioms interior_predecessor_unique
#print axioms slope_packing
#print axioms small_check
#print axioms simple_slope_cycle
end BB429Q0Macro
