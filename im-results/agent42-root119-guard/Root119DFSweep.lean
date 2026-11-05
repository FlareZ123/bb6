import Root119BShield
set_option linter.unusedSimpArgs false
namespace BB6Root119

/-- A D/1 then F/1 pair advances right by two, erasing the intermediate cell. -/
def dfPair (c : Conf) : Conf :=
  ⟨.D, c.h+2, setBit c.tape (c.h+1) false⟩

def dfValid (c : Conf) : Prop :=
  c.q = .D ∧ c.tape c.h = true ∧ c.tape (c.h+1) = true

theorem df_two_step (c : Conf) (hv : dfValid c) :
    run 2 c = some (dfPair c) := by
  rcases c with ⟨q,h,t⟩
  obtain ⟨hq,h0,h1⟩ := hv
  cases q <;> try contradiction
  change t h = true at h0
  change t (h+1) = true at h1
  have hne : h+1 ≠ h := by omega
  have hh : h+1+1 = h+2 := by omega
  simp [run,next,dfPair,setBit,h0,h1,hne,hh]
  funext x
  simp only [setBit]
  by_cases hx : x=h <;> by_cases hy : x=h+1 <;> simp_all <;> omega

/-- Only the bit at head +1 changes. -/
theorem dfPair_left (c : Conf) (x : Int) (hx : x ≠ c.h+1) :
    (dfPair c).tape x = c.tape x := by
  simp [dfPair,setBit,hx]

/-- A single D/F pair cannot create p q 0 0 left of the new head. -/
theorem df_pair_preserves_1100 (p q : Bool) (c : Conf)
    (hv : dfValid c) (hs : NoLeft4 p q false c) :
    NoLeft4 p q false (dfPair c) := by
  obtain ⟨hq,h0,h1⟩ := hv
  intro x hx hw
  change x+3 < c.h+2 at hx
  change (dfPair c).tape x = p ∧ (dfPair c).tape (x+1) = q ∧
    (dfPair c).tape (x+2) = false ∧ (dfPair c).tape (x+3) = false at hw
  by_cases hfar : x+3 < c.h
  · apply hs x hfar
    constructor
    · rw [dfPair_left c x (by omega)] at hw
      exact hw.1
    constructor
    · rw [dfPair_left c (x+1) (by omega)] at hw
      exact hw.2.1
    constructor
    · rw [dfPair_left c (x+2) (by omega)] at hw
      exact hw.2.2.1
    · rw [dfPair_left c (x+3) (by omega)] at hw
      exact hw.2.2.2
  · have hcases : x+3=c.h ∨ x+3=c.h+1 := by omega
    rcases hcases with hcase | hcase
    · have hlast : (dfPair c).tape (x+3) = true := by
        rw [hcase,dfPair_left c c.h (by omega)]
        exact h0
      exact Bool.false_ne_true (hw.2.2.2.symm.trans hlast)
    · have hthird : (dfPair c).tape (x+2) = true := by
        have heq : x+2=c.h := by omega
        rw [heq,dfPair_left c c.h (by omega)]
        exact h0
      exact Bool.false_ne_true (hw.2.2.1.symm.trans hthird)

/-- Entire n-pair D/F sweep, retaining all exterior-tape data. -/
def dfMany : Nat → Conf → Conf
  | 0, c => c
  | n+1, c => dfMany n (dfPair c)

def dfExtended (n : Nat) (c : Conf) : Prop :=
  c.q = .D ∧
  ∀ i : Nat, i < n →
    c.tape (c.h+2*(i:Int)) = true ∧
    c.tape (c.h+2*(i:Int)+1) = true

theorem dfExtended_head (n : Nat) (c : Conf) (hv : dfExtended (n+1) c) :
    dfValid c := by
  obtain ⟨hq,hrest⟩ := hv
  obtain ⟨h0,h1⟩ := hrest 0 (by omega)
  exact ⟨hq,by simpa using h0,by simpa using h1⟩

theorem dfExtended_tail (n : Nat) (c : Conf) (hv : dfExtended (n+1) c) :
    dfExtended n (dfPair c) := by
  obtain ⟨hq,hrest⟩ := hv
  refine ⟨rfl,?_⟩
  intro i hi
  obtain ⟨hi0,hi1⟩ := hrest (i+1) (by omega)
  constructor
  · change setBit c.tape (c.h+1) false (c.h+2+2*(i:Int)) = true
    rw [show c.h+2+2*(i:Int) = c.h+2*((i+1:Int)) by omega]
    simp only [setBit, if_neg (show c.h+2*((i+1:Int)) ≠ c.h+1 by omega)]
    have heq : c.h+2*((i+1:Int)) = c.h+2*((i+1:Nat):Int) := by omega
    rw [heq]
    exact hi0
  · change setBit c.tape (c.h+1) false (c.h+2+2*(i:Int)+1) = true
    rw [show c.h+2+2*(i:Int)+1 = c.h+2*((i+1:Int))+1 by omega]
    simp only [setBit, if_neg (show c.h+2*((i+1:Int))+1 ≠ c.h+1 by omega)]
    have heq : c.h+2*((i+1:Int))+1 = c.h+2*((i+1:Nat):Int)+1 := by omega
    rw [heq]
    exact hi1

theorem df_run_add (m n : Nat) (c : Conf) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    have heq : m+1+n=(m+n)+1 := by omega
    rw [heq]
    simp only [run, Option.bind_assoc]
    congr 1
    funext y
    exact ih y

/-- Exact source-machine execution for every natural sweep length. -/
theorem df_two_n (n : Nat) (c : Conf) (hv : dfExtended n c) :
    run (2*n) c = some (dfMany n c) := by
  induction n generalizing c with
  | zero => simp [run,dfMany]
  | succ n ih =>
    have hhead := dfExtended_head n c hv
    have htail := dfExtended_tail n c hv
    have htwo := df_two_step c hhead
    have hrest := ih (dfPair c) htail
    have hsplit : 2*(n+1) = 2+2*n := by omega
    rw [hsplit,df_run_add,htwo]
    simpa [dfMany] using hrest

/-- Arbitrarily long D/F rightward sweeps preserve left 1100-avoidance. -/
theorem df_many_preserves_1100 (p q : Bool) (n : Nat) (c : Conf)
    (hv : dfExtended n c) (hs : NoLeft4 p q false c) :
    NoLeft4 p q false (dfMany n c) := by
  induction n generalizing c with
  | zero => simpa [dfMany] using hs
  | succ n ih =>
    have hhead := dfExtended_head n c hv
    have htail := dfExtended_tail n c hv
    have hnew := df_pair_preserves_1100 p q c hhead hs
    simpa [dfMany] using ih (dfPair c) htail hnew

/-- Conditional original blank-reachability and 1100 shield transfer. -/
theorem reached_df_sweep_1100 (n : Nat) (c : Conf)
    (hc : Reach c) (hv : dfExtended n c) (hs : NoLeft4 true true false c) :
    Reach (dfMany n c) ∧ NoLeft4 true true false (dfMany n c) := by
  exact ⟨reachable_of_run (2*n) c (dfMany n c) hc (df_two_n n c hv),
    df_many_preserves_1100 true true n c hv hs⟩

#print axioms BB6Root119.df_two_n
#print axioms BB6Root119.df_many_preserves_1100
#print axioms BB6Root119.reached_df_sweep_1100
end BB6Root119
