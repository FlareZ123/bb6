import WordBlock
namespace BB6.Agent12WordRunner
open BB6.Agent12WordBlock
abbrev Pair := Nat × Nat

def encode (p : Pair) : State := ⟨p.1,p.1+2*p.2⟩

theorem encode_consistent (p : Pair) : consistent (encode p) := by
  rcases p with ⟨a,k⟩
  simp [consistent,parity,encode]

theorem decode_encode (p : Pair) : decode (encode p)=p := by
  rcases p with ⟨a,k⟩
  simp [decode,encode,gap]
  omega

structure Plan where
  word : List Nat
  positive : ∀ r ∈ word, 1≤r
  steps : Nat
  steps_eq : steps=word.length
  nonzero : 0<steps
  power : Nat
  power_eq : power=2^shift word
  even : Coeff
  even_eq : even=coeff word 0
  odd : Coeff
  odd_eq : odd=coeff word 1

def makePlan (rs : List Nat) : Option Plan :=
  if h : 0<rs.length ∧ rs.all (fun r => decide (1≤r)) = true then
    some ⟨rs,by
      intro r hr
      exact of_decide_eq_true (List.all_eq_true.mp h.2 r hr),
      rs.length,rfl,h.1,2^shift rs,rfl,coeff rs 0,rfl,coeff rs 1,rfl⟩
  else none

def planCoeff (p : Plan) (o : Nat) : Coeff := if o=0 then p.even else p.odd

theorem planCoeff_eq (p : Plan) (m : Nat) : planCoeff p (m%2)=coeff p.word (m%2) := by
  have h : m%2=0 ∨ m%2=1 := by omega
  rcases h with h|h
  · simp [planCoeff,h,p.even_eq]
  · simp [planCoeff,h,p.odd_eq]

structure CertifiedBlock (next : Pair → Option Pair) (p : Pair) (limit : Nat) where
  steps : Nat
  endpoint : Pair
  positive : 0<steps
  bounded : steps≤limit
  exact_run : runNext next steps (some p)=some endpoint

def tryPlan (next : Pair → Option Pair) (law : EdgeLaw next)
    (p : Pair) (limit : Nat) (plan : Plan) : Option (CertifiedBlock next p limit) :=
  let s := encode p
  let t := applyCoeff (planCoeff plan (s.m%2)) s
  if h : plan.steps≤limit ∧ 8*plan.power≤s.m ∧ 0≤t.a ∧
      20*(plan.power:Int)≤gap t+4 then
    some ⟨plan.steps,decode t,plan.nonzero,h.1,by
      have he : applyCoeff (coeff plan.word (s.m%2)) s=t := by
        simp only [t,planCoeff_eq]
      have hm : 8*2^shift plan.word≤s.m := by simpa only [plan.power_eq] using h.2.1
      have hg : 20*(2:Int)^shift plan.word≤gap t+4 := by
        have he : (plan.power:Int)=(2:Int)^shift plan.word := by
          rw [plan.power_eq]
          exact_mod_cast (rfl : (2:Nat)^shift plan.word=2^shift plan.word)
        simpa only [he] using h.2.2.2
      have hx := block_certificate next law plan.word s t plan.positive hm (encode_consistent p) he h.2.2.1 hg
      simpa only [plan.steps_eq,s,decode_encode] using hx⟩
  else none

def bitWord (q : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | i+1,g => if q.testBit i then (g+1)::bitWord q i 0 else bitWord q i (g+1)

theorem bitWord_positive (q n g : Nat) : ∀ r ∈ bitWord q n g, 1≤r := by
  induction n generalizing g with
  | zero => simp [bitWord]
  | succ n ih =>
    intro r hr
    simp only [bitWord] at hr
    split at hr
    next h =>
      rcases List.mem_cons.mp hr with h|h
      · omega
      · exact ih 0 r h
    next h => exact ih (g+1) r hr

theorem bitWord_shift (q n g : Nat) : shift (bitWord q n g)≤n+g := by
  induction n generalizing g with
  | zero => simp [bitWord,shift]
  | succ n ih =>
    simp only [bitWord]
    split
    next h =>
      have hp := ih 0
      simp only [shift,List.sum_cons] at hp ⊢
      omega
    next h => have hp := ih (g+1); omega

def makeTable (bits : Nat) : Array (Option Plan) :=
  (List.range (2^bits)).toArray.map (fun q => makePlan (bitWord q bits 0))

def tablePredict (bits : Nat) (tab : Array (Option Plan)) (p : Pair) : Option Plan :=
  let q := (2^bits*p.1)/(p.1+2*p.2)
  (tab[q]?).join

def runBudget (next : Pair → Option Pair) (law : EdgeLaw next)
    (predict : Pair → Option Plan) (n : Nat) (p : Pair) : Option Pair :=
  if hn : n=0 then some p else
    match (predict p).bind (tryPlan next law p n) with
    | some b => runBudget next law predict (n-b.steps) b.endpoint
    | none => match next p with
      | some q => runBudget next law predict (n-1) q
      | none => none
termination_by n
decreasing_by
  · have h₁ := b.positive
    have h₂ := b.bounded
    omega
  · omega

theorem runNext_none (next : Pair → Option Pair) (n : Nat) :
    runNext next n none=none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [runNext] using ih

theorem runNext_add (next : Pair → Option Pair) (n m : Nat) (s : Option Pair) :
    runNext next (n+m) s=runNext next m (runNext next n s) := by
  induction n generalizing s with
  | zero => simp [runNext]
  | succ n ih => rw [show n+1+m=n+m+1 by omega,runNext,runNext,ih]

theorem runBudget_eq (next : Pair → Option Pair) (law : EdgeLaw next)
    (predict : Pair → Option Plan) (n : Nat) (p : Pair) :
    runBudget next law predict n p=runNext next n (some p) := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    rw [runBudget]
    split
    next h => subst n; rfl
    next hn =>
      split
      next b hb =>
        have h₁ := b.positive
        have h₂ := b.bounded
        rw [ih (n-b.steps) (by omega) b.endpoint]
        calc
          runNext next (n-b.steps) (some b.endpoint) = runNext next (n-b.steps) (runNext next b.steps (some p)) := by rw [b.exact_run]
          _ = runNext next (b.steps+(n-b.steps)) (some p) := (runNext_add next b.steps (n-b.steps) (some p)).symm
          _ = runNext next n (some p) := by rw [show b.steps+(n-b.steps)=n by omega]
      next hn' =>
        split
        next q hq =>
          rw [ih (n-1) (by omega) q]
          calc
            runNext next (n-1) (some q) = runNext next ((n-1)+1) (some p) := by simp [runNext,hq]
            _ = runNext next n (some p) := by rw [show n-1+1=n by omega]
        next hq =>
          calc
            none = runNext next ((n-1)+1) (some p) := by simp [runNext,hq,runNext_none]
            _ = runNext next n (some p) := by rw [show n-1+1=n by omega]

#print axioms tryPlan
#print axioms bitWord_shift
#print axioms runBudget_eq
end BB6.Agent12WordRunner
