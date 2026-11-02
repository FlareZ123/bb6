import DTableWitness
import Lean.Elab.Tactic.Omega

namespace BB6.Portfolio

structure FiniteCfg where
  state : State
  head : Int
  ones : List Int
  deriving DecidableEq, Repr

def embed (c : FiniteCfg) : Cfg :=
  ⟨c.state,c.head,fun i => decide (i ∈ c.ones)⟩

def writeOnes (ones : List Int) (head : Int) (b : Bool) : List Int :=
  if b then head::(ones.filter (· ≠ head)) else ones.filter (· ≠ head)

def finiteStep (c : FiniteCfg) : Option FiniteCfg :=
  (D0 c.state (decide (c.head ∈ c.ones))).map fun (w,d,s) =>
    ⟨s,c.head+d.dx,writeOnes c.ones c.head w⟩

def finiteRun : Nat → Option FiniteCfg → Option FiniteCfg
  | 0, c => c
  | n+1, c => (finiteRun n c).bind finiteStep

theorem embed_writeOnes (xs : List Int) (h : Int) (b : Bool) :
    (fun i : Int => decide (i ∈ writeOnes xs h b)) =
    updateTape (fun i : Int => decide (i ∈ xs)) h b := by
  funext i
  by_cases p : i=h
  · subst i
    cases b <;> simp [writeOnes,updateTape]
  · cases b <;> simp [writeOnes,updateTape,p]

theorem embed_step (c : FiniteCfg) :
    step D0 (embed c)=(finiteStep c).map embed := by
  cases h : D0 c.state (decide (c.head ∈ c.ones)) with
  | none => simp [step,embed,finiteStep,h]
  | some instr =>
    rcases instr with ⟨w,d,s⟩
    simp only [step,embed,finiteStep,h,Option.map_some]
    congr 1
    congr 1
    exact (embed_writeOnes c.ones c.head w).symm

theorem embed_run (n : Nat) (c : Option FiniteCfg) :
    run D0 n (c.map embed) = (finiteRun n c).map embed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, finiteRun, ih]
    cases h : finiteRun n c with
    | none => simp
    | some p => simp [embed_step]

def finBlank (s : State) : FiniteCfg := ⟨s,0,[]⟩

theorem finBlank_embed (s : State) : embed (finBlank s) = blank s := by
  simp [embed,finBlank,blank]

-- Important: FiniteCfg records the exact current head and all positions of ones.
-- A verified finite certificate can be turned into an actual infinite-blank-tape
-- theorem without trusting a separate simulator.

def F0Pure (n : Nat) (h : Int) : Cfg :=
  ⟨(5 : State),h,fun i => decide (h<i ∧ i≤h+(n:Int))⟩

end BB6.Portfolio

namespace BB6.Portfolio

def intervalList (h : Int) (n : Nat) : List Int :=
  (List.range n).map (fun (j : Nat) => h+1+(j:Int))

theorem mem_intervalList (h i : Int) (n : Nat) :
    i ∈ intervalList h n ↔ h<i ∧ i≤h+(n:Int) := by
  simp only [intervalList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩
    have hcast : (j:Int) < (n:Int) := Int.ofNat_lt.mpr hj
    omega
  · intro hi
    have hp : 0 ≤ i-h-1 := by omega
    have castval : (((i-h-1).toNat:Int)) = i-h-1 :=
      Int.toNat_of_nonneg hp
    refine ⟨(i-h-1).toNat, ?_, ?_⟩
    · apply (Int.toNat_lt hp).2
      omega
    · omega

def finiteI (n : Nat) (h : Int) : FiniteCfg :=
  ⟨(5:State),h,intervalList h n⟩

theorem embed_finiteI (n : Nat) (h : Int) :
    embed (finiteI n h) = F0Pure n h := by
  simp only [embed,finiteI,F0Pure]
  congr 1
  funext i
  simp only [mem_intervalList]

theorem exact_blank_to_unary (s : State) (t n : Nat) (h : Int)
    (hc : finiteRun t (some (finBlank s))=some (finiteI n h)) :
    run D0 t (some (blank s)) = some (F0Pure n h) := by
  have hh := embed_run t (some (finBlank s))
  simpa only [Option.map_some,finBlank_embed,hc,embed_finiteI] using hh

-- Four distinct canonical machine roots land in the same reusable raw F0
-- section language. These are genuine blank-origin identities.
theorem blank_root_B_to_I5 :
    run D0 15 (some (blank (1:State))) = some (F0Pure 5 (-3)) := by
  apply exact_blank_to_unary
  decide

theorem blank_root_C_to_I15 :
    run D0 92 (some (blank (2:State))) = some (F0Pure 15 (-12)) := by
  apply exact_blank_to_unary
  set_option maxRecDepth 65536 in
    decide

theorem blank_root_F_to_I39 :
    run D0 403 (some (blank (5:State))) = some (F0Pure 39 (-35)) := by
  apply exact_blank_to_unary
  set_option maxRecDepth 65536 in
    decide

#print axioms mem_intervalList
#print axioms exact_blank_to_unary
#print axioms blank_root_B_to_I5
#print axioms blank_root_C_to_I15
#print axioms blank_root_F_to_I39
end BB6.Portfolio
