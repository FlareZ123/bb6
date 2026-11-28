import F421SecondaryMass

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

/-- Either exact exhaustion or safe survival at each positional P cap. -/
def capP (B : Nat) : List Nat → Prop
  | [] => True
  | p::xs => (p=2*B ∨ 2*B+3≤p) ∧ capP (2*B) xs

def subtractBudget (B : Nat) : List Nat → List Nat
  | [] => []
  | p::xs => (p-2*B)::subtractBudget (2*B) xs

def budgetSum (B : Nat) : List Nat → Nat
  | [] => 0
  | _::xs => 2*B+budgetSum (2*B) xs

theorem budgetSumPow (B : Nat) (xs : List Nat) :
    budgetSum B xs + 2*B = 2*B*2^xs.length := by
  induction xs generalizing B with
  | nil => simp [budgetSum]
  | cons p xs ih =>
    have h := ih (2*B)
    simp only [budgetSum,List.length_cons,Nat.pow_succ]
    calc
      2*B+budgetSum (2*B) xs+2*B = budgetSum (2*B) xs+2*(2*B) := by omega
      _ = 2*(2*B)*2^xs.length := h
      _ = 2*B*(2^xs.length*2) := by ac_rfl

theorem subtractBudgetSum (B : Nat) (xs : List Nat) (hp : capP B xs) :
    (subtractBudget B xs).sum+budgetSum B xs=xs.sum := by
  induction xs generalizing B with
  | nil => rfl
  | cons p xs ih =>
    have h0 : 2*B≤p := by rcases hp.1 with h|h; omega; omega
    have ht := ih (2*B) hp.2
    simp only [subtractBudget,List.sum_cons,budgetSum]
    omega

/-- Original marked drain P-sum does not depend on terminal merge patterns
    or Q entries, for arbitrary exact-survivor/exhaustion P profiles. -/
theorem sourcePDrainSum (B : Nat) (xs : List Nat) (hB : 0<B) (hp : capP B xs) :
    (sourcePDrain (B-1) (xs.map (·-1))).1.sum =
      (subtractBudget B xs).sum := by
  induction xs generalizing B with
  | nil => rfl
  | cons p xs ih =>
    have ht := hp.2
    have hn : 0<2*B := by omega
    have he : 2*(B-1)+1=2*B-1 := by omega
    have hx : 2*B≤p := by rcases hp.1 with h|h; omega; omega
    rcases hp.1 with h|h
    · have hle : p-1≤2*(B-1)+1 := by omega
      have hstep : B-1+(p-1+1)/2=2*B-1 := by omega
      simp only [List.map_cons,sourcePDrain,ite_eq_left hle,hstep,
        subtractBudget,List.sum_cons]
      change (sourcePDrain (2*B-1) (xs.map (·-1))).1.sum =
        (p-2*B)+(subtractBudget (2*B) xs).sum
      have hpzero : p-2*B=0 := by omega
      rw [hpzero,Nat.zero_add]
      simpa using ih (2*B) hn ht
    · have hnot : ¬p-1≤2*(B-1)+1 := by omega
      simp only [List.map_cons,sourcePDrain,ite_eq_right hnot,
        subtractBudget,List.sum_cons]
      have hb' : 2*(B-1)+1=2*B-1 := by omega
      rw [hb']
      have h' := ih (2*B) hn ht
      have hdiff : p-1-(2*B-1)=p-2*B := by omega
      simp only [hdiff]
      rw [h']

/-- Exact P mass of the original marked source drain, arbitrary Q/carry. -/
theorem sourceOriginalDrainSum (B carry : Nat) (cs : List PC)
    (hB : 0<B) (hp : capP B (pProjection cs)) :
    pSum (drain (B-1) carry (dec cs)).1 =
      (subtractBudget B (pProjection cs)).sum := by
  have he := originalDrainPProjection (B-1) carry (dec cs)
  rw [projectionDec] at he
  have hh := sourcePDrainSum B (pProjection cs) hB hp
  have hSum := congrArg List.sum he
  simpa [pSum,pProjection] using hSum.trans hh

/-- Exact affine P-mass conservation even when arbitrarily many P cells
    delete or their Q blocks merge. The increment is the old leading a+3. -/
theorem secondaryPsumUniversal (b : Nat) (cs : List PC)
    (hp : capP 1 (pProjection cs)) :
    pSum ((sNext b cs).2.2) =
      pSum cs + (2*2^cs.length-1)+3 := by
  have h := sourceOriginalDrainSum 1 0 cs (by decide) hp
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  rw [he] at h
  have htrim : pSum (trimQ 1 as)=pSum as := by
    have ht := projectionTrimQ 1 as
    exact congrArg List.sum ht
  have hsum := subtractBudgetSum 1 (pProjection cs) hp
  have hbudget := budgetSumPow 1 (pProjection cs)
  have hlen : (pProjection cs).length=cs.length := by simp [pProjection]
  have hc : pSum cs=(pProjection cs).sum := rfl
  rw [hlen] at hbudget
  unfold sNext
  rw [he]
  simp only [Prod.fst,Prod.snd,pSum,List.map_append,List.map_singleton,List.map_cons,
     List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
  have hh : (as.map Cell.p).sum = (subtractBudget 1 (pProjection cs)).sum := by
    simpa [pSum] using h
  rw [show (trimQ 1 as).map Cell.p = as.map Cell.p from projectionTrimQ 1 as]
  rw [hh]
  have hpow : 0<2^cs.length := Nat.pow_pos (by decide)
  simp only [Nat.one_mul,Nat.mul_one] at hbudget
  simp only [List.map_nil,List.sum_nil,Nat.add_zero]
  dsimp only [pProjection] at hsum hbudget hh ⊢
  have numeric (d bud f e : Nat) (hs : d+bud=f) (hb : bud+2=2*e) :
      d+4*e=f+(2*e-1)+3 := by omega
  exact numeric _ _ _ _ hsum hbudget

#print axioms sourcePDrainSum
#print axioms secondaryPsumUniversal
end F421SecondaryLifetimes
