/-!
# A globally total, exactly counted, single-section token recurrence

Uses the original #85 token encodings and CountedTokenRules.append.lean.
Every input is a CR configuration with positive first token; the output
is either a CR configuration or a finite halt, with exact primitive count.
EL normalization is structural recursion on the remaining token list.
There is no affine guess, fuel cutoff, or fallback simulator.
-/

structure A12CRPoint where
  headMinusOne : ℕ
  rightTail : List ℕ
  left : List ℕ
  deriving DecidableEq, Repr

def a12TokenTape : List ℕ → ListBlank (Fin 2)
  | [] => default
  | k::K => (([1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> a12TokenTape K)

private theorem a12TokenTape_eq (K : List ℕ) :
    a12TokenTape K = encTokens K [] := by
  induction K with
  | nil => rfl
  | cons k K ih => simp only [a12TokenTape,encTokens,ih]

def a12PointCfg (s : A12CRPoint) : Cfg (Fin 2) (Fin 6) :=
  (a12TokenTape ((s.headMinusOne+1)::s.rightTail)) {{C}}>
    (encRight (s.left.map (fun x => (x,0))))

private theorem a12PointCfg_eq (s : A12CRPoint) :
    a12PointCfg s = tok_CR ((s.headMinusOne+1)::s.rightTail) [] s.left := by
  unfold a12PointCfg tok_CR
  rw [a12TokenTape_eq, encRightNat_eq]

def a12ELword (r v : ℕ) (L : List ℕ) : List ℕ :=
  List.replicate (r+1) 0 ++ (v+1)::L

def a12ELnorm (x r v : ℕ) (L : List ℕ) : ℕ × ℕ × ℕ :=
  if v=0 ∧ L=[] then
    (x%3,r+4*(x/3),a12HCost (x/3) (r+1))
  else (x,r,0)

private theorem a12ELnorm_sound (x r v : ℕ) (K L : List ℕ) :
    ReachesIn target (a12ELnorm x r v L).2.2
      (tok_EL (x::K) [] (a12ELword r v L))
      (tok_EL ((a12ELnorm x r v L).1::K) []
        (a12ELword (a12ELnorm x r v L).2.1 v L)) := by
  by_cases h : v=0 ∧ L=[]
  · obtain ⟨rfl,rfl⟩ := h
    simp only [a12ELnorm, ↓reduceIte, true_and, a12ELword]
    have h := a12cHmod x r K
    have hr : r+1+4*(x/3) = r+4*(x/3)+1 := by omega
    rw [hr] at h
    exact h
  · simp only [a12ELnorm, if_neg h]
    exact ReachesIn.zero _ _

-- Blank-end zero padding is an exact physical tape equality.
private theorem a12ELblank (L : List ℕ) :
    tok_EL [] [] L = tok_EL [0,0] [] L := by
  unfold tok_EL
  simp only [encTokens_zero, encTokens_nil, encLeft_nil, ListBlank.cons_zero_default]

private theorem a12ELzero (K L : List ℕ) :
    ReachesIn target 1 (tok_EL (0::K) [] L)
      (tok_CR ((K.headD 0+1)::K.drop 1) [] L) := by
  cases K with
  | nil =>
    have h : tok_EL [0] [] L = tok_EL [0,0] [] L := by
      unfold tok_EL
      simp only [encTokens_zero, encTokens_nil, encLeft_nil, ListBlank.cons_zero_default]
    rw [h]
    exact a12c_EL_0_cons 0 [] [] L
  | cons k K => exact a12c_EL_0_cons k K [] L

def a12CostAdd {α : Type} (n : ℕ) (p : ℕ × α) : ℕ × α :=
  (n+p.1,p.2)

-- The first two fields are the number of extra leading zeros and
-- the first positive left digit minus one. Such a marker is always
-- present on entry to EL. Normalize the unary-marker case in O(1)
-- arithmetic, then consume the head token or return to CR.
def a12ELscan : List ℕ → ℕ → ℕ → List ℕ → ℕ × A12CRPoint
  | [],r,v,L => (1,⟨0,[],a12ELword r v L⟩)
  | x::K,r,v,L =>
    let (a,d,c) := a12ELnorm x r v L
    a12CostAdd c (match a with
      | 0 => (1,⟨K.headD 0,K.drop 1,a12ELword d v L⟩)
      | 1 => a12CostAdd 2 (a12ELscan K (d+1) v L)
      | 2 => a12CostAdd 7 (a12ELscan K 0 0 (List.replicate d 0 ++ (v+1)::L))
      | a+3 => (8+4*(d+1),⟨0,1::List.replicate (d+1) 1 ++ a::K,v::L⟩))

private theorem a12ELscan_sound (K : List ℕ) (r v : ℕ) (L : List ℕ) :
    ReachesIn target (a12ELscan K r v L).1
      (tok_EL K [] (a12ELword r v L))
      (a12PointCfg (a12ELscan K r v L).2) := by
  simp only [a12PointCfg_eq]
  induction K generalizing r v L with
  | nil =>
    simp only [a12ELscan]
    rw [a12ELblank]
    exact a12c_EL_0_cons 0 [] [] (a12ELword r v L)
  | cons x K ih =>
    have hN := a12ELnorm_sound x r v K L
    rcases hnorm : a12ELnorm x r v L with ⟨a,d,c⟩
    rw [hnorm] at hN
    simp only [a12ELscan,hnorm,a12CostAdd]
    rcases a with _ | _ | _ | a
    · exact ReachesIn.trans hN (a12ELzero K (a12ELword d v L))
    · have h1 := a12c_EL_1 K [] (a12ELword d v L)
      exact ReachesIn.trans hN (ReachesIn.trans h1 (ih (d+1) v L))
    · have h1 := a12c_EL_2 K [] (List.replicate d 0 ++ (v+1)::L)
      exact ReachesIn.trans hN (ReachesIn.trans h1 (ih 0 0 (List.replicate d 0 ++ (v+1)::L)))
    · have h1 := a12c_EL_add3 a K [] (a12ELword d v L)
      have h2 := a12cDRsweep (d+1) (a::K) ((v+1)::L)
      have h3 := a12c_DR_succ (List.replicate (d+1) 1 ++ a::K) [] v L
      have h := ReachesIn.trans h1 (ReachesIn.trans h2 h3)
      have hc : 5+(4*(d+1)+3) = 8+4*(d+1) := by omega
      rw [hc] at h
      exact ReachesIn.trans hN h

/-- Decompose a left stack as zeros followed by an optional positive digit.
The digit in the optional pair is its value minus one. -/
def a12SplitZeros : List ℕ → ℕ × Option (ℕ × List ℕ)
  | [] => (0,none)
  | 0::L =>
    let p := a12SplitZeros L
    (p.1+1,p.2)
  | (v+1)::L => (0,some (v,L))

private theorem a12SplitZeros_sound (L : List ℕ) :
    L = List.replicate (a12SplitZeros L).1 0 ++
      (match (a12SplitZeros L).2 with
       | none => []
       | some (v,T) => (v+1)::T) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases a with
    | zero =>
      simp only [a12SplitZeros,List.replicate_succ,List.cons_append]
      exact congrArg (List.cons 0) ih
    | succ a => rfl

-- DR has fixed head token 2. K is the tail behind it.
def a12DRreturn (K L : List ℕ) : ℕ × A12CRPoint :=
  let (z,p) := a12SplitZeros L
  match p with
  | some (v,T) => (4*z+3,⟨0,1::List.replicate z 1 ++ K,v::T⟩)
  | none => a12CostAdd (6*z+8) (a12ELscan K z 0 [])

private theorem a12DRreturn_sound (K L : List ℕ) :
    ReachesIn target (a12DRreturn K L).1
      (tok_DR (2::K) [] L) (a12PointCfg (a12DRreturn K L).2) := by
  simp only [a12PointCfg_eq]
  have hL := a12SplitZeros_sound L
  rcases hs : a12SplitZeros L with ⟨z,p⟩
  rw [hs] at hL
  cases p with
  | none =>
    simp only [a12DRreturn,hs,a12CostAdd]
    have h1 := a12cDRsweep z K []
    have h2 := a12c_DR_nil_8 (List.replicate z 1 ++ K) []
    have h3 := a12cELsweep z K [0,1]
    rw [a12_rep_push 0 z [1]] at h3
    have h := ReachesIn.trans h1 (ReachesIn.trans h2 h3)
    have hc : 4*z+(8+2*z) = 6*z+8 := by omega
    rw [hc] at h
    rw [hL]
    have hs := a12ELscan_sound K z 0 []
    simp only [a12PointCfg_eq,a12ELword] at hs
    exact ReachesIn.trans h hs
  | some p =>
    rcases p with ⟨v,T⟩
    simp only [a12DRreturn,hs]
    rw [hL]
    have h1 := a12cDRsweep z K ((v+1)::T)
    simp only [List.cons_append] at h1
    have hh := ReachesIn.trans h1 (a12c_DR_succ (List.replicate z 1 ++ K) [] v T)
    simpa only [Nat.zero_add,List.cons_append] using hh

def a12Live (c : ℕ) (p : ℕ × A12CRPoint) : ℕ × Option A12CRPoint :=
  (c+p.1,some p.2)

-- Exact arithmetic, on arbitrary finite lists. The executable run-length
-- implementation is a representation refinement, not a separate dynamics.
def a12CRCostStep (s : A12CRPoint) : ℕ × Option A12CRPoint :=
  let k := s.headMinusOne
  let K := s.rightTail
  match s.left with
  | [] =>
    match k with
    | 0 => a12Live 9 (a12ELscan K 0 0 [])
    | k+1 => a12Live 21 (a12ELscan (k::K) 1 0 [])
  | 0::L => (2,some ⟨k+2,K,L⟩)
  | 1::[] => a12Live 33 (a12ELscan ((k+1)::K) 2 0 [])
  | 1::0::L => (5,some ⟨0,(k+4)::K,L⟩)
  | 1::1::[] => a12Live 25 (a12ELscan ((k+1)::K) 1 0 [])
  | 1::1::c::L => a12Live 25 (a12ELscan ((k+1)::K) 1 (c+1) L)
  | 1::(v+2)::L => a12Live 15 (a12DRreturn (1::(k+1)::K) (v::L))
  | (v+2)::L => (2,none)

/-- Every macro has a positive exact primitive count. A live output is
a CR configuration; a terminal output includes the literal source halt. -/
theorem a12CRCostStep_sound (s : A12CRPoint) :
    match a12CRCostStep s with
    | (n,some t) => 0<n ∧ ReachesIn target n (a12PointCfg s) (a12PointCfg t)
    | (n,none) => ∃ q, ReachesIn target n (a12PointCfg s) q ∧ (step target q).isNone := by
  simp only [a12PointCfg_eq]
  rcases s with ⟨k,K,L⟩
  cases L with
  | nil =>
    cases k with
    | zero =>
      simp only [a12CRCostStep,a12Live]
      have hs := a12ELscan_sound K 0 0 []
      simp only [a12PointCfg_eq,a12ELword] at hs
      exact ⟨by omega,ReachesIn.trans (a12c_CR_1_nil_9 K []) hs⟩
    | succ k =>
      simp only [a12CRCostStep,a12Live]
      have hs := a12ELscan_sound (k::K) 1 0 []
      simp only [a12PointCfg_eq,a12ELword] at hs
      exact ⟨by omega,ReachesIn.trans (a12c_CR_add2_nil_21 k K []) hs⟩
  | cons a L =>
    rcases a with _ | _ | a
    · simp only [a12CRCostStep]
      refine ⟨by decide,?_⟩
      have h := a12c_CR_zero (k+1) K [] L
      have hk : k+1+2 = k+2+1 := by omega
      rw [hk] at h
      exact h
    · cases L with
      | nil =>
        simp only [a12CRCostStep,a12Live]
        have hs := a12ELscan_sound ((k+1)::K) 2 0 []
        simp only [a12PointCfg_eq,a12ELword] at hs
        exact ⟨by omega,ReachesIn.trans (a12c_CR_1_nil_33 (k+1) K []) hs⟩
      | cons b L =>
        rcases b with _ | _ | b
        · simp only [a12CRCostStep]
          exact ⟨by decide,a12c_CR_1_0 (k+1) K [] L⟩
        · cases L with
          | nil =>
            simp only [a12CRCostStep,a12Live]
            have hs := a12ELscan_sound ((k+1)::K) 1 0 []
            simp only [a12PointCfg_eq,a12ELword] at hs
            exact ⟨by omega,ReachesIn.trans (a12c_CR_1_1_nil_25 (k+1) K []) hs⟩
          | cons c L =>
            simp only [a12CRCostStep,a12Live]
            have hs := a12ELscan_sound ((k+1)::K) 1 (c+1) L
            simp only [a12PointCfg_eq,a12ELword] at hs
            exact ⟨by omega,ReachesIn.trans (a12c_CR_1_1_cons_25 (k+1) K [] c L) hs⟩
        · simp only [a12CRCostStep,a12Live]
          have hs := a12DRreturn_sound (1::(k+1)::K) (b::L)
          rw [a12PointCfg_eq] at hs
          exact ⟨by omega,ReachesIn.trans (a12c_CR_1_add2 (k+1) K [] b L) hs⟩
    · simpa only [a12CRCostStep,Nat.add_assoc,show (1:ℕ)+1=2 by decide] using a12c_CR_add2_halts ((k+1)::K) [] a L

def a12CRNext (s : A12CRPoint) : Option A12CRPoint := (a12CRCostStep s).2

def a12Root85 : A12CRPoint := ⟨2,[],[0,0]⟩

theorem a12Root85_exact : ReachesIn target 11 (init []) (a12PointCfg a12Root85) := by
  rw [a12PointCfg_eq]
  change ReachesIn target 11 (init []) (cfg_CR_n_n [(0,0),(0,0)] [(2,0)])
  unfold cfg_CR_n_n
  have hL : encLeft [(2,0)] =
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default := rfl
  have hR : encRight [(0,0),(0,0)] =
      (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default := rfl
  rw [hL,hR]
  a12cexecute 11

theorem a12CRNext_sound (s : A12CRPoint) :
    match a12CRNext s with
    | some t => ReachesPlus target (a12PointCfg s) (a12PointCfg t)
    | none => ∃ q, ReachesStar target (a12PointCfg s) q ∧ (step target q).isNone := by
  have h := a12CRCostStep_sound s
  unfold a12CRNext
  rcases hc : a12CRCostStep s with ⟨n,p⟩
  rw [hc] at h
  cases p with
  | some t => exact h.2.to_plus h.1
  | none =>
    obtain ⟨q,hq,hh⟩ := h
    exact ⟨q,hq.to_star,hh⟩

/-- The actual #85 blank root, not merely a prepared configuration. -/
theorem a12CR_acceleration : IsValidAcceleration target a12Root85 a12PointCfg a12CRNext := by
  refine IsValidAcceleration.of_step a12Root85_exact.to_star ?_
  intro s
  cases h : a12CRNext s <;> simpa only [h] using a12CRNext_sound s

theorem a12Root85_halt_iff : IsHalt target ↔ CollatzHalts a12CRNext a12Root85 :=
  a12CR_acceleration.isHalt_iff

#print axioms a12ELscan_sound
#print axioms a12DRreturn_sound
#print axioms a12CRCostStep_sound
#print axioms a12Root85_exact
#print axioms a12Root85_halt_iff
