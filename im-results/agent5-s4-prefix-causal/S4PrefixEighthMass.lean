import S4PrefixSeven
import S4PrefixContractionTransfer
import S4Toggle
import Lean.Elab.Tactic.Omega

namespace S4PrefixEighthMass

open S4Power S4Octet S4Toggle S4PrefixCausal S4PrefixSeven
open S4PrefixContraction S4PrefixContractionTransfer

set_option maxRecDepth 25000
set_option maxHeartbeats 0

/-- Unweighted stack mass: each digit contributes its value plus one cell. -/
def stackMass (xs : List Nat) : Nat := xs.sum + xs.length

private theorem H_empty_mass (a : Nat) :
    ∀ U, H a [] = some U → stackMass U = a + 3 := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
      intro U h
      by_cases he : a % 2 = 0
      · by_cases hzero : a = 0
        · simp [H, he, hzero] at h
        · have hU : [a/2+2, a/2-1] = U := by
            simpa [H, he, hzero] using h
          subst U
          simp [stackMass]
          omega
      · by_cases hsmall : a ≤ 1
        · simp [H, he, hsmall] at h
        · have hlt : a/2 < a := by omega
          cases hrec : H (a/2) [] with
          | none => simp [H, he, hsmall, hrec] at h
          | some V =>
              have hU : a/2 :: V = U := by
                simpa [H, he, hsmall, hrec] using h
              subst U
              have hV := ih (a/2) hlt V hrec
              simp [stackMass] at hV ⊢
              omega

/-- Every successful H-drain adds exactly three units of stack mass. -/
theorem H_mass (a : Nat) : ∀ L U, H a L = some U →
    stackMass U = a + stackMass L + 3 := by
  intro L
  induction L generalizing a with
  | nil =>
      intro U h
      exact H_empty_mass a U h
  | cons b S ih =>
      intro U h
      by_cases he : a % 2 = 0
      · have hU : (a/2+2)::(b+a/2)::S = U := by
          simpa [H, he] using h
        subst U
        simp [stackMass]
        omega
      · cases hrec : H (b+a/2+1) S with
        | none => simp [H, he, hrec] at h
        | some V =>
            have hU : a/2 :: V = U := by
              simpa [H, he, hrec] using h
            subst U
            have hV := ih (b+a/2+1) V hrec
            simp [stackMass] at hV ⊢
            omega

/-- A successful G-drain adds c+2 units of stack mass. -/
theorem G_mass (c : Nat) (T U : List Nat)
    (h : G c T = some U) : stackMass U = stackMass T + c + 2 := by
  cases T with
  | nil =>
      have hm := H_mass (c-1) [] U h
      simp [stackMass] at hm ⊢
      omega
  | cons b S =>
      have hm := H_mass (b+c) S U h
      simp [stackMass] at hm ⊢
      omega

/-- The three drains in one P-return add 511+292+221 = 1024 mass. -/
theorem P_mass (T U : List Nat) (h : P T = some U) :
    stackMass U = stackMass T + 1024 := by
  cases h509 : G 509 T with
  | none => simp [P, h509] at h
  | some V =>
      cases h290 : G 290 V with
      | none => simp [P, h509, h290] at h
      | some W =>
          cases h219 : G 219 W with
          | none => simp [P, h509, h290, h219] at h
          | some U' =>
              have hU : U' = U := by
                simpa [P, h509, h290, h219] using h
              subst U
              have h1 := G_mass 509 T V h509
              have h2 := G_mass 290 V W h290
              have h3 := G_mass 219 W U' h219
              simp [stackMass] at h1 h2 h3 ⊢
              omega

/-- Exact mass drift along every successful n-step P-orbit. -/
theorem prun_mass (n : Nat) : ∀ T U, prun n T = some U →
    stackMass U = stackMass T + 1024*n := by
  induction n with
  | zero =>
      intro T U h
      simp [prun] at h
      subst U
      simp [stackMass]
  | succ n ih =>
      intro T U h
      cases hrun : prun n T with
      | none => simp [prun, hrun] at h
      | some V =>
          have hp : P V = some U := by
            simpa [prun, hrun] using h
          have hm1 := ih T V hrun
          have hm2 := P_mass V U hp
          omega

/-- The root seed has mass 2247, so its successful P-orbit has exact linear mass. -/
theorem root_mass (n : Nat) (U : List Nat)
    (h : prun n seed = some U) :
    stackMass U = 2247 + 1024*n := by
  have hm := prun_mass n seed U h
  simp [stackMass, seed] at hm ⊢
  omega

def s159 : List Nat := [280,398,1255,2487,10896,6084,15142,26739,80194,21578]

def s175 : List Nat := [280,398,1257,5173,7805,6592,19004,19579,99771,21578]

def s191 : List Nat := [280,398,1255,2484,3252,7314,13930,19053,128277,21578]

def s207 : List Nat := [280,398,1257,5171,3977,6065,14073,16563,72420,46999,23499,11749,5874,2939,2936]

def s223 : List Nat := [280,398,1255,2487,10900,18212,14073,16563,72420,46999,23499,11749,5874,2939,2936]

def s239 : List Nat := [280,398,1257,5173,7808,19248,29825,16563,72420,46999,23499,11749,5874,2939,2936]

def s255 : List Nat := [280,398,1255,2484,3254,13297,37282,38686,72420,46999,23499,11749,5874,2939,2936]

def s271 : List Nat := [280,398,1257,5171,3979,10462,53087,38686,72420,46999,23499,11749,5874,2939,2936]

def s287 : List Nat := [280,398,1255,2487,10898,11305,32196,35441,53933,100930,23499,11749,5874,2939,2936]

def s303 : List Nat := [280,398,1257,5173,7809,28090,32196,35441,53933,100930,23499,11749,5874,2939,2936]

def s319 : List Nat := [280,398,1255,2484,3253,9554,28065,51749,41960,71445,47472,29613,35485,2939,2936]

def s335 : List Nat := [280,398,1257,5171,3978,8136,21225,36487,39226,110669,47472,29613,35485,2939,2936]

def s337 : List Nat := [283,906,982,3490,3734,5935,13580,25036,64260,110669,47472,29613,35485,2939,2936]

theorem chunk143_159 : prun 16 S4PrefixSeven.state143 = some s159 := by
  simp [prun, P, G, H.eq_1, H.eq_2, S4PrefixSeven.state143, s159]

theorem chunk159_175 : prun 16 s159 = some s175 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s159, s175]

theorem chunk175_191 : prun 16 s175 = some s191 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s175, s191]

theorem chunk191_207 : prun 16 s191 = some s207 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s191, s207]

theorem chunk207_223 : prun 16 s207 = some s223 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s207, s223]

theorem chunk223_239 : prun 16 s223 = some s239 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s223, s239]

theorem chunk239_255 : prun 16 s239 = some s255 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s239, s255]

theorem chunk255_271 : prun 16 s255 = some s271 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s255, s271]

theorem chunk271_287 : prun 16 s271 = some s287 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s271, s287]

theorem chunk287_303 : prun 16 s287 = some s303 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s287, s303]

theorem chunk303_319 : prun 16 s303 = some s319 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s303, s319]

theorem chunk319_335 : prun 16 s319 = some s335 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s319, s335]

theorem chunk335_337 : prun 2 s335 = some s337 := by
  simp [prun, P, G, H.eq_1, H.eq_2, s335, s337]

/-- Composition of successful P-orbit segments. -/
private theorem prun_add_local (m n : Nat) (xs : List Nat) :
    prun (m+n) xs = (prun m xs).bind (prun n) := by
  induction n with
  | zero => simp [prun]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [prun, ih]
      cases h : prun m xs with
      | none => simp [h]
      | some U => simp [h, prun]

private theorem prun_compose {m n : Nat} {T U V : List Nat}
    (h1 : prun m T = some U) (h2 : prun n U = some V) :
    prun (m+n) T = some V := by
  rw [prun_add_local, h1]
  simpa using h2

/-- The actual root survives to macro-step 337, with the displayed full stack. -/
theorem seed337 : prun 337 seed = some s337 := by
  have h0 := seed143
  have h1 := chunk143_159
  have h2 := chunk159_175
  have h3 := chunk175_191
  have h4 := chunk191_207
  have h5 := chunk207_223
  have h6 := chunk223_239
  have h7 := chunk239_255
  have h8 := chunk255_271
  have h9 := chunk271_287
  have h10 := chunk287_303
  have h11 := chunk303_319
  have h12 := chunk319_335
  have h13 := chunk335_337
  have h01 := prun_compose h0 h1
  have h02 := prun_compose h01 h2
  have h03 := prun_compose h02 h3
  have h04 := prun_compose h03 h4
  have h05 := prun_compose h04 h5
  have h06 := prun_compose h05 h6
  have h07 := prun_compose h06 h7
  have h08 := prun_compose h07 h8
  have h09 := prun_compose h08 h9
  have h10' := prun_compose h09 h10
  have h11' := prun_compose h10' h11
  have h12' := prun_compose h11' h12
  have h13' := prun_compose h12' h13
  have hsteps : 143+ 16 + 16 + 16 + 16 + 16 + 16 + 16 + 16 + 16 + 16 + 16 + 16 + 2 = 337 := by omega
  simpa [hsteps] using h13'

def cycle8Start : List Nat := cycle7 ++ [25036]
def tail337 : List Nat := [64260,110669,47472,29613,35485,2939,2936]

/-- Conditional exact prefix evolution from the formally verified step-337 state. -/
theorem root_eight_prefix (n : Nat) (U : List Nat)
    (h : prun (337+n) seed = some U) :
    U.take 8 = prefixRun n cycle8Start := by
  have hstate : prun n s337 = some U := by
    rw [prun_add_local, seed337] at h
    simpa using h
  have hfull : prun n (cycle8Start ++ tail337) = some U := by
    simpa [s337, cycle8Start, tail337, cycle7] using hstate
  exact prun_prefix n cycle8Start tail337 U hfull

/-- The seventh-prefix cycle's phase 17 is the explicit forcing key for digit eight. -/
def key8 : List Nat := [282,964,974,2637,13534,14347,13580]

theorem key8_phase : prefixRun 17 cycle7 = key8 := by decide

theorem key8_advance :
    pp key8 = [280,396,742,2600,7697,11022,12301] := by decide

/-- At this phase, the appended eighth digit is halved up to an additive constant. -/
theorem forcing17 (v : Nat) :
    (pp (key8 ++ [v]))[7]! ≤ v/2 + 6153 := by
  by_cases h : v % 2 = 0
  · have hpar : (v + 12302) % 2 = 0 := by omega
    simp [pp, gp, hp, key8, hpar]
    omega
  · have hpar : (v + 12302) % 2 = 1 := by omega
    simp [pp, gp, hp, key8, hpar]
    omega

theorem forcing17_append (v : Nat) :
    ∃ w, pp (key8 ++ [v]) = pp key8 ++ [w] ∧ w ≤ v/2 + 6153 := by
  obtain ⟨w, hw⟩ := pp_append_one key8 v
  refine ⟨w, hw, ?_⟩
  have hb := forcing17 v
  rw [hw, key8_advance] at hb
  simpa using hb

/-- One 5120-step return contracts the appended eighth digit. -/
def K8 : Nat := toll 17 cycle7 + 6153 + toll 5102 key8

theorem K8_eq : K8 = 1407397607 := by decide

theorem block5120_contraction (v : Nat) :
    ∃ w, prefixRun 5120 (cycle7 ++ [v]) = cycle7 ++ [w] ∧
      w ≤ v/2 + K8 := by
  have hnum : 17+1+5102 = 5120 := by omega
  have hcycle : prefixRun (17+1+5102) cycle7 = cycle7 := by
    simpa [hnum] using spin5120
  have hforce : ∀ v, ∃ w,
      pp (prefixRun 17 cycle7 ++ [v]) =
        pp (prefixRun 17 cycle7) ++ [w] ∧ w ≤ v/2 + 6153 := by
    intro v
    rw [key8_phase]
    exact forcing17_append v
  obtain ⟨w, hw, hb⟩ :=
    cyclic_extension_contraction cycle7 17 5102 6153 hcycle hforce v
  refine ⟨w, ?_, ?_⟩
  · simpa [hnum] using hw
  · simpa [K8, key8_phase] using hb

def return8 (v : Nat) : Nat := (prefixRun 5120 (cycle7 ++ [v])).getLast!

theorem block5120_shape (v : Nat) :
    prefixRun 5120 (cycle7 ++ [v]) = cycle7 ++ [return8 v] := by
  obtain ⟨w, hw, _hb⟩ := block5120_contraction v
  have hlast : return8 v = w := by
    unfold return8
    rw [hw]
    simp [cycle7]
  simpa [hlast] using hw

theorem return8_bound (v : Nat) : return8 v ≤ v/2 + K8 := by
  obtain ⟨w, hw, hb⟩ := block5120_contraction v
  have hlast : return8 v = w := by
    simp [return8, hw, cycle7]
  simpa [hlast] using hb

def return8Iter : Nat → Nat → Nat
  | 0, v => v
  | n+1, v => return8 (return8Iter n v)

/-- Every sequence of 5120-step returns stays in a finite explicit interval. -/
theorem return8Iter_bound (n v : Nat) :
    return8Iter n v ≤ max v (2*K8) := by
  let B := max v (2*K8)
  have hvB : v ≤ B := by exact Nat.le_max_left _ _
  have hKB : 2*K8 ≤ B := by exact Nat.le_max_right _ _
  induction n with
  | zero => simpa [return8Iter, B] using hvB
  | succ n ih =>
      have hs := return8_bound (return8Iter n v)
      have hn : return8 (return8Iter n v) ≤ B := by omega
      simpa [return8Iter, B] using hn

theorem prefixRun_blocks (n v : Nat) :
    prefixRun (5120*n) (cycle7 ++ [v]) =
      cycle7 ++ [return8Iter n v] := by
  induction n with
  | zero => simp [prefixRun, return8Iter]
  | succ n ih =>
      have hmul : 5120*(n+1) = 5120*n+5120 := by omega
      rw [hmul, prefixRun_add, ih]
      simpa [return8Iter] using block5120_shape (return8Iter n v)

/-- If the actual root survives to a block boundary, its eighth digit is bounded. -/
theorem root_eighth_block_bound (k : Nat) (U : List Nat)
    (h : prun (337+5120*k) seed = some U) :
    U.take 8 = cycle7 ++ [return8Iter k 25036] ∧
      return8Iter k 25036 ≤ max 25036 (2*K8) := by
  have hroot := root_eight_prefix (5120*k) U h
  have hblocks :
      prefixRun (5120*k) cycle8Start =
        cycle7 ++ [return8Iter k 25036] := by
    simpa [cycle8Start] using prefixRun_blocks k 25036
  constructor
  · exact hroot.trans hblocks
  · exact return8Iter_bound k 25036

theorem root_eighth_block_bound_numeric (k : Nat) (U : List Nat)
    (h : prun (337+5120*k) seed = some U) :
    U.take 8 = cycle7 ++ [return8Iter k 25036] ∧
      return8Iter k 25036 ≤ 2814795214 := by
  obtain ⟨hprefix, hbound⟩ := root_eighth_block_bound k U h
  exact ⟨hprefix, by simpa [K8_eq] using hbound⟩

/-- The mass law remains exact at the same conditional future block boundaries. -/
theorem root_mass_at_block (k : Nat) (U : List Nat)
    (h : prun (337+5120*k) seed = some U) :
    stackMass U = 2247 + 1024*(337+5120*k) :=
  root_mass (337+5120*k) U h

end S4PrefixEighthMass
