import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39LE4084
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none

/-- Two stacks, nearest cell first; R includes the scanned cell. -/
def A (L R : List Bool) : Z0 := ⟨0,R.headD false :: L,R.tail⟩

theorem rule0 (L R : List Bool) : run0 table 6 (A L ([false,false,false,false] ++ R)) = some (A ([false,true] ++ L) ([true,true] ++ R)) := by rfl
theorem rule1 (L R : List Bool) : run0 table 4 (A L ([false,false,false,true] ++ R)) = some (A ([false,false,true,true] ++ L) R) := by rfl
theorem rule2 (L R : List Bool) : run0 table 6 (A L ([false,false,true,false,false] ++ R)) = some (A ([false,false,true,true] ++ L) ([true] ++ R)) := by rfl
theorem rule3 (L R : List Bool) : run0 table 5 (A L ([false,false,true,false,true] ++ R)) = some (A ([false,true,false,true,true] ++ L) R) := by rfl
theorem bad (L R : List Bool) : run0 table 4 (A L ([false,false,true,true] ++ R)) = none := by rfl
theorem rule5 (L R : List Bool) : run0 table 2 (A L ([false,true] ++ R)) = some (A ([true,true] ++ L) R) := by rfl
theorem rule6 (L R : List Bool) : run0 table 2 (A ([false,false] ++ L) ([true] ++ R)) = some (A L ([false,true,false] ++ R)) := by rfl
theorem rule7 (L R : List Bool) : run0 table 2 (A ([false,true] ++ L) ([true] ++ R)) = some (A L ([true,true,false] ++ R)) := by rfl
theorem rule8 (L R : List Bool) : run0 table 7 (A ([true,false] ++ L) ([true,false] ++ R)) = some (A ([false,false,true] ++ L) ([true] ++ R)) := by rfl
theorem rule9 (L R : List Bool) : run0 table 6 (A ([true,false] ++ L) ([true,true] ++ R)) = some (A ([false,true,false,true] ++ L) R) := by rfl
theorem rule10 (L R : List Bool) : run0 table 3 (A ([true,true] ++ L) ([true] ++ R)) = some (A ([true] ++ L) ([true,false] ++ R)) := by rfl

/-- A certificate language can couple both complete finite stacks.
    Zero padding is explicit; arbitrary untouched tails occur in every rule. -/
structure Closed (K : List Bool → List Bool → Prop) : Prop where
  seed : ∀ n, K (List.replicate n false) (List.replicate n false)
  c0 : ∀ L R, K L ([false,false,false,false] ++ R) → K ([false,true] ++ L) ([true,true] ++ R)
  c1 : ∀ L R, K L ([false,false,false,true] ++ R) → K ([false,false,true,true] ++ L) R
  c2 : ∀ L R, K L ([false,false,true,false,false] ++ R) → K ([false,false,true,true] ++ L) ([true] ++ R)
  c3 : ∀ L R, K L ([false,false,true,false,true] ++ R) → K ([false,true,false,true,true] ++ L) R
  forbid : ∀ L R, ¬ K L ([false,false,true,true] ++ R)
  c5 : ∀ L R, K L ([false,true] ++ R) → K ([true,true] ++ L) R
  c6 : ∀ L R, K ([false,false] ++ L) ([true] ++ R) → K L ([false,true,false] ++ R)
  c7 : ∀ L R, K ([false,true] ++ L) ([true] ++ R) → K L ([true,true,false] ++ R)
  c8 : ∀ L R, K ([true,false] ++ L) ([true,false] ++ R) → K ([false,false,true] ++ L) ([true] ++ R)
  c9 : ∀ L R, K ([true,false] ++ L) ([true,true] ++ R) → K ([false,true,false,true] ++ L) R
  c10 : ∀ L R, K ([true,true] ++ L) ([true] ++ R) → K ([true] ++ L) ([true,false] ++ R)

theorem next {K : List Bool → List Bool → Prop} (h : Closed K)
    (L R : List Bool) (hk : K L R) (hl : 2 ≤ L.length) (hr : 5 ≤ R.length) :
    ∃ k L' R', 0 < k ∧ K L' R' ∧ L.length ≤ L'.length + 5 ∧
      R.length ≤ R'.length + 5 ∧ run0 table k (A L R) = some (A L' R') := by
  cases R with
  | nil => simp at hr
  | cons r0 R =>
    cases r0 with
    | false =>
      cases R with
      | nil => simp at hr
      | cons r1 R =>
        cases r1 with
        | false =>
          cases R with
          | nil => simp at hr
          | cons r2 R =>
            cases r2 with
            | false =>
              cases R with
              | nil => simp at hr
              | cons r3 R =>
                cases r3 with
                | false =>
                  refine ⟨6, ([false,true] ++ L), ([true,true] ++ R), by decide, h.c0 L R hk, ?_, ?_, rule0 L R⟩ <;> simp <;> omega
                | true =>
                  refine ⟨4, ([false,false,true,true] ++ L), R, by decide, h.c1 L R hk, ?_, ?_, rule1 L R⟩ <;> simp <;> omega
            | true =>
              cases R with
              | nil => simp at hr
              | cons r3 R =>
                cases r3 with
                | false =>
                  cases R with
                  | nil => simp at hr
                  | cons r4 R =>
                    cases r4 with
                    | false =>
                      refine ⟨6, ([false,false,true,true] ++ L), ([true] ++ R), by decide, h.c2 L R hk, ?_, ?_, rule2 L R⟩ <;> simp <;> omega
                    | true =>
                      refine ⟨5, ([false,true,false,true,true] ++ L), R, by decide, h.c3 L R hk, ?_, ?_, rule3 L R⟩ <;> simp <;> omega
                | true =>
                  exact False.elim (h.forbid L R hk)
        | true =>
          refine ⟨2, ([true,true] ++ L), R, by decide, h.c5 L R hk, ?_, ?_, rule5 L R⟩ <;> simp <;> omega
    | true =>
      cases L with
      | nil => simp at hl
      | cons l0 L =>
        cases l0 with
        | false =>
          cases L with
          | nil => simp at hl
          | cons l1 L =>
            cases l1 with
            | false =>
              refine ⟨2, L, ([false,true,false] ++ R), by decide, h.c6 L R hk, ?_, ?_, rule6 L R⟩ <;> simp <;> omega
            | true =>
              refine ⟨2, L, ([true,true,false] ++ R), by decide, h.c7 L R hk, ?_, ?_, rule7 L R⟩ <;> simp <;> omega
        | true =>
          cases L with
          | nil => simp at hl
          | cons l1 L =>
            cases l1 with
            | false =>
              cases R with
              | nil => simp at hr
              | cons r1 R =>
                cases r1 with
                | false =>
                  refine ⟨7, ([false,false,true] ++ L), ([true] ++ R), by decide, h.c8 L R hk, ?_, ?_, rule8 L R⟩ <;> simp <;> omega
                | true =>
                  refine ⟨6, ([false,true,false,true] ++ L), R, by decide, h.c9 L R hk, ?_, ?_, rule9 L R⟩ <;> simp <;> omega
            | true =>
              refine ⟨3, ([true] ++ L), ([true,false] ++ R), by decide, h.c10 L R hk, ?_, ?_, rule10 L R⟩ <;> simp <;> omega

/-- n macro epochs need only 5*n cells of finite zero padding per side. -/
theorem epochs {K : List Bool → List Bool → Prop} (h : Closed K)
    (n : Nat) (L R : List Bool) (hk : K L R)
    (hl : 5*n ≤ L.length) (hr : 5*n ≤ R.length) :
    ∃ t z, n ≤ t ∧ run0 table t (A L R) = some z := by
  induction n generalizing L R with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ n ih =>
    obtain ⟨k,L',R',hp,hk',hL,hR,he⟩ := next h L R hk (by omega) (by omega)
    obtain ⟨t,z,ht,hs⟩ := ih L' R' hk' (by omega) (by omega)
    exact ⟨k+t,z,by omega,join0 he hs⟩

private theorem getD_zeros (n i : Nat) :
    (List.replicate n false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_replicate]
  split <;> rfl

open BB6Coverage.Agent50Zipper in
private def seedZ (n : Nat) : Z :=
  ⟨0,0,List.replicate (n+1) false,List.replicate (n-1) false⟩

private theorem seed_project (n : Nat) :
    project (seedZ n) = A (List.replicate n false) (List.replicate n false) := by
  cases n <;> rfl

open BB6Coverage.Agent50Zipper in
private theorem seed_embed (n : Nat) : embed (seedZ n) = blank := by
  unfold embed seedZ blank
  congr 1
  funext x
  unfold atCell
  split <;> exact getD_zeros _ _

/-- Any closed two-stack language establishes original-machine nonhalting,
    for every completion of the one unspecified transition. -/
theorem never_of_closed {K : List Bool → List Bool → Prop}
    (h : Closed K) (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := epochs h n (List.replicate (5*n) false)
    (List.replicate (5*n) false) (h.seed _) (by simp) (by simp)
  have hz : (BB6Coverage.Agent50Zipper.zrun table t (seedZ (5*n))).map project = some z :=
    (run_project table t _).trans ((seed_project _).symm ▸ hr)
  cases he : BB6Coverage.Agent50Zipper.zrun table t (seedZ (5*n)) with
  | none => simp [he] at hz
  | some z' =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound table m hm t _ z' he
    rw [seed_embed,show t=n+(t-n) by omega,run_append] at H
    cases hn : run m n blank with
    | none => simp [hn] at H
    | some c => rfl

#print axioms never_of_closed
