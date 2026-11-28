import AffinePrefixCover
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321PrunedCover
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321WordGuard
open BB6.Agent2F321RootWord
open BB6.Agent2F321PrefixSparsity
open BB6.Agent2F321DangerCount
open BB6.Agent2F321AffinePrefix

/-- Candidate terminal R from the affine endpoint equality. Only emit it
    if exact division and interval membership hold. -/
def terminalCandidate (f : Affine) (i : Interval) : List Nat :=
  let p := 2*(f.A:Int)+1
  let b := 2*f.B-f.C
  let R := (b/p).toNat
  if b=p*(R:Int) ∧ i.lo≤(R:Int) ∧ (R:Int)≤i.hi then [R] else []

theorem terminal_mem {f i R t} (hm : Matches f R (t+1) t) (hi : In i R) :
    R∈terminalCandidate f i := by
  rcases hm with ⟨hx,hv⟩
  unfold Affine.x at hx
  unfold Affine.v at hv
  have he : 2*f.B-f.C=(2*(f.A:Int)+1)*(R:Int) := by
    rw [Int.add_mul,Int.mul_assoc,Int.one_mul]
    omega
  have hp : 2*(f.A:Int)+1≠0 := by omega
  unfold terminalCandidate
  dsimp only
  have hd : ((2*f.B-f.C)/(2*(f.A:Int)+1)).toNat=R := by
    rw [he,Int.mul_comm,Int.mul_ediv_cancel _ hp]
    simp
  rw [hd]
  unfold In at hi
  simp [he,hi.1,hi.2]

/-- At a singleton interval no further splitting is necessary. In the
    fallback case enumerate the interval at the weighted cutoff. Completeness
    does not require that the survivor actually terminates. -/
def enumerateInterval (i : Interval) : List Nat :=
  let lo := i.lo.toNat
  let hi := i.hi.toNat
  if i.hi<0 then [] else (List.range (hi+1-lo)).map (fun n => lo+n)

theorem mem_enumerate {i R} (hi : In i R) : R∈enumerateInterval i := by
  unfold In at hi
  unfold enumerateInterval
  dsimp only
  have hn : ¬i.hi<0 := by omega
  rw [if_neg hn]
  apply List.mem_map.mpr
  refine ⟨R-i.lo.toNat,List.mem_range.mpr ?_,by omega⟩
  omega

/-- Expand only feasible intervals. Far costs two; High costs one. At the
    first crossing of the budget, retain the entire remaining interval. -/
def explore : Nat → Affine → Interval → List Nat
  | 0, _, i => enumerateInterval i
  | n+1, f, i =>
      if i.hi < max 0 i.lo then []
      else if i.hi ≤ max 0 i.lo then enumerateInterval i
      else terminalCandidate f i ++ explore n f.high (highInterval f i) ++
        explore (n-1) f.far (farInterval f i)

theorem explore_complete {w f i R a d t} (fuel : Nat)
    (hm : Matches f R a d) (hi : In i R) (hw : WordRun w a d (t+1) t) :
    R∈explore fuel f i := by
  induction fuel using Nat.strongRecOn generalizing w f i a d with
  | ind fuel ih =>
      cases fuel with
      | zero => simpa [explore] using mem_enumerate hi
      | succ n =>
          unfold explore
          have hne : ¬i.hi<max 0 i.lo := by unfold In at hi; omega
          rw [if_neg hne]
          split
          · exact mem_enumerate hi
          · cases hw with
            | nil =>
                apply List.mem_append.mpr
                left
                exact List.mem_append.mpr (Or.inl (terminal_mem hm hi))
            | high hg ht =>
                apply List.mem_append.mpr
                left
                apply List.mem_append.mpr
                right
                exact ih n (by omega) (high_matches hm hg) ((high_interval_iff hm).mpr ⟨hi,hg⟩) ht
            | far h1 h2 ht =>
                apply List.mem_append.mpr
                right
                exact ih (n-1) (by omega) (far_matches hm h2) ((far_interval_iff hm).mpr ⟨hi,h2⟩) ht

/-- For a maximal leading High block, immediately test the empty tail and
    take only the Far branch; a further High is not a separate code. -/
def coverAt (h c N : Nat) : List Nat :=
  let f := initial h c
  let i := initialInterval h c N
  terminalCandidate f i ++ explore (h+4) f.far (farInterval f i)

theorem coverAt_complete {h c N R w} (hN : R≤N) (hd : Danger h w R c) : R∈coverAt h c N := by
  rcases danger_iff.mp hd with ⟨hs,t,a,d,hh,hw⟩
  have hm := initial_matches hh
  have hi := initial_interval_iff.mpr ⟨hN,a,d,hh⟩
  unfold coverAt
  rcases hs with rfl | ⟨v,rfl⟩
  · cases hw
    exact List.mem_append.mpr (Or.inl (terminal_mem hm hi))
  · cases hw with
    | far _ hg ht =>
        exact List.mem_append.mpr (Or.inr (explore_complete (h+4) (far_matches hm hg)
          ((far_interval_iff hm).mpr ⟨hi,hg⟩) ht))

def coverThrough (c N : Nat) : Nat → List (Nat×Nat)
  | 0 => (coverAt 0 c N).map (fun R => (R,c))
  | k+1 => coverThrough c N k ++ (coverAt (k+1) c N).map (fun R => (R,c))

theorem coverThrough_complete {h c N R k} (hk : h≤k) (hr : R∈coverAt h c N) :
    (R,c)∈coverThrough c N k := by
  induction k with
  | zero =>
      have he : h=0 := by omega
      subst h
      exact List.mem_map.mpr ⟨R,hr,rfl⟩
  | succ k ih =>
      by_cases he : h=k+1
      · subst h
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨R,hr,rfl⟩))
      · exact List.mem_append.mpr (Or.inl (ih (by omega)))

def prunedCover (k : Nat) : List (Nat×Nat) :=
  coverThrough 1 (2^k) k ++ coverThrough 2 (2^k) k

theorem pruned_cover_complete {k R c} (hk : 2≤k) (hR : R≤2^k) (hd : DangerousAnchor R c) :
    (R,c)∈prunedCover k := by
  rcases hd with ⟨hc,h,w,hd⟩
  have hH : h≤k := by
    rcases danger_iff.mp hd with ⟨_,t,a,d,hh,hw⟩
    exact leadingHigh_le hk hR hc hh
  have hm := coverThrough_complete hH (coverAt_complete hR hd)
  unfold prunedCover
  rcases hc with rfl | rfl
  · exact List.mem_append.mpr (Or.inl hm)
  · exact List.mem_append.mpr (Or.inr hm)

#print axioms explore_complete
#print axioms pruned_cover_complete
end BB6.Agent2F321PrunedCover
