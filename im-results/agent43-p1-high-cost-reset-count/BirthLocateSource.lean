import BirthLocate
import ReverseBlockSource

namespace BB6.Agent43BirthLocate
open BB6.Agent9BatchCarry (Interior Walk)
open BB6.Agent9FoldedProbe
open BB6.Agent45ReverseBlock (fast source_fast_iff)

def strictParent (q k z : Nat) : Option Nat :=
  (fast (q+k) k (2^k*z)).bind fun c =>
    if 1≤c ∧ c+3≤q then some (fold q c) else none

/-- The exact fitted reverse query returns the unique folded start. -/
theorem strictParent_iff (q k z a : Nat) (hz : Canon (q+k) z)
    (hf : 2^(k+1)≤q+k) : strictParent q k z=some a ↔ FoldedWalk q a k z := by
  unfold strictParent
  cases he : fast (q+k) k (2^k*z) with
  | none =>
    simp only [Option.bind,reduceCtorEq,false_iff]
    intro hw
    obtain ⟨c,hc,_⟩ := folded_lift_end hw
    have hp := (source_fast_iff q c k z (walk_start hc) hf).2 hc
    simp [he] at hp
  | some c =>
    simp only [Option.bind]
    split <;> rename_i hc
    · simp only [Option.some.injEq]
      constructor
      · intro ha
        have hw := (source_fast_iff q c k z hc hf).1 he
        exact ⟨c,z,hw,ha,hz.2⟩
      · intro hw
        exact unique_start ⟨c,z,(source_fast_iff q c k z hc hf).1 he,rfl,hz.2⟩ hw
    · simp only [reduceCtorEq,false_iff]
      intro hw
      obtain ⟨d,hd,_⟩ := folded_lift_end hw
      have hp := (source_fast_iff q d k z (walk_start hd) hf).2 hd
      rw [he,Option.some.injEq] at hp
      subst d
      exact hc (walk_start hd)

/-- Binary search with a proved true lower endpoint and false upper endpoint. -/
def boundary (f : Nat → Bool) (lo hi : Nat) : Nat :=
  if _h : lo+1<hi then
    let m := (lo+hi)/2
    if f m then boundary f m hi else boundary f lo m
  else lo
termination_by hi-lo
decreasing_by all_goals omega

theorem boundary_spec (f : Nat → Bool) (lo hi : Nat)
    (hlt : lo<hi) (hl : f lo=true) (hh : f hi=false) :
    lo≤boundary f lo hi ∧ boundary f lo hi<hi ∧
      f (boundary f lo hi)=true ∧ f (boundary f lo hi+1)=false := by
  rw [boundary]
  split <;> rename_i h
  · dsimp only
    split <;> rename_i hm
    · have hb := boundary_spec f ((lo+hi)/2) hi (by omega) hm hh
      exact ⟨by omega,hb.2.1,hb.2.2⟩
    · have hm' : f ((lo+hi)/2)=false := by cases h : f ((lo+hi)/2) <;> simp_all
      have hb := boundary_spec f lo ((lo+hi)/2) (by omega) hl hm'
      exact ⟨hb.1,by omega,hb.2.2⟩
  · exact ⟨Nat.le_refl _,hlt,hl,by rw [show lo+1=hi by omega]; exact hh⟩
termination_by hi-lo
decreasing_by all_goals omega

/-- Fitted suffix lengths are tested using the same two-candidate query
    as the C++ sweep. The zero-length suffix is included. -/
def testSuffix (F z k : Nat) : Bool := (strictParent (F-k) k z).isSome

theorem testSuffix_iff (F z k : Nat) (hk : k≤F) (hz : Canon F z)
    (hf : 2^(k+1)≤F) : testSuffix F z k=true ↔ HasSuffix F z k := by
  have hsum : F-k+k=F := Nat.sub_add_cancel hk
  have hz' : Canon (F-k+k) z := by rw [hsum]; exact hz
  have hf' : 2^(k+1)≤F-k+k := by rw [hsum]; exact hf
  unfold testSuffix HasSuffix
  constructor
  · intro h
    cases he : strictParent (F-k) k z with
    | none => simp [he] at h
    | some a => exact ⟨a,(strictParent_iff _ _ _ _ hz' hf').1 he⟩
  · rintro ⟨a,ha⟩
    rw [(strictParent_iff _ _ _ _ hz' hf').2 ha]
    rfl

def locate (F z k : Nat) : Nat := boundary (testSuffix F z) 0 k

/-- The binary search returns the precise boundary between the longest
    legal suffix and its immediately longer impossible suffix. -/
theorem locate_spec (F z k : Nat) (hk : 0<k) (hq : k≤F)
    (hz : Canon F z) (hf : 2^(k+1)≤F)
    (hn : ¬ HasSuffix F z k) :
    locate F z k<k ∧ HasSuffix F z (locate F z k) ∧
      ¬ HasSuffix F z (locate F z k+1) := by
  have fit (i : Nat) (hi : i≤k) : 2^(i+1)≤F :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hf
  have h0 : HasSuffix F z 0 := by
    have hw : Walk F z 0 z := Walk.nil F z hz.1
    exact ⟨z,z,z,by simpa using hw,by simpa using hz.2,by simpa using hz.2⟩
  have hyes := (testSuffix_iff F z 0 (by omega) hz (fit 0 (by omega))).2 h0
  have hno : testSuffix F z k=false := by
    cases he : testSuffix F z k
    · rfl
    · exact False.elim (hn ((testSuffix_iff F z k hq hz hf).1 he))
  have hb := boundary_spec (testSuffix F z) 0 k hk hyes hno
  change 0≤locate F z k ∧ locate F z k<k ∧ testSuffix F z (locate F z k)=true ∧ testSuffix F z (locate F z k+1)=false at hb
  refine ⟨hb.2.1,(testSuffix_iff F z _ (by omega) hz (fit _ (by omega))).1 hb.2.2.1,?_⟩
  intro hs
  have ht := (testSuffix_iff F z _ (by omega) hz (fit _ (by omega))).2 hs
  rw [hb.2.2.2] at ht
  contradiction

/-- Thus every failed fitted block returns an actual maximal folded class,
    with the clock recovered without enumerating intervening starts. -/
theorem locate_center (F z k : Nat) (hk : 0<k) (hq : k≤F)
    (hz : Canon F z) (hf : 2^(k+1)≤F)
    (hn : ¬ HasSuffix F z k) :
    FoldedWalk (F-locate F z k) ((F-locate F z k-2)/2) (locate F z k) z := by
  obtain ⟨hlt,hy,hn'⟩ := locate_spec F z k hk hq hz hf hn
  let l := locate F z k
  have hq' : F-(l+1)+1=F-l := by dsimp [l]; omega
  have hq'' : F-(l+1)-1=F-l-2 := by omega
  have hs : (∃ a, FoldedWalk (F-(l+1)+1) a l z) ∧
      ¬(∃ a, FoldedWalk (F-(l+1)) a (l+1) z) := by
    rw [hq']
    exact ⟨hy,hn'⟩
  have hw := (first_failure_iff (F-(l+1)) l z).2 hs
  rw [hq',hq''] at hw
  exact hw

/-- The failure list contains clocks, not all in-block carry sets. -/
def lostClocks (F k : Nat) (ends : List Nat) : List Nat :=
  ends.filterMap fun z => if testSuffix F z k then none else some (F-locate F z k)

/-- Every birth strictly above the lower block boundary is found exactly
    by the failed terminal queries. Deduplicating this list is harmless. -/
theorem mem_lostClocks (F k b : Nat) (ends : List Nat)
    (hk : 0<k) (hq : k≤F) (hf : 2^(k+1)≤F)
    (hc : ∀ z∈ends, Canon F z) (hb : F-k<b) (hb' : b≤F) :
    b∈lostClocks F k ends ↔
      ∃ z∈ends, FoldedWalk b ((b-2)/2) (F-b) z := by
  unfold lostClocks
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨z,hz,he⟩
    have hno : testSuffix F z k=false := by
      cases h : testSuffix F z k <;> simp_all
    have hn : ¬HasSuffix F z k := by
      intro ht
      have h := (testSuffix_iff F z k hq (hc z hz) hf).2 ht
      rw [hno] at h; contradiction
    have hl := locate_spec F z k hk hq (hc z hz) hf hn
    have heq : F-locate F z k=b := by simpa [hno] using he
    have hlen : locate F z k=F-b := by omega
    have hw := locate_center F z k hk hq (hc z hz) hf hn
    rw [heq,hlen] at hw
    exact ⟨z,hz,hw⟩
  · rintro ⟨z,hz,hw⟩
    have hclock : b-1+1=b := by omega
    have hcenter : b-1-1=b-2 := by omega
    have hw' : FoldedWalk (b-1+1) ((b-1-1)/2) (F-b) z := by rw [hclock,hcenter]; exact hw
    have hbound := (first_failure_iff (b-1) (F-b) z).1 hw'
    have hy : HasSuffix F z (F-b) := by
      unfold HasSuffix
      rw [show F-(F-b)=b by omega]
      simpa only [hclock] using hbound.1
    have hn : ¬ HasSuffix F z (F-b+1) := by
      unfold HasSuffix
      rw [show F-(F-b+1)=b-1 by omega]
      exact hbound.2
    have hnk : ¬ HasSuffix F z k := by
      intro h; exact hn (suffix_mono F z k (F-b+1) (by omega) hq h)
    have hl := locate_spec F z k hk hq (hc z hz) hf hnk
    have heq : locate F z k=F-b := by
      by_cases h : locate F z k < F-b
      · exfalso
        exact hl.2.2 (suffix_mono F z (F-b) (locate F z k+1) (by omega) (by omega) hy)
      · by_cases h' : F-b < locate F z k
        · exfalso
          exact hn (suffix_mono F z (locate F z k) (F-b+1) (by omega) (by omega) hl.2.1)
        · omega
    have hno : testSuffix F z k=false := by
      cases he : testSuffix F z k
      · rfl
      · exact False.elim (hnk ((testSuffix_iff F z k hq (hc z hz) hf).1 he))
    exact ⟨z,hz,by simp [hno,heq,show F-(F-b)=b by omega]⟩

/-- Complete exact skipped-birth interface for a common-clock live cover.
    The lower boundary b=F-k is deliberately handled by the next block. -/
theorem lostClocks_live (F k j b : Nat) (ends : List Nat)
    (hk : 0<k) (hq : k≤F) (hf : 2^(k+1)≤F)
    (hb : F-k<b) (hb' : b≤F) (hb4 : 4≤b)
    (he : LiveCover F j ends) :
    b∈lostClocks F k ends ↔ ∃ z, Walk b ((b-2)/2) (F-b+j) z := by
  have hc : ∀ z∈ends, Canon F z := by
    intro z hz; obtain ⟨w,hw⟩ := (he z).1 hz; exact folded_start hw
  rw [mem_lostClocks F k b ends hk hq hf hc hb hb']
  have hclock : b+(F-b)=F := by omega
  constructor
  · rintro ⟨z,hz,hw⟩
    obtain ⟨w,ht⟩ := (he z).1 hz
    have ht' : FoldedWalk (b+(F-b)) z j w := by rw [hclock]; exact ht
    obtain ⟨w',hw',_⟩ := folded_lift_start (folded_append hw ht')
    exact ⟨w',hw'⟩
  · rintro ⟨w,hw⟩
    have hcanon := center_canon b hb4
    have hw' : FoldedWalk b ((b-2)/2) (F-b+j) (fold (b+(F-b+j)) w) :=
      ⟨_,w,hw,hcanon.2,rfl⟩
    obtain ⟨z,hz,ht⟩ := folded_split hw'
    rw [hclock] at ht
    exact ⟨z,(he z).2 ⟨_,ht⟩,hz⟩

#print axioms strictParent_iff
#print axioms boundary_spec
#print axioms testSuffix_iff
#print axioms locate_spec
#print axioms locate_center
#print axioms mem_lostClocks
#print axioms lostClocks_live
end BB6.Agent43BirthLocate
