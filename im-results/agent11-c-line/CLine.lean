import Std

namespace BB6CLine

def nextC : Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | (a,k,1) => some (a,k+1,0)
  | (_,_,2) => none
  | (a,k,3) => some (a,k+2,1)
  | (0,k,0) => some (1,0,2*k+2)
  | (1,0,0) => some (5,0,1)
  | (1,k+1,0) => some (2,2,2*k+1)
  | (a+2,k,0) => some (a,1,2*k+1)
  | (0,k,d+4) => if k%2=0 then some (4*(k/2)+2,2,d+1)
                    else some (4*(k/2)+5,0,d+4)
  | (a+1,k,d+4) => some (a,k+1,d+3)

def rankC (s:Nat×Nat×Nat):Nat := s.1+2*s.2.1+s.2.2

def Wing (s:Nat×Nat×Nat):Prop := s.2.2=s.1+5 ∧ (s.1+s.2.1)%2=0

def Thin (s:Nat×Nat×Nat):Prop := ∃ j, s=(0,2*j,4*j+10)

def Special (s:Nat×Nat×Nat):Prop := s=(1,4,0)

inductive Reach : Nat×Nat×Nat → Prop where
 | init : Reach (5,0,1)
 | next (s t:Nat×Nat×Nat) : Reach s → nextC s=some t → Reach t

/-- Every nonhalting transition preserves or increases the weighted rank. -/
theorem rank_mono {s t:Nat×Nat×Nat} (h:nextC s=some t):rankC s≤rankC t:=by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t; simp [rankC] <;> omega
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t; simp [rankC] <;> omega
      · simp only [nextC,Option.some.injEq] at h
        subst t; simp [rankC] <;> omega
    · simp only [nextC,Option.some.injEq] at h
      subst t; simp [rankC] <;> omega
  · simp only [nextC,Option.some.injEq] at h
    subst t; simp [rankC] <;> omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t; simp [rankC] <;> omega
  · rcases a with _|a
    · dsimp [nextC] at h
      by_cases he:k%2=0
      · simp only [he,↓reduceIte,Option.some.injEq] at h
        subst t; simp [rankC] <;> omega
      · simp only [he,↓reduceIte,Option.some.injEq] at h
        subst t; simp [rankC] <;> omega
    · simp only [nextC,Option.some.injEq] at h
      subst t; simp [rankC] <;> omega

private theorem advance0:nextC (5,0,1)=some (5,1,0):=by decide
private theorem advance1:nextC (5,1,0)=some (3,1,3):=by decide
private theorem advance2:nextC (3,1,3)=some (3,3,1):=by decide

/-- Exact first three states give rank >=10 thereafter, excluding (1,4,0). -/
theorem front_invariant (s:Nat×Nat×Nat)(h:Reach s):
  s=(5,0,1) ∨ s=(5,1,0) ∨ s=(3,1,3) ∨ 10≤rankC s:=by
  induction h with
  | init => exact Or.inl rfl
  | next p q hp ht ih =>
      rcases ih with h0|h1|h2|h3
      · subst p
        rw [advance0] at ht
        have : q=(5,1,0):=Option.some.inj ht.symm
        exact Or.inr (Or.inl this)
      · subst p
        rw [advance1] at ht
        have : q=(3,1,3):=Option.some.inj ht.symm
        exact Or.inr (Or.inr (Or.inl this))
      · subst p
        rw [advance2] at ht
        have : q=(3,3,1):=Option.some.inj ht.symm
        exact Or.inr (Or.inr (Or.inr (by simp [this,rankC])))
      · exact Or.inr (Or.inr (Or.inr (Nat.le_trans h3 (rank_mono ht))))

theorem special_unreachable (h:Reach (1,4,0)):False:=by
  have hi:=front_invariant (1,4,0) h
  rcases hi with hh|hh|hh|hh <;> simp [rankC] at hh

/-- Inbound edge analysis for the halting wing: every entry comes from
    within the wing, the exceptional small state, or a thin infinite line. -/
theorem wing_predecessor (s t:Nat×Nat×Nat)
    (h:nextC s=some t)(ht:Wing t):
    Wing s ∨ Special s ∨ Thin s := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t
      rcases ht with ⟨he,hp⟩
      simp only [Wing] at *
      omega
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t
        rcases ht with ⟨he,hp⟩
        simp only [Wing] at *
        omega
      · simp only [nextC,Option.some.injEq] at h
        subst t
        rcases ht with ⟨he,hp⟩
        right;left
        change 2*k+1=2+5 at he
        have hk:k=3:=by omega
        subst k
        rfl
    · simp only [nextC,Option.some.injEq] at h
      subst t
      rcases ht with ⟨he,hp⟩
      simp only [Wing] at *
      omega
  · simp only [nextC,Option.some.injEq] at h
    subst t
    rcases ht with ⟨he,hp⟩
    simp only [Wing] at *
    omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t
    rcases ht with ⟨he,hp⟩
    simp only [Wing] at *
    omega
  · rcases a with _|a
    · dsimp [nextC] at h
      by_cases he:k%2=0
      · simp only [he,↓reduceIte,Option.some.injEq] at h
        subst t
        rcases ht with ⟨hc,hpar⟩
        right;right
        dsimp [Thin]
        refine ⟨k/2,?_⟩
        have heq:k=2*(k/2):=by omega
        change d+1=4*(k/2)+2+5 at hc
        clear hpar
        simp only [Prod.mk.injEq]
        simp only [true_and]
        omega
      · simp only [he,↓reduceIte,Option.some.injEq] at h
        subst t
        rcases ht with ⟨hc,hpar⟩
        simp only [Wing] at *
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      left
      dsimp [Wing] at *
      rcases ht with ⟨hc,hpar⟩
      constructor <;> omega

/-- Every blank-start orbit point in the halting wing has a prior visit to
    the one-parameter family Thin. -/
theorem reached_wing_has_line (s:Nat×Nat×Nat) (hs:Reach s) (hw:Wing s):
    ∃ p, Reach p ∧ Thin p := by
  induction hs with
  | init => simp [Wing] at hw
  | next p q hp ht ih =>
      rcases wing_predecessor p q ht hw with hwing | hspecial | hthin
      · exact ih hwing
      · have hfalse : False := by
          change p=(1,4,0) at hspecial
          subst p
          exact special_unreachable hp
        exact False.elim hfalse
      · exact ⟨p,hp,hthin⟩

/-- Under the high-sector decrement branch, every wing point necessarily
    reaches an even-indexed halting guard. -/
theorem wing_reaches_guard (a k:Nat) (h:Reach (a,k,a+5))
    (hp:(a+k)%2=0): ∃ j, Reach (0,2*j,5) := by
  induction a generalizing k with
  | zero =>
      refine ⟨k/2,?_⟩
      have he:k=2*(k/2):=by omega
      rw [he] at h
      simpa only [Nat.zero_add] using h
  | succ a ih =>
      have hn:nextC (a+1,k,a+1+5)=some (a,k+1,a+5):= by
        have h1:a+1+5=(a+2)+4:=by omega
        have h2:(a+2)+3=a+5:=by omega
        rw [h1,←h2]
        rfl
      have hr:Reach (a,k+1,a+5):=Reach.next _ _ h hn
      apply ih (k+1) hr
      omega

private theorem line_enters_wing (j:Nat):
  nextC (0,2*j,4*j+10)=some (4*j+2,2,4*j+7) := by
  simp [nextC] <;> omega

/-- Thin-family entry is sufficient to reach the halt guard. -/
theorem reached_line_has_guard (p:Nat×Nat×Nat) (hr:Reach p)(ht:Thin p):
    ∃ j, Reach (0,2*j,5) := by
  obtain ⟨j,hp⟩:=ht
  subst p
  have hn:=line_enters_wing j
  have hh:Reach (4*j+2,2,4*j+7):=Reach.next _ _ hr hn
  have hpar:((4*j+2)+2)%2=0:=by omega
  have he:4*j+7=(4*j+2)+5:=by omega
  rw [he] at hh
  exact wing_reaches_guard (4*j+2) 2 hh hpar

/-- An exact blank-start equivalence: reaching any even-indexed c=5 guard
    is the same as reaching the thinner diagonal line c=2k+10 (k even). -/
theorem guard_iff_thin :
  (∃ j, Reach (0,2*j,5)) ↔ (∃ p, Reach p ∧ Thin p) := by
  constructor
  · rintro ⟨j,hr⟩
    apply reached_wing_has_line (0,2*j,5) hr
    dsimp [Wing]
    constructor <;> omega
  · rintro ⟨p,hr,ht⟩
    exact reached_line_has_guard p hr ht

/-- Rank and the exact first orbit states exclude the empty all-zero state. -/
theorem empty_unreachable (h:Reach (0,0,0)):False:=by
  have hi:=front_invariant (0,0,0) h
  rcases hi with hh|hh|hh|hh <;> simp [rankC] at hh

/-- An incoming transition to c=2 starts either at the all-zero counter
    triple, or at a c=5 zero-a state with even middle counter. -/
theorem incoming_halting_layer (s t:Nat×Nat×Nat)
    (h:nextC s=some t)(hc:t.2.2=2):
    s=(0,0,0) ∨ ∃ j, s=(0,2*j,5):=by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t
      change 2*k+2=2 at hc
      left
      have hk:k=0:=by omega
      subst k
      rfl
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t
        simp at hc
      · simp only [nextC,Option.some.injEq] at h
        subst t
        change 2*k+1=2 at hc
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      change 2*k+1=2 at hc
      omega
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp at hc
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp at hc
  · rcases a with _|a
    · dsimp [nextC] at h
      by_cases he:k%2=0
      · simp only [he,↓reduceIte,Option.some.injEq] at h
        subst t
        change d+1=2 at hc
        right
        refine ⟨k/2,?_⟩
        have hk:k=2*(k/2):=by omega
        have hd:d=1:=by omega
        subst d
        change (0,k,5) = (0,2*(k/2),5)
        exact congrArg (fun x:Nat => (0,x,5)) hk
      · simp only [he,↓reduceIte,Option.some.injEq] at h
        subst t
        change d+4=2 at hc
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      change d+3=2 at hc
      omega

/-- An accelerated trajectory from the actual blank-tape entry reaches
    the stopping layer precisely when it hits the diagonal thin family. -/
theorem halting_layer_iff_thin :
    (∃ s, Reach s ∧ s.2.2=2) ↔
    (∃ j, Reach (0,2*j,4*j+10)) := by
  constructor
  · rintro ⟨s,hs,hc⟩
    cases hs with
    | init => simp at hc
    | next p s hp ht =>
        rcases incoming_halting_layer p s ht hc with hzero | hguard
        · subst p
          exact False.elim (empty_unreachable hp)
        · obtain ⟨j,hp⟩:=hguard
          subst p
          have hl:=guard_iff_thin.mp ⟨j,hp⟩
          rcases hl with ⟨q,hq,⟨n,hn⟩⟩
          subst q
          exact ⟨n,hq⟩
  · rintro ⟨j,hr⟩
    have hg:∃ k, Reach (0,2*k,5):=by
      apply guard_iff_thin.mpr
      exact ⟨(0,2*j,4*j+10),hr,⟨j,rfl⟩⟩
    obtain ⟨k,hk⟩:=hg
    have hn:nextC (0,2*k,5)=some (4*k+2,2,2):=by
      simp [nextC]
    exact ⟨(4*k+2,2,2),Reach.next _ _ hk hn,rfl⟩

/-- Under the published accelerated semantics, the call itself stops exactly
    on c=2. -/
theorem nextC_none_iff (s:Nat×Nat×Nat):
    nextC s=none ↔ s.2.2=2 := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp [nextC]
    · rcases k with _|k
      · simp [nextC]
      · simp [nextC]
    · simp [nextC]
  · simp [nextC]
  · simp [nextC]
  · simp [nextC]
  · rcases a with _|a
    · dsimp [nextC]
      by_cases he:k%2=0
      · simp [he]
      · simp [he]
    · change (some (a,k+1,d+3) : Option (Nat×Nat×Nat))=none ↔ d+4=2
      simp

/-- Complete stopping characterization for the true blank-entry accelerator:
    a successful blank-origin trajectory eventually calls none iff it
    reaches a counter triple (0,2j,4j+10) for some j. -/
theorem stops_iff_thin :
    (∃ s, Reach s ∧ nextC s=none) ↔
    (∃ j, Reach (0,2*j,4*j+10)) := by
  rw [← halting_layer_iff_thin]
  constructor
  · rintro ⟨s,hr,hs⟩
    exact ⟨s,hr,(nextC_none_iff s).mp hs⟩
  · rintro ⟨s,hr,hs⟩
    exact ⟨s,hr,(nextC_none_iff s).mpr hs⟩

#print axioms BB6CLine.guard_iff_thin
#print axioms BB6CLine.halting_layer_iff_thin
#print axioms BB6CLine.stops_iff_thin

end BB6CLine
