import StreakWord

namespace BB6.Agent12PackedStreakWord
open BB6.Agent12WordBlock BB6.Agent12StreakWord

/-- A compositional summary; all streak information is independent of parity. -/
structure Summary where
  count : Nat
  pre : Nat
  post : Nat
  maxRun : Nat
  maxShift : Nat
  allDirect : Bool
  positive : Bool
  even : Coeff
  odd : Coeff
  deriving Repr, DecidableEq

def choose (s : Summary) (o : Nat) : Coeff := if o=0 then s.even else s.odd

def endDirect (s : Summary) (d : Nat) : Nat :=
  if s.allDirect then d+s.count else s.post

def guard (s : Summary) (R D d : Nat) : Prop :=
  s.positive=true ∧ s.maxShift≤R ∧ s.maxRun≤D ∧ d+s.pre≤D

instance (s : Summary) (R D d : Nat) : Decidable (guard s R D d) := by unfold guard; infer_instance

def joinCoeff (l r : Coeff) : Coeff :=
  ⟨r.p*l.p,r.p*l.q+r.q,r.p*l.c-r.q*(l.w:Int)+r.c,l.w+r.w⟩

def joinFor (l r : Summary) (o : Nat) : Coeff :=
  let v := choose l o
  joinCoeff v (choose r ((o+v.w)%2))

def join (l r : Summary) : Summary :=
  ⟨l.count+r.count,
    if l.allDirect then l.count+r.pre else l.pre,
    if r.allDirect then l.post+r.count else r.post,
    max (max l.maxRun r.maxRun) (l.post+r.pre),
    max l.maxShift r.maxShift,
    l.allDirect && r.allDirect,l.positive && r.positive,
    joinFor l r 0,joinFor l r 1⟩

def one (r : Nat) : Summary :=
  let d := if r=1 then 1 else 0
  ⟨1,d,d,d,r,r==1,decide (1≤r),coeff [r] 0,coeff [r] 1⟩

def Summarizes (v : Summary) (rs : List Nat) : Prop :=
  v.count=rs.length ∧ v.pre≤v.count ∧
  (∀ s : State, run rs s=applyCoeff (choose v (s.m%2)) s) ∧
  (∀ d : Nat, endStreak d rs=endDirect v d) ∧
  (∀ R D d : Nat, guard v R D d → boundedWord R D d rs=true)

private theorem run_append (xs ys : List Nat) (s : State) :
    run (xs++ys) s=run ys (run xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (step x s)

private theorem endStreak_append (xs ys : List Nat) (d : Nat) :
    endStreak d (xs++ys)=endStreak (endStreak d xs) ys := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih => exact ih (advance d x)

private theorem bounded_append (R D d : Nat) (xs ys : List Nat)
    (hx : boundedWord R D d xs=true)
    (hy : boundedWord R D (endStreak d xs) ys=true) :
    boundedWord R D d (xs++ys)=true := by
  induction xs generalizing d with
  | nil => exact hy
  | cons x xs ih =>
    have h : (d≤D ∧ 1≤x ∧ x≤R) ∧ boundedWord R D (advance d x) xs=true := by
      simpa [boundedWord] using hx
    have hh := ih (advance d x) h.2 hy
    simpa [boundedWord,h.1] using hh

private theorem apply_joinCoeff (l r : Coeff) (s : State) :
    applyCoeff (joinCoeff l r) s=applyCoeff r (applyCoeff l s) := by
  simp only [joinCoeff,applyCoeff]
  push_cast
  congr 1 <;> grind

private theorem choose_join (l r : Summary) (m : Nat) :
    choose (join l r) (m%2)=joinFor l r (m%2) := by
  have h : m%2=0 ∨ m%2=1 := by omega
  rcases h with h|h <;> simp [choose,join,h]

private theorem join_guard (l r : Summary) (R D d : Nat)
    (hprel : l.pre≤l.count) (h : guard (join l r) R D d) :
    guard l R D d ∧ guard r R D (endDirect l d) := by
  simp only [guard,join,Bool.and_eq_true,Nat.max_le] at h
  obtain ⟨⟨hl,hr⟩,⟨hR1,hR2⟩,⟨⟨hD1,hD2⟩,hcross⟩,hpre⟩ := h
  cases hld : l.allDirect
  · simp only [hld,Bool.false_eq_true,ite_false] at hpre
    exact ⟨⟨hl,hR1,hD1,hpre⟩,⟨hr,hR2,hD2,by simpa [endDirect,hld] using hcross⟩⟩
  · simp only [hld,ite_true] at hpre
    exact ⟨⟨hl,hR1,hD1,by omega⟩,⟨hr,hR2,hD2,by simp [endDirect,hld]; omega⟩⟩

private theorem end_join (l r : Summary) (d : Nat) :
    endDirect (join l r) d=endDirect r (endDirect l d) := by
  cases hl : l.allDirect <;> cases hr : r.allDirect <;>
    simp [endDirect,join,hl,hr,Nat.add_assoc]

theorem one_sound (r : Nat) : Summarizes (one r) [r] := by
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [one]; split <;> omega
  · intro s
    rw [run_eq_coeff]
    have h : s.m%2=0 ∨ s.m%2=1 := by omega
    rcases h with h|h <;> simp [one,choose,h]
  · intro d
    by_cases h : r=1 <;> simp [one,endStreak,advance,endDirect,h]
  · intro R D d h
    by_cases hr : r=1
    · subst r
      simp [guard,one] at h
      simp [boundedWord,advance,show d≤D by omega,h.1,show d+1≤D by omega]
    · simp [guard,one,hr] at h
      simp [boundedWord,advance,hr,h.1,h.2.1,h.2.2]

theorem join_sound (l r : Summary) (xs ys : List Nat)
    (hl : Summarizes l xs) (hr : Summarizes r ys) : Summarizes (join l r) (xs++ys) := by
  obtain ⟨hlc,hlp,hlr,hle,hlg⟩ := hl
  obtain ⟨hrc,hrp,hrr,hre,hrg⟩ := hr
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [join,hlc,hrc]
  · simp [join]; split <;> omega
  · intro s
    rw [run_append,hlr,hrr,choose_join]
    unfold joinFor
    rw [apply_joinCoeff]
    have h : (applyCoeff (choose l (s.m%2)) s).m%2=(s.m%2+(choose l (s.m%2)).w)%2 := by
      simp [applyCoeff,Nat.add_mod]
    rw [h]
  · intro d
    rw [endStreak_append,hle,hre,end_join]
  · intro R D d h
    obtain ⟨h1,h2⟩ := join_guard l r R D d hlp h
    apply bounded_append R D d xs ys (hlg R D d h1)
    rw [hle]
    exact hrg R D _ h2

/-- Low-order tokens occur first in chronological order. The split point is
    fixed by depth, so evaluation is balanced and never constructs the list. -/
def packedWord (width : Nat) : Nat → Nat → List Nat
  | 0,code => [code % 2^width]
  | depth+1,code =>
    let b := 2^(width*2^depth)
    packedWord width depth (code%b) ++ packedWord width depth (code/b)

def packedSummary (width : Nat) : Nat → Nat → Summary
  | 0,code => one (code % 2^width)
  | depth+1,code =>
    let b := 2^(width*2^depth)
    join (packedSummary width depth (code%b)) (packedSummary width depth (code/b))

theorem packed_sound (width depth code : Nat) :
    Summarizes (packedSummary width depth code) (packedWord width depth code) := by
  induction depth generalizing code with
  | zero => exact one_sound _
  | succ depth ih =>
    simp only [packedSummary,packedWord]
    exact join_sound _ _ _ _ (ih _) (ih _)

/-- A packed block is checked by summary arithmetic, with a proof of the
    full word semantics but without evaluating the expanded list. -/
theorem packed_certificate (next : Nat × Nat → Option (Nat × Nat)) (law : EdgeLaw next)
    (width depth code R D : Nat) (s t : State)
    (hg : guard (packedSummary width depth code) R D 0)
    (hm : 8*2^R≤s.m) (hd : 40*2^D≤s.m) (hp : consistent s)
    (he : applyCoeff (choose (packedSummary width depth code) (s.m%2)) s=t)
    (hx : 0≤t.a) (hg' : 20*(2:Int)^endDirect (packedSummary width depth code) 0≤gap t+4) :
    runNext next (packedSummary width depth code).count (some (decode s))=some (decode t) := by
  obtain ⟨hc,_,hr,he',hg0⟩ := packed_sound width depth code
  have hw := hg0 R D 0 hg
  have hrun := hr s
  rw [he] at hrun
  rw [←hrun] at hx hg' ⊢
  rw [←he'] at hg'
  rw [hc]
  exact (long_word_certificate next law R D 0 _ s hw hm hd hp hx hg').2.2

theorem packed_count (width depth code : Nat) : (packedSummary width depth code).count=2^depth := by
  induction depth generalizing code with
  | zero => rfl
  | succ depth ih => simp [packedSummary,join,ih,Nat.pow_succ]; omega

#print axioms one_sound
#print axioms join_sound
#print axioms packed_sound
#print axioms packed_certificate
#print axioms packed_count
end BB6.Agent12PackedStreakWord
