import Box28CarryFamily
namespace BB6.Agent17.Box28EraseScan
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push)
open BB6.Agent17.Box28CarryFamily (Gate localBlank)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

def q (s : Bool) : Q := if s then .F else .E
inductive ZeroMove where
  | scan (s w : Bool)
  | dR (w : Bool)
  | dL
  deriving DecidableEq
inductive Mark where
  | a (w : Bool)
  | b
  | scan (s w : Bool)
  | dR (w : Bool)
  | dL (w : Bool)
  deriving DecidableEq
structure Params where
  z : Bool → ZeroMove
  o : Bool → Mark

def zeroStep (m : ZeroMove) (c : Config) : Config :=
  match m with
  | .scan s w => right (q s) w c
  | .dR w => right .D w c
  | .dL => left .D false c

def markStep (m : Mark) (c : Config) : Config :=
  match m with
  | .a w => right .A w c
  | .b => right .B true c
  | .scan s w => right (q s) w c
  | .dR w => right .D w c
  | .dL w => left .D w c

def stepCore (p : Params) (a b c : Gate) (x : Config) : Option Config :=
  match x.q,x.a with
  | .A,false => some (right .B true x)
  | .A,true => a x
  | .B,false => some (left .C true x)
  | .B,true => b x
  | .C,false => c x
  | .C,true => some (left .D false x)
  | .D,false => some (right .E false x)
  | .D,true => some (left .D false x)
  | .E,false => some (zeroStep (p.z false) x)
  | .F,false => some (zeroStep (p.z true) x)
  | .E,true => some (markStep (p.o false) x)
  | .F,true => some (markStep (p.o true) x)

def runCore (p : Params) (a b c : Gate) : Nat → Config → Option Config
  | 0,x => some x
  | n+1,x => (stepCore p a b c x).bind (runCore p a b c n)

theorem runCore_add (p : Params) (a b c : Gate) (m n : Nat) (x : Config) :
    runCore p a b c (m+n) x = (runCore p a b c m x).bind (runCore p a b c n) := by
  induction m generalizing x with
  | zero => simp [runCore]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [runCore]
    cases stepCore p a b c x <;> simp [ih]

/-- At most one marker in the rightward stream. -/
inductive Sparse : Stream → Prop where
  | blank : Sparse zeros
  | marker : Sparse (push true zeros)
  | zero {s : Stream} : Sparse s → Sparse (push false s)

theorem sparse_pop (s : Stream) (h : Sparse s) : Sparse (pop s) := by
  cases h with
  | blank => exact .blank
  | marker => exact .blank
  | zero h => exact h

theorem sparse_true (s : Stream) (h : Sparse s) (hh : s 0=true) : pop s=zeros := by
  cases h with
  | blank => contradiction
  | marker => rfl
  | zero h => contradiction

theorem sparse_bit (w : Bool) : Sparse (push w zeros) := by
  cases w
  · exact .zero .blank
  · exact .marker

/-- State-sensitive one-marker invariant, with no constraint on the
    farther-left tape. A1, B1 and C0 are never queried. -/
def Good (x : Config) : Prop :=
  match x.q with
  | .A => x.a=false ∧ x.r=zeros
  | .B => x.a=false ∧ x.r=zeros ∧ x.l 0=true
  | .C => x.a=true ∧ Sparse x.r
  | .D => Sparse x.r
  | .E | .F => Sparse (push x.a x.r)

theorem good_right_scan (s w : Bool) (x : Config) (h : Sparse x.r) :
    Good (right (q s) w x) := by
  cases s <;> simpa [Good,right,q] using h

theorem good_zero (m : ZeroMove) (x : Config) (h : Sparse x.r) : Good (zeroStep m x) := by
  cases m with
  | scan s w => exact good_right_scan s w x h
  | dR w => exact sparse_pop _ h
  | dL => exact .zero h

theorem good_marker (m : Mark) (x : Config) (h : x.r=zeros) : Good (markStep m x) := by
  rcases x with ⟨s,l,a,r⟩
  change r=zeros at h
  subst r
  cases m with
  | a w => exact ⟨rfl,rfl⟩
  | b => exact ⟨rfl,rfl,rfl⟩
  | scan s w => exact good_right_scan s w _ .blank
  | dR w => exact .blank
  | dL w => exact sparse_bit w

theorem good_scan_zero (m : ZeroMove) (s : Q) (l r : Stream) (h : Sparse (push false r)) :
    Good (zeroStep m ⟨s,l,false,r⟩) := by
  apply good_zero
  simpa using sparse_pop _ h

theorem good_scan_marker (m : Mark) (s : Q) (l r : Stream) (h : Sparse (push true r)) :
    Good (markStep m ⟨s,l,true,r⟩) := by
  apply good_marker
  simpa using sparse_true _ h rfl

theorem progress (p : Params) (a b c : Gate) (x : Config) (hx : Good x) :
    ∃ y, stepCore p a b c x=some y ∧ Good y := by
  rcases x with ⟨s,l,u,r⟩
  cases s <;> cases u <;> simp only [Good] at hx
  case A.false =>
    obtain ⟨_,hr⟩ := hx
    subst r
    exact ⟨_,rfl,⟨rfl,rfl,rfl⟩⟩
  case A.true => exact False.elim (Bool.noConfusion hx.1)
  case B.false =>
    obtain ⟨_,hr,hl⟩ := hx
    subst r
    exact ⟨_,rfl,⟨hl,.marker⟩⟩
  case B.true => exact False.elim (Bool.noConfusion hx.1)
  case C.false => exact False.elim (Bool.noConfusion hx.1)
  case C.true => exact ⟨_,rfl,.zero hx.2⟩
  case D.false => exact ⟨_,rfl,good_right_scan false false _ hx⟩
  case D.true => exact ⟨_,rfl,.zero hx⟩
  case E.false => exact ⟨_,rfl,good_scan_zero (p.z false) _ _ _ hx⟩
  case E.true => exact ⟨_,rfl,good_scan_marker (p.o false) _ _ _ hx⟩
  case F.false => exact ⟨_,rfl,good_scan_zero (p.z true) _ _ _ hx⟩
  case F.true => exact ⟨_,rfl,good_scan_marker (p.o true) _ _ _ hx⟩

theorem never_good (p : Params) (a b c : Gate) (t : Nat) (x : Config) (hx : Good x) :
    runCore p a b c t x ≠ none := by
  induction t generalizing x with
  | zero => simp [runCore]
  | succ t ih =>
    obtain ⟨y,hs,hy⟩ := progress p a b c x hx
    rw [runCore,hs,Option.bind_some]
    exact ih y hy

theorem never_blank (p : Params) (a b c : Gate) (t : Nat) :
    runCore p a b c t localBlank ≠ none := never_good p a b c t _ ⟨rfl,rfl⟩

#print axioms never_blank
end BB6.Agent17.Box28EraseScan
