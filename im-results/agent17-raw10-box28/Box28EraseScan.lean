import Box28CarryFamily

namespace BB6.Agent17.Box28EraseScan
open C9Pair
open BB6.Agent17.Box28CarryFamily (Gate pair localBlank)
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def q (s : Bool) : Q := if s then .F else .E
inductive Mark where
  | a (w : Bool)
  | b
  | scan (s w : Bool)
  deriving DecidableEq
structure Params where
  z : Bool → Bool × Bool
  o : Bool → Mark

def markStep (m : Mark) (c : Config) : Config :=
  match m with
  | .a w => right .A w c
  | .b => right .B true c
  | .scan s w => right (q s) w c

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
  | .E,false => some (right (q (p.z false).1) (p.z false).2 x)
  | .F,false => some (right (q (p.z true).1) (p.z true).2 x)
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

def atScan (s : Bool) (l r : Stream) : Config := ⟨q s,l,r 0,pop r⟩
def atLeft (l r : Stream) : Config := ⟨.D,pop l,l 0,r⟩
def ray (n : Nat) (l : Stream) : Stream := rep true n (push false l)
def tail : Stream := pair false true zeros
def root (n : Nat) (l : Stream) : Config := atScan false (push false l) (rep false n tail)

theorem push_ray (w : Bool) (n : Nat) (l : Stream) :
    ∃ m l', push w (ray n l) = ray m l' := by
  cases w
  · exact ⟨0,ray n l,rfl⟩
  · exact ⟨n+1,l,rfl⟩

theorem zero_step (p : Params) (a b c : Gate) (s : Bool) (l u : Stream) :
    stepCore p a b c (atScan s l (push false u)) =
      some (atScan (p.z s).1 (push (p.z s).2 l) u) := by cases s <;> rfl

theorem scan_prefix (p : Params) (a b c : Gate) (n : Nat) (s : Bool) (r : Nat) (l u : Stream) :
    ∃ s' r' l', runCore p a b c n (atScan s (ray r l) (rep false n u)) =
      some (atScan s' (ray r' l') u) := by
  induction n generalizing s r l with
  | zero => exact ⟨s,r,l,rfl⟩
  | succ n ih =>
    obtain ⟨r',l',he⟩ := push_ray (p.z s).2 r l
    obtain ⟨s'',r'',l'',hr⟩ := ih (p.z s).1 r' l'
    exact ⟨s'',r'',l'',by rw [runCore,rep,zero_step,Option.bind_some,he,hr]⟩

theorem drift (p : Params) (a b c : Gate) (t : Nat) (s : Bool) (l : Stream) :
    runCore p a b c t (atScan s l zeros) ≠ none := by
  induction t generalizing s l with
  | zero => simp [runCore]
  | succ t ih =>
    have h := zero_step p a b c s l zeros
    rw [zero_push] at h
    rw [runCore,h,Option.bind_some]
    exact ih _ _

theorem rewind (p : Params) (a b c : Gate) (r : Nat) (l u : Stream) :
    runCore p a b c (r+1) (atLeft (ray r l) u) =
      some (atScan false (push false l) (rep false r u)) := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih =>
    rw [show r+1+1=1+(r+1) by omega,runCore_add]
    change (some (atLeft (ray r l) (push false u))).bind _ = _
    rw [Option.bind_some,ih,rep_add false r 1] <;> rfl

theorem mark_step (p : Params) (a b c : Gate) (s : Bool) (l : Stream) :
    stepCore p a b c (atScan s l (push true zeros)) =
      some (markStep (p.o s) (atScan s l (push true zeros))) := by cases s <;> rfl

theorem turnA (p : Params) (a b c : Gate) (w : Bool) (s : Bool) (r : Nat) (l : Stream) :
    runCore p a b c 3 (markStep (.a w) (atScan s (ray r l) (push true zeros))) =
      some (atLeft (push w (ray r l)) tail) := by rfl

theorem turnB (p : Params) (a b c : Gate) (s : Bool) (r : Nat) (l : Stream) :
    runCore p a b c 2 (markStep .b (atScan s (ray r l) (push true zeros))) =
      some (atLeft (ray r l) tail) := by rfl

theorem progress (p : Params) (a b c : Gate) (n : Nat) (l : Stream) :
    (∃ t m l', 0<t ∧ runCore p a b c t (root n l) = some (root m l')) ∨
    (∀ t, runCore p a b c t (root n l) ≠ none) := by
  obtain ⟨s,r,l',h⟩ := scan_prefix p a b c (n+1) false 0 l (push true zeros)
  rw [rep_add false n 1] at h
  change runCore p a b c (n+1) (root n l) = some (atScan s (ray r l') (push true zeros)) at h
  have hmark : runCore p a b c (n+1+1) (root n l) =
      some (markStep (p.o s) (atScan s (ray r l') (push true zeros))) := by
    rw [runCore_add,h,Option.bind_some]
    simp [runCore,mark_step]
  cases hm : p.o s with
  | a w =>
    left
    obtain ⟨r',l'',he⟩ := push_ray w r l'
    refine ⟨n+2+3+(r'+1),r',l'',by omega,?_⟩
    rw [runCore_add,runCore_add,show n+2=n+1+1 by omega,hmark,hm,Option.bind_some,
      turnA,he,Option.bind_some,rewind]
    rfl
  | b =>
    left
    refine ⟨n+2+2+(r+1),r,l',by omega,?_⟩
    rw [runCore_add,runCore_add,show n+2=n+1+1 by omega,hmark,hm,Option.bind_some,
      turnB,Option.bind_some,rewind]
    rfl
  | scan s' w =>
    right; intro t ht
    rw [hm] at hmark
    change runCore p a b c (n+1+1) (root n l) =
      some (atScan s' (push w (ray r l')) zeros) at hmark
    by_cases hle : t≤n+1+1
    · rw [show n+1+1=t+(n+1+1-t) by omega,runCore_add,ht] at hmark; contradiction
    · rw [show t=(n+1+1)+(t-(n+1+1)) by omega,runCore_add,hmark,Option.bind_some] at ht
      exact drift p a b c _ _ _ ht

theorem never_root (p : Params) (a b c : Gate) (t n : Nat) (l : Stream) :
    runCore p a b c t (root n l) ≠ none := by
  induction t using Nat.strongRecOn generalizing n l with
  | ind t ih =>
    rcases progress p a b c n l with ⟨u,m,l',hu,hr⟩|h
    · intro ht
      by_cases hle : t≤u
      · rw [show u=t+(u-t) by omega,runCore_add,ht] at hr; contradiction
      · rw [show t=u+(t-u) by omega,runCore_add,hr,Option.bind_some] at ht
        exact ih _ (by omega) m l' ht
    · exact h t

theorem init (p : Params) (a b c : Gate) :
    runCore p a b c 4 localBlank = some (root 0 zeros) := by
  simp [runCore,stepCore,localBlank,root,atScan,q,tail,pair,rep,left,right]

theorem never_blank (p : Params) (a b c : Gate) (t : Nat) :
    runCore p a b c t localBlank ≠ none := by
  intro ht
  have hi := init p a b c
  by_cases hle : t≤4
  · rw [show 4=t+(4-t) by omega,runCore_add,ht] at hi; contradiction
  · rw [show t=4+(t-4) by omega,runCore_add,hi,Option.bind_some] at ht
    exact never_root p a b c _ 0 zeros ht

#print axioms never_blank
end BB6.Agent17.Box28EraseScan
