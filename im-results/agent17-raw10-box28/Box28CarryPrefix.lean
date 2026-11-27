import Box28CarryGateSource

namespace BB6.Agent17.Box28CarryPrefix
open BB6Coverage BB6.Agent17.Box28CarryFamily BB6.Agent17.Box28CarryGateSource
open BB6.Agent13.Box33BinaryCounter (zeros)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Finite rays with implicit zero tails. This evaluator is used only for
    exact entry prefixes, not as a bounded nonhalting test. -/
structure FinConfig where
  q : C9Pair.Q
  l : List Bool
  a : Bool
  r : List Bool
  deriving DecidableEq

def bits : List Bool → C9Pair.Stream
  | [] => zeros
  | b::bs => C9Pair.push b (bits bs)
def view (c : FinConfig) : C9Pair.Config := ⟨c.q,bits c.l,c.a,bits c.r⟩
@[simp] theorem view_q (c : FinConfig) : (view c).q = c.q := rfl
@[simp] theorem view_a (c : FinConfig) : (view c).a = c.a := rfl

def fRight (q : C9Pair.Q) (w : Bool) (c : FinConfig) : FinConfig :=
  ⟨q,w::c.l,c.r.headD false,c.r.tail⟩
def fLeft (q : C9Pair.Q) (w : Bool) (c : FinConfig) : FinConfig :=
  ⟨q,c.l.tail,c.l.headD false,w::c.r⟩

theorem view_right (q : C9Pair.Q) (w : Bool) (c : FinConfig) :
    view (fRight q w c) = C9Pair.right q w (view c) := by
  rcases c with ⟨s,l,a,r⟩
  cases r <;> rfl
theorem view_left (q : C9Pair.Q) (w : Bool) (c : FinConfig) :
    view (fLeft q w c) = C9Pair.left q w (view c) := by
  rcases c with ⟨s,l,a,r⟩
  cases l <;> rfl

def fAction (e : Option Move) (c : FinConfig) : Option FinConfig :=
  e.map fun mv => if mv.right then fRight (BB6.Agent13.Box33Source.q false mv.next) mv.write c
    else fLeft (BB6.Agent13.Box33Source.q false mv.next) mv.write c

theorem view_action (e : Option Move) (c : FinConfig) :
    (fAction e c).map view = action e (view c) := by
  cases e with
  | none => rfl
  | some mv => cases h : mv.right <;> simp [fAction,action,h,view_right,view_left]

def fstep (two : Bool) (e : Option Move) (c : FinConfig) : Option FinConfig :=
  match c.q,c.a with
  | .A,false => some (fRight .B true c)
  | .A,true => some (fRight (if two then .F else .E) true c)
  | .B,false | .C,false => some (fLeft .C true c)
  | .B,true => none
  | .C,true => some (fLeft .D false c)
  | .D,false => some (fRight .E false c)
  | .D,true => some (fLeft .D true c)
  | .E,false => fAction e c
  | .E,true => some (fRight .F true c)
  | .F,false => some (fRight .A true c)
  | .F,true => some (fRight .C true c)

theorem fstep_view (two : Bool) (e : Option Move) (c : FinConfig) :
    (fstep two e c).map view = stepCore two (fun _ => none) (action e) (view c) := by
  rcases c with ⟨q,l,a,r⟩
  cases q <;> cases a <;>
    simp only [fstep,stepCore,view_q,view_a,Option.map_some,Option.map_none,view_right,view_left,view_action] <;> rfl

/-- Every successful checked step avoids the missing B1 gate. Thus the
    successful prefix is valid for arbitrary B1, not just halt. -/
theorem fstep_sound (two : Bool) (e : Option Move) (b : Gate) (c d : FinConfig)
    (hs : fstep two e c = some d) :
    stepCore two b (action e) (view c) = some (view d) := by
  have h := fstep_view two e c
  rw [hs,Option.map_some] at h
  rcases c with ⟨q,l,a,r⟩
  cases q <;> cases a <;> first | exact h.symm | simp [fstep] at hs

def runFinite (two : Bool) (e : Option Move) : Nat → FinConfig → Option FinConfig
  | 0,c => some c
  | n+1,c => (fstep two e c).bind (runFinite two e n)

theorem runFinite_sound (two : Bool) (e : Option Move) (b : Gate) (n : Nat)
    (c d : FinConfig) (h : runFinite two e n c = some d) :
    runCore two b (action e) n (view c) = some (view d) := by
  induction n generalizing c with
  | zero =>
    have hc : c = d := Option.some.inj h
    subst d
    rfl
  | succ n ih =>
    cases hs : fstep two e c with
    | none => simp [runFinite,hs] at h
    | some c' =>
      have h' : runFinite two e n c' = some d := by
        simpa only [runFinite,hs,Option.bind_some] using h
      rw [runCore,fstep_sound two e b c c' hs,Option.bind_some]
      exact ih c' h'

def fblank : FinConfig := ⟨.A,[],false,[]⟩

theorem sourcePrefix (two : Bool) (m : Machine) (e : Option Move)
    (he : m (4,false) = e) (n : Nat) (d : FinConfig)
    (h : runFinite two e n fblank = some d) :
    runCore two (sourceGate m (1,true)) (sourceGate m (4,false)) n localBlank = some (view d) := by
  have hg : sourceGate m (4,false) = action e := by unfold sourceGate; rw [he]
  rw [hg]
  exact runFinite_sound two e (sourceGate m (1,true)) n fblank d h

#print axioms sourcePrefix
end BB6.Agent17.Box28CarryPrefix
