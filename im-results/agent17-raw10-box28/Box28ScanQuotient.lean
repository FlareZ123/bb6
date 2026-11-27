import Box28CarryFamily

namespace BB6.Agent17.Box28ScanQuotient
open C9Pair
open BB6.Agent17.Box28CarryFamily (Gate Droot Eroot pair localBlank)
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false

/-- The three right-writing scan states: 0=A, 1=E, 2=F.
    A0 is the sole exit from the rightward scan. -/
abbrev S := Fin 3
structure Params where
  a : S
  e : S
  f : S
  ze : S
  zf : S
  deriving DecidableEq
def state (s : S) : Q := if s=0 then .A else if s=1 then .E else .F
def one (p : Params) (s : S) : S := if s=0 then p.a else if s=1 then p.e else p.f
def zero (p : Params) (s : S) : S := if s=1 then p.ze else p.zf
def iter (f : S → S) : Nat → S → S
  | 0,s => s
  | n+1,s => iter f n (f s)
theorem iter_add (f : S → S) (n m : Nat) (s : S) :
    iter f (n+m) s = iter f m (iter f n s) := by
  induction n generalizing s with
  | zero => simp [iter]
  | succ n ih => rw [Nat.succ_add,iter,iter,ih]

/-- Number of additional zeros consumed before A, or a perpetual right sweep. -/
def zeroHit (p : Params) (s : S) : Option S :=
  if s=0 then some 0 else if zero p s=0 then some 1
  else if zero p (zero p s)=0 then some 2 else none

def afterGap (p : Params) (s : S) : S := one p (zero p s)

def safe (p : Params) : Nat → S → Bool
  | 0,_ => true
  | k+1,s => if s=0 then false else
      match zeroHit p (afterGap p s) with
      | none => true
      | some z => safe p k (iter (one p) (2+z.val) s)
def good (p : Params) (s : S) : Bool := safe p 3 s

theorem good_not_A (p : Params) (s : S) (h : good p s = true) : s ≠ 0 := by
  intro he; subst s; simp [good,safe] at h

theorem drift_check : ∀ a e f ze zf s : S,
    zeroHit ⟨a,e,f,ze,zf⟩ s = none →
      s ≠ 0 ∧ zeroHit ⟨a,e,f,ze,zf⟩ (zero ⟨a,e,f,ze,zf⟩ s) = none := by decide

theorem drift_closed (p : Params) (s : S) (h : zeroHit p s = none) :
    s ≠ 0 ∧ zeroHit p (zero p s) = none := by
  rcases p with ⟨a,e,f,ze,zf⟩
  exact drift_check a e f ze zf s h

theorem good_check : ∀ a e f ze zf s z : S,
    good ⟨a,e,f,ze,zf⟩ s = true →
    zeroHit ⟨a,e,f,ze,zf⟩ (afterGap ⟨a,e,f,ze,zf⟩ s) = some z →
      good ⟨a,e,f,ze,zf⟩ (iter (one ⟨a,e,f,ze,zf⟩) (2+z.val) s) = true := by decide

theorem good_closed (p : Params) (s z : S) (h : good p s = true)
    (hz : zeroHit p (afterGap p s) = some z) :
    good p (iter (one p) (2+z.val) s) = true := by
  rcases p with ⟨a,e,f,ze,zf⟩
  exact good_check a e f ze zf s z h hz

def stepCore (p : Params) (b : Gate) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right (state p.a) true c)
  | .B,false | .C,false => some (left .C true c)
  | .B,true => b c
  | .C,true => some (left .D false c)
  | .D,false => some (right .E false c)
  | .D,true => some (left .D true c)
  | .E,false => some (right (state p.ze) true c)
  | .E,true => some (right (state p.e) true c)
  | .F,false => some (right (state p.zf) true c)
  | .F,true => some (right (state p.f) true c)

def runCore (p : Params) (b : Gate) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (stepCore p b c).bind (runCore p b n)

theorem runCore_add (p : Params) (b : Gate) (m n : Nat) (c : Config) :
    runCore p b (m+n) c = (runCore p b m c).bind (runCore p b n) := by
  induction m generalizing c with
  | zero => simp [runCore]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [runCore]
    cases stepCore p b c <;> simp [ih]

theorem runCore_one (p : Params) (b : Gate) (c : Config) :
    runCore p b 1 c = stepCore p b c := by
  cases h : stepCore p b c <;> simp [runCore,h]

def atScan (s : S) (l r : Stream) : Config := ⟨state s,l,r 0,pop r⟩
def tail : Stream := pair false true zeros
def root (n : Nat) : Config := atScan 1 zeros (rep true n tail)

theorem step_one (p : Params) (b : Gate) (s : S) (l r : Stream) :
    stepCore p b (atScan s l (push true r)) = some (atScan (one p s) (push true l) r) := by
  have hs := (show ∀ s : S, s=0 ∨ s=1 ∨ s=2 by decide) s
  rcases hs with h|h|h <;> subst s <;> rfl

theorem step_zero (p : Params) (b : Gate) (s : S) (l r : Stream) (hs : s ≠ 0) :
    stepCore p b (atScan s l (push false r)) = some (atScan (zero p s) (push true l) r) := by
  have h := (show ∀ s : S, s≠0 → s=1 ∨ s=2 by decide) s hs
  rcases h with h|h <;> subst s <;> rfl

theorem rep_push (n : Nat) (s : Stream) :
    rep true n (push true s) = push true (rep true n s) :=
  BB6.Agent17.Box28CarryFamily.rep_push n s |>.trans rfl

theorem onesScan (p : Params) (b : Gate) (n : Nat) (s : S) (l r : Stream) :
    runCore p b n (atScan s l (rep true n r)) =
      some (atScan (iter (one p) n s) (rep true n l) r) := by
  induction n generalizing s l with
  | zero => rfl
  | succ n ih =>
    rw [runCore,rep,step_one,Option.bind_some,ih,rep_push] <;> rfl

theorem gap (p : Params) (b : Gate) (n : Nat) (s : S) (hs : s≠0) :
    runCore p b 2 (atScan s (ones n) tail) =
      some (atScan (afterGap p s) (ones (n+2)) zeros) := by
  change runCore p b 2 (atScan s (ones n) (push false (push true zeros))) = _
  rw [runCore,step_zero p b s _ _ hs,Option.bind_some,runCore,step_one] <;> rfl

theorem zero_one (p : Params) (b : Gate) (s : S) (n : Nat) (hs : s≠0) :
    runCore p b 1 (atScan s (ones n) zeros) =
      some (atScan (zero p s) (ones (n+1)) zeros) := by
  rw [runCore_one]
  have hh := step_zero p b s (ones n) zeros hs
  rw [zero_push] at hh
  exact hh

theorem zeroScan (p : Params) (b : Gate) (s z : S) (n : Nat)
    (h : zeroHit p s = some z) :
    runCore p b z.val (atScan s (ones n) zeros) =
      some (atScan 0 (ones (n+z.val)) zeros) := by
  unfold zeroHit at h
  split at h
  · rename_i hs
    subst s
    have hz : z=0 := (Option.some.inj h).symm
    subst z; rfl
  · rename_i hs
    split at h
    · rename_i h1
      have hz : z=1 := (Option.some.inj h).symm
      subst z
      change runCore p b 1 _ = some (atScan 0 (ones (n+1)) zeros)
      rw [zero_one p b s n hs,h1]
    · rename_i h1
      split at h
      · rename_i h2
        have hz : z=2 := (Option.some.inj h).symm
        subst z
        change runCore p b (1+1) _ = _
        rw [runCore_add,zero_one p b s n hs,Option.bind_some,
          zero_one p b (zero p s) (n+1) h1,h2] <;> rfl
      · contradiction

theorem drift (p : Params) (b : Gate) (t n : Nat) (s : S)
    (h : zeroHit p s = none) :
    runCore p b t (atScan s (ones n) zeros) ≠ none := by
  induction t generalizing n s with
  | zero => simp [runCore]
  | succ t ih =>
    have hc := drift_closed p s h
    rw [show t+1=1+t by omega,runCore_add,zero_one p b s n hc.1,Option.bind_some]
    exact ih (n+1) (zero p s) hc.2

theorem rewind (p : Params) (b : Gate) (n : Nat) (r : Stream) :
    runCore p b (n+2) (Droot n r) = some (Eroot 0 (rep true (n+1) r)) := by
  induction n generalizing r with
  | zero => simp [runCore,stepCore,Droot,Eroot,ones,rep,left,right]
  | succ n ih =>
    rw [show n+1+2=1+(n+2) by omega,runCore_add]
    change (some (Droot n (push true r))).bind _ = _
    rw [Option.bind_some,ih,BB6.Agent17.Box28CarryFamily.rep_push]

theorem turn (p : Params) (b : Gate) (n : Nat) :
    runCore p b 3 (atScan 0 (ones (n+1)) zeros) = some (Droot n tail) := by rfl

theorem turn_back (p : Params) (b : Gate) (n : Nat) :
    runCore p b (n+5) (atScan 0 (ones (n+1)) zeros) = some (root (n+1)) := by
  rw [show n+5=3+(n+2) by omega,runCore_add,turn,Option.bind_some,rewind] <;> rfl

theorem scanGap (p : Params) (b : Gate) (n : Nat)
    (h : iter (one p) n 1 ≠ 0) :
    runCore p b (n+2) (root n) =
      some (atScan (afterGap p (iter (one p) n 1)) (ones (n+2)) zeros) := by
  rw [runCore_add]
  change (runCore p b n (atScan 1 zeros (rep true n tail))).bind _ = _
  rw [onesScan,Option.bind_some]
  exact gap p b n _ h

theorem round (p : Params) (b : Gate) (n : Nat) (z : S)
    (h : iter (one p) n 1 ≠ 0)
    (hz : zeroHit p (afterGap p (iter (one p) n 1)) = some z) :
    runCore p b (2*(n+2+z.val)+4) (root n) = some (root (n+2+z.val)) := by
  rw [show 2*(n+2+z.val)+4=(n+2)+z.val+(n+1+z.val+5) by omega,
    runCore_add,runCore_add,scanGap p b n h,Option.bind_some,
    zeroScan p b _ z (n+2) hz,Option.bind_some]
  rw [show n+2+z.val=n+1+z.val+1 by omega]
  exact turn_back p b _

theorem never_root (p : Params) (b : Gate) (t n : Nat)
    (h : good p (iter (one p) n 1) = true) : runCore p b t (root n) ≠ none := by
  induction t using Nat.strongRecOn generalizing n with
  | ind t ih =>
    intro ht
    have hn := good_not_A p _ h
    cases hz : zeroHit p (afterGap p (iter (one p) n 1)) with
    | none =>
      have hr := scanGap p b n hn
      by_cases hle : t≤n+2
      · rw [show n+2=t+(n+2-t) by omega,runCore_add,ht] at hr; contradiction
      · rw [show t=(n+2)+(t-(n+2)) by omega,runCore_add,hr,Option.bind_some] at ht
        exact drift p b _ _ _ hz ht
    | some z =>
      have hr := round p b n z hn hz
      let u := 2*(n+2+z.val)+4
      by_cases hle : t≤u
      · change runCore p b u (root n) = _ at hr
        rw [show u=t+(u-t) by omega,runCore_add,ht] at hr; contradiction
      · change runCore p b u (root n) = _ at hr
        rw [show t=u+(t-u) by omega,runCore_add,hr,Option.bind_some] at ht
        have hg := good_closed p _ z h hz
        have he : iter (one p) (n+2+z.val) 1 =
            iter (one p) (2+z.val) (iter (one p) n 1) := by
          rw [show n+2+z.val=n+(2+z.val) by omega,iter_add]
        apply ih (t-u) (by dsimp [u]; omega) (n+2+z.val) ?_ ht
        rw [he]
        exact hg

theorem init (p : Params) (b : Gate) :
    runCore p b 4 localBlank = some (root 0) := by
  simp [runCore,stepCore,localBlank,root,atScan,state,tail,pair,ones,rep,left,right]

theorem never_blank (p : Params) (b : Gate) (t : Nat)
    (h : good p 1 = true) : runCore p b t localBlank ≠ none := by
  intro ht
  have hi := init p b
  by_cases hle : t≤4
  · rw [show 4=t+(4-t) by omega,runCore_add,ht] at hi; contradiction
  · rw [show t=4+(t-4) by omega,runCore_add,hi,Option.bind_some] at ht
    exact never_root p b _ 0 h ht

/-- Number of live steps from the root to the B1 query, if the finite gap
    orbit hits A. Fuel 3 suffices because there are three gap states. -/
def haltCost (p : Params) : Nat → Nat → S → Option Nat
  | 0,_,_ => none
  | k+1,n,s => if s=0 then some (n+1) else
      match zeroHit p (afterGap p s) with
      | none => none
      | some z =>
        let m := n+2+z.val
        (haltCost p k m (iter (one p) (2+z.val) s)).map (fun t => 2*m+4+t)
def blankCost (p : Params) : Option Nat := (haltCost p 3 0 1).map (4+·)

#print axioms good_check
#print axioms never_blank
end BB6.Agent17.Box28ScanQuotient
