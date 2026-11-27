import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49C1Guard
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where | la0 | ld0 | rd0 | la1 | ld1
  deriving DecidableEq, Repr

def e0 : Kind → Move
  | .la0 => ⟨false,false,0⟩
  | .ld0 => ⟨false,false,3⟩
  | .rd0 => ⟨false,true,3⟩
  | .la1 => ⟨true,false,0⟩
  | .ld1 => ⟨true,false,3⟩

def table (v : Kind) (w : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some (e0 v))
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨w,true,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def tail4 (w : Bool) : List Bool := [w,w,w,w]
def stack (w : Bool) : Nat → List Bool
  | 0 => true :: true :: true :: tail4 w
  | n+1 => true :: false :: stack w n
def boundary (w : Bool) (r : List Bool) : Z0 := ⟨0,false::true::tail4 w,r⟩
def C (w : Bool) (n : Nat) (b : Bool) (r : List Bool) : Z0 := ⟨2,b::stack w n,r⟩
def A (w : Bool) (n : Nat) (r : List Bool) : Z0 := ⟨0,stack w n,r⟩

theorem entry (v : Kind) (w : Bool) :
    run0 (table v w) 14 ⟨0,[],[]⟩ = some (boundary w []) := by
  cases v <;> cases w <;> rfl

theorem enterNil (v : Kind) (w : Bool) :
    run0 (table v w) 2 (boundary w []) = some (C w 0 false []) := by rfl

theorem enterCons (v : Kind) (w b : Bool) (r : List Bool) :
    run0 (table v w) 2 (boundary w (false::b::r)) = some (C w 0 b r) := by rfl

theorem enterSingle (v : Kind) (w : Bool) :
    run0 (table v w) 2 (boundary w [false]) = some (C w 0 false []) := by rfl

theorem scanOne (v : Kind) (w : Bool) (n : Nat) (r : List Bool) :
    run0 (table v w) 1 (C w n true r) = some (A w n (false::r)) := by rfl

theorem scanNil (v : Kind) (w : Bool) (n : Nat) :
    run0 (table v w) 5 (C w n false []) = some (A w n [false,true]) := by
  cases n <;> rfl

theorem scanZero (v : Kind) (w : Bool) (n : Nat) (r : List Bool) :
    run0 (table v w) 5 (C w n false (false::r)) = some (A w n (false::true::r)) := by
  cases n <;> rfl

theorem scanPair (v : Kind) (w b : Bool) (n : Nat) (r : List Bool) :
    run0 (table v w) 2 (C w n false (true::b::r)) = some (C w (n+1) b r) := by rfl

theorem scanLast (v : Kind) (w : Bool) (n : Nat) :
    run0 (table v w) 2 (C w n false [true]) = some (C w (n+1) false []) := by rfl

/-- Every finite right word returns to A with a finite stack of 10 pairs. -/
theorem scan (v : Kind) (w : Bool) (n : Nat) (b : Bool) (r : List Bool) :
    ∃ k j s, 0 < k ∧ run0 (table v w) k (C w n b r) = some (A w j s) := by
  cases b with
  | true => exact ⟨1,n,false::r,by decide,scanOne v w n r⟩
  | false =>
    cases r with
    | nil => exact ⟨5,n,[false,true],by decide,scanNil v w n⟩
    | cons a r =>
      cases a with
      | false => exact ⟨5,n,false::true::r,by decide,scanZero v w n r⟩
      | true =>
        cases r with
        | nil => exact ⟨7,n+1,[false,true],by decide,join0 (scanLast v w n) (scanNil v w (n+1))⟩
        | cons b r =>
          obtain ⟨k,j,s,hk,h⟩ := scan v w (n+1) b r
          exact ⟨2+k,j,s,by omega,join0 (scanPair v w b n r) h⟩
termination_by r.length

def popCost : Kind → Nat
  | .la0 => 2
  | .ld0 => 8
  | .rd0 => 6
  | .la1 => 2
  | .ld1 => 4

def out : Kind → List Bool
  | .la0 => [false,false]
  | .ld0 => [false,true]
  | .rd0 => [false,true]
  | .la1 => [true,false]
  | .ld1 => [false,false]

theorem pop (v : Kind) (w : Bool) (n : Nat) (r : List Bool) :
    run0 (table v w) (popCost v) (A w (n+1) r) = some (A w n (out v ++ r)) := by
  cases v <;> cases n <;> rfl

theorem finish (v : Kind) (w : Bool) (r : List Bool) :
    run0 (table v w) 3 (A w 0 r) = some (boundary w (false::r)) := by rfl

theorem popAll (v : Kind) (w : Bool) (n : Nat) (r : List Bool) :
    ∃ k s, 0 < k ∧ run0 (table v w) k (A w n r) = some (boundary w (false::s)) := by
  induction n generalizing r with
  | zero => exact ⟨3,r,by decide,finish v w r⟩
  | succ n ih =>
    obtain ⟨k,s,hk,h⟩ := ih (out v ++ r)
    exact ⟨popCost v+k,s,by omega,join0 (pop v w n r) h⟩

def Guard (w : Bool) (z : Z0) : Prop :=
  z = boundary w [] ∨ ∃ r, z = boundary w (false::r)

theorem return_guard (v : Kind) (w : Bool) (z : Z0) (hz : Guard w z) :
    ∃ k t, 0 < k ∧ Guard w t ∧ run0 (table v w) k z = some t := by
  have close (b : Bool) (r : List Bool) (h : run0 (table v w) 2 z = some (C w 0 b r)) :
      ∃ k t, 0 < k ∧ Guard w t ∧ run0 (table v w) k z = some t := by
    obtain ⟨k,j,s,hk,hs⟩ := scan v w 0 b r
    obtain ⟨k',s',hk',hs'⟩ := popAll v w j s
    exact ⟨2+k+k',boundary w (false::s'),by omega,Or.inr ⟨s',rfl⟩,join0 (join0 h hs) hs'⟩
  rcases hz with rfl | ⟨r,rfl⟩
  · exact close false [] (enterNil v w)
  · cases r with
    | nil => exact close false [] (enterSingle v w)
    | cons b r => exact close b r (enterCons v w b r)

/-- A positive-cost closed invariant is sufficient; no periodicity assumption. -/
theorem never (v : Kind) (w : Bool) (m : Machine) (hm : compatible (table v w) m) :
    NeverHalts m := by
  have arbitrary : ∀ k, ∃ t z, k ≤ t ∧ Guard w z ∧
      run0 (table v w) t ⟨0,[],[]⟩ = some z := by
    intro k
    induction k with
    | zero => exact ⟨14,boundary w [],by decide,Or.inl rfl,entry v w⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hz,hr⟩ := ih
      obtain ⟨d,z',hd,hz',hr'⟩ := return_guard v w z hz
      exact ⟨t+d,z',by omega,hz',join0 hr hr'⟩
  intro n
  obtain ⟨t,z,ht,_,hr⟩ := arbitrary n
  have hz : (BB6Coverage.Agent50Zipper.zrun (table v w) t start).map project = some z :=
    (run_project (table v w) t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun (table v w) t start with
  | none => simp [h] at hz
  | some c =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound (table v w) m hm t start c h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent7Raw49C1Guard
