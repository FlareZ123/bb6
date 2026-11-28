import Macro
namespace F197.PrefixCheck
structure C where
  p : Phase
  l : List Bool
  r : List Bool
  deriving DecidableEq

def embed (m : C) (x y : Tape) : MacroConfig := ⟨m.p,pre m.l x,pre m.r y⟩

/-- The finite-prefix machine refuses every step requiring a read from either
opaque continuation, and includes the phase-validity guard in each rule. -/
def next : C → Option (Nat × C)
 | ⟨.D,false::l,false::true::r⟩ => some (4,⟨.D,false::true::false::l,r⟩)
 | ⟨.D,false::l,false::false::r⟩ => some (6,⟨.B,l,false::false::true::r⟩)
 | ⟨.D,false::l,true::true::true::r⟩ => some (5,⟨.D,false::true::false::false::l,r⟩)
 | ⟨.D,false::l,true::true::false::r⟩ => some (9,⟨.D,false::true::l,false::true::r⟩)
 | ⟨.D,false::l,true::false::true::r⟩ => some (6,⟨.D,false::true::false::l,false::r⟩)
 | ⟨.D,false::l,true::false::false::false::r⟩ => some (4,⟨.D,false::true::true::false::false::l,r⟩)
 | ⟨.B,false::l,false::r⟩ => some (2,⟨.D,false::true::l,r⟩)
 | ⟨.B,true::true::l,false::r⟩ => some (2,⟨.B,l,false::false::false::r⟩)
 | ⟨.B,true::false::l,false::r⟩ => some (2,⟨.F,l,true::false::false::r⟩)
 | ⟨.F,true::l,r⟩ => some (1,⟨.F,l,true::r⟩)
 | ⟨.F,false::l,r⟩ => some (1,⟨.A,l,true::r⟩)
 | ⟨.A,false::l,true::r⟩ => some (3,⟨.B,l,false::false::r⟩)
 | ⟨.A,true::l,true::r⟩ => some (4,⟨.D,false::true::l,r⟩)
 | _ => none

theorem next_sound (m m' : C) (n : Nat) (x y : Tape) (h : next m = some (n,m')) :
    run n (physical (embed m x y)) = some (physical (embed m' x y)) := by
  fun_cases next m <;> simp [next] at h <;> rcases h with ⟨rfl,rfl⟩ <;>
    apply macro_sound (m := embed _ x y) <;> first | rfl | trivial

def exec : Nat → C → Option (Nat × C)
  | 0,m => some (0,m)
  | k+1,m => do
    let (n,m') ← next m
    let (t,m'') ← exec k m'
    return (n+t,m'')

theorem exec_sound (k : Nat) (m m' : C) (n : Nat) (x y : Tape)
    (h : exec k m = some (n,m')) : run n (physical (embed m x y)) = some (physical (embed m' x y)) := by
  induction k generalizing m n with
  | zero => simp [exec] at h; rcases h with ⟨rfl,rfl⟩; rfl
  | succ k ih =>
    cases hs : next m with
    | none => simp [exec,hs] at h
    | some nm =>
      rcases nm with ⟨c,m1⟩
      cases ht : exec k m1 with
      | none => simp [exec,hs,ht] at h
      | some tm =>
        rcases tm with ⟨t,m2⟩
        simp [exec,hs,ht] at h
        rcases h with ⟨rfl,rfl⟩
        rw [run_add, next_sound m m1 c x y hs]
        exact ih m1 t ht

#print axioms exec_sound
end F197.PrefixCheck
