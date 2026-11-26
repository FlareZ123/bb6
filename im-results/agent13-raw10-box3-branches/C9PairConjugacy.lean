import Std

namespace C9Pair
inductive Q where | A | B | C | D | E | F deriving DecidableEq, Repr
abbrev Stream := Nat → Bool
def push (a : Bool) (s : Stream) : Stream
  | 0 => a
  | n+1 => s n
def pop (s : Stream) : Stream := fun n => s (n+1)
@[simp] theorem push_zero (a : Bool) (s : Stream) : push a s 0 = a := rfl
@[simp] theorem pop_push (a : Bool) (s : Stream) : pop (push a s) = s := rfl
@[simp] theorem push_pop (s : Stream) : push (s 0) (pop s) = s := by
  funext n; cases n <;> rfl
structure Config where
  q : Q
  l : Stream
  a : Bool
  r : Stream

def right (q : Q) (w : Bool) (c : Config) : Config := ⟨q, push w c.l, c.r 0, pop c.r⟩
def left (q : Q) (w : Bool) (c : Config) : Config := ⟨q, pop c.l, c.l 0, push w c.r⟩
-- false = longer machine, true = shorter machine.
def step (short : Bool) (c : Config) : Option Config :=
  match c.q, c.a with
  | .A, false => some (right .B true c)
  | .A, true => some (right .D false c)
  | .B, false => some (left .C true c)
  | .B, true => some (left .B true c)
  | .C, false => some (left .E false c)
  | .C, true => some (left .C false c)
  | .D, false => some (right .F short c)
  | .D, true => some (left .E true c)
  | .E, false => some (right .E true c)
  | .E, true => some (right .A false c)
  | .F, false => some (left (if short then .B else .A) true c)
  | .F, true => none

def run (short : Bool) : Nat → Config → Option Config
  | 0, c => some c
  | n+1, c => (step short c).bind (run short n)

theorem run_add (short : Bool) (m n : Nat) (c : Config) :
    run short (m+n) c = (run short m c).bind (run short n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step short c <;> simp [ih]

def macroD (c : Config) : Config := ⟨.B, pop c.l, c.l 0, push true (push true (pop c.r))⟩

theorem d0_success (l r : Stream) (hr : r 0 = false) :
    run false 5 ⟨.D,l,false,r⟩ = some (macroD ⟨.D,l,false,r⟩) ∧
    run true 3 ⟨.D,l,false,r⟩ = some (macroD ⟨.D,l,false,r⟩) := by
  constructor <;> simp [run,step,right,left,macroD,hr]

theorem d0_halt (l r : Stream) (hr : r 0 = true) :
    run false 2 ⟨.D,l,false,r⟩ = none ∧ run true 2 ⟨.D,l,false,r⟩ = none := by
  constructor <;> simp [run,step,right,hr]

theorem common_chunk (c : Config) (hc : c.q ≠ .F) :
    (∃ k j, 0 < k ∧ 0 < j ∧ run false k c = none ∧ run true j c = none) ∨
    (∃ k j c', 0 < k ∧ 0 < j ∧ c'.q ≠ .F ∧
      run false k c = some c' ∧ run true j c = some c') := by
  rcases c with ⟨q,l,a,r⟩
  cases q <;> cases a <;> simp at hc
  case D.false =>
    cases hr : r 0
    · right; exact ⟨5,3,macroD ⟨.D,l,false,r⟩,by decide,by decide,by simp [macroD],(d0_success l r hr).1,(d0_success l r hr).2⟩
    · left; exact ⟨2,2,by decide,by decide,(d0_halt l r hr).1,(d0_halt l r hr).2⟩
  case A.false => right; exact ⟨1,1,right .B true ⟨.A,l,false,r⟩,by decide,by decide,by simp [right],rfl,rfl⟩
  case A.true => right; exact ⟨1,1,right .D false ⟨.A,l,true,r⟩,by decide,by decide,by simp [right],rfl,rfl⟩
  case B.false => right; exact ⟨1,1,left .C true ⟨.B,l,false,r⟩,by decide,by decide,by simp [left],rfl,rfl⟩
  case B.true => right; exact ⟨1,1,left .B true ⟨.B,l,true,r⟩,by decide,by decide,by simp [left],rfl,rfl⟩
  case C.false => right; exact ⟨1,1,left .E false ⟨.C,l,false,r⟩,by decide,by decide,by simp [left],rfl,rfl⟩
  case C.true => right; exact ⟨1,1,left .C false ⟨.C,l,true,r⟩,by decide,by decide,by simp [left],rfl,rfl⟩
  case D.true => right; exact ⟨1,1,left .E true ⟨.D,l,true,r⟩,by decide,by decide,by simp [left],rfl,rfl⟩
  case E.false => right; exact ⟨1,1,right .E true ⟨.E,l,false,r⟩,by decide,by decide,by simp [right],rfl,rfl⟩
  case E.true => right; exact ⟨1,1,right .A false ⟨.E,l,true,r⟩,by decide,by decide,by simp [right],rfl,rfl⟩

def Halts (short : Bool) (c : Config) : Prop := ∃ n, run short n c = none

theorem equivalent_from (short : Bool) (n : Nat) (c : Config) (hc : c.q ≠ .F)
    (hn : run short n c = none) : Halts (!short) c := by
  induction n using Nat.strongRecOn generalizing c with
  | ind n ih =>
    rcases common_chunk c hc with ⟨k,j,hk,hj,hf,ht⟩ | ⟨k,j,d,hk,hj,hd,hf,ht⟩
    · cases short
      · exact ⟨j,ht⟩
      · exact ⟨k,hf⟩
    · have aux : ∀ (b : Bool) (u v : Nat), 0 < u →
          run b u c = some d → run (!b) v c = some d →
          run b n c = none → b = short → Halts (!b) c := by
        intro b u v hu hrun hop hnone hb
        subst b
        have hlt : u < n := by
          by_cases hle : u < n
          · exact hle
          · exfalso
            have he := run_add short n (u-n) c
            have eq : n+(u-n)=u := by omega
            rw [eq,hnone] at he
            simp at he
            rw [hrun] at he
            contradiction
        have he := run_add short u (n-u) c
        have eq : u+(n-u)=n := by omega
        rw [eq,hnone,hrun] at he
        simp at he
        obtain ⟨m,hm⟩ := ih (n-u) (by omega) d hd he.symm
        exact ⟨v+m,by rw [run_add,hop]; exact hm⟩
      cases hshort : short
      · exact aux false k j hk hf ht (hshort ▸ hn) hshort.symm
      · exact aux true j k hj ht hf (hshort ▸ hn) hshort.symm

theorem blank_halts_iff : Halts false ⟨.A,fun _ => false,false,fun _ => false⟩ ↔
    Halts true ⟨.A,fun _ => false,false,fun _ => false⟩ := by
  constructor <;> intro h <;> obtain ⟨n,hn⟩ := h
  · exact equivalent_from false n _ (by decide) hn
  · exact equivalent_from true n _ (by decide) hn

#print axioms blank_halts_iff
end C9Pair
