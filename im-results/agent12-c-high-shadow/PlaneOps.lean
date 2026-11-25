import BitEventCertificate
namespace BB6.Agent12PlaneOps
open BB6.Agent12BitPlanes BB6.Agent12BitEventSummary

def padLeft : List Nat → List (Nat×Nat)
  | [] => []
  | q::qs => (0,q)::padLeft qs

def pairs : List Nat → List Nat → List (Nat×Nat)
  | [],qs => padLeft qs
  | p::ps,[] => (p,0)::pairs ps []
  | p::ps,q::qs => (p,q)::pairs ps qs

theorem pairs_fst (ps qs : List Nat) (i : Nat) : value ((pairs ps qs).map Prod.fst) i=value ps i := by
  induction ps generalizing qs with
  | nil => induction qs with
    | nil => rfl
    | cons q qs ih =>
      change bit 0 i+2*value ((pairs [] qs).map Prod.fst) i=0
      simp [ih,value,bit]
  | cons p ps ih => cases qs with
    | nil => simp [pairs,value,ih]
    | cons q qs => simp [pairs,value,ih]

theorem pairs_snd (ps qs : List Nat) (i : Nat) : value ((pairs ps qs).map Prod.snd) i=value qs i := by
  induction ps generalizing qs with
  | nil => induction qs with
    | nil => rfl
    | cons q qs ih =>
      change bit q i+2*value ((pairs [] qs).map Prod.snd) i=bit q i+2*value qs i
      rw [ih]
  | cons p ps ih => cases qs with
    | nil => simp [pairs,value,ih,bit]
    | cons q qs => simp [pairs,value,ih]

def addP (ps qs : List Nat) : List Nat := BB6.Agent12BitEventCertificate.addPairs (pairs ps qs) 0

theorem fullAdder (x y c i : Nat) : bit x i+bit y i+bit c i=bit ((x^^^y)^^^c) i+2*bit ((x&&&y)|||((x^^^y)&&&c)) i := by
  simp only [bit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases c.testBit i <;> decide

theorem addPairs_sound (ps : List (Nat×Nat)) (c i : Nat) :
    value (BB6.Agent12BitEventCertificate.addPairs ps c) i = value (ps.map Prod.fst) i+value (ps.map Prod.snd) i+bit c i := by
  induction ps generalizing c with
  | nil => simp [BB6.Agent12BitEventCertificate.addPairs,value]
  | cons p ps ih =>
    rcases p with ⟨x,y⟩
    simp only [BB6.Agent12BitEventCertificate.addPairs,value,List.map_cons,ih]
    have h := fullAdder x y c i
    omega

theorem addP_sound (ps qs : List Nat) (i : Nat) : value (addP ps qs) i=value ps i+value qs i := by
  rw [addP,addPairs_sound,pairs_fst,pairs_snd]; simp [bit]

def mul2 (ps : List Nat) : List Nat := 0::ps
@[simp] theorem value_mul2 (ps : List Nat) (i : Nat) : value (mul2 ps) i=2*value ps i := by simp [mul2,value,bit]

def maskP (q : Nat) (ps : List Nat) : List Nat := ps.map (fun p=>p&&&q)
@[simp] theorem value_maskP (q : Nat) (ps : List Nat) (i : Nat) : value (maskP q ps) i=bit q i*value ps i := by
  induction ps with
  | nil => simp [maskP,value]
  | cons p ps ih =>
    change bit (p&&&q) i+2*value (maskP q ps) i=bit q i*(bit p i+2*value ps i)
    rw [bit_and,ih]; grind

def shiftP (ps : List Nat) : List Nat := ps.map (fun p=>p>>>1)
@[simp] theorem value_shiftP (ps : List Nat) (i : Nat) : value (shiftP ps) i=value ps (i+1) := value_rshift ps 1 i

-- Low planes are handled first, propagating a borrow to the high planes.
def borrow (ps : List (Nat×Nat)) (c : Nat) : Nat := match ps with
  | [] => c
  | (x,y)::rs => borrow rs (((y|||c)^^^((y|||c)&&&x)) ||| (y&&&c))

theorem borrow_sound (ps : List (Nat×Nat)) (c i : Nat) :
    (borrow ps c).testBit i=true ↔ value (ps.map Prod.fst) i<value (ps.map Prod.snd) i+bit c i := by
  induction ps generalizing c with
  | nil => simp [borrow,value,bit]; cases c.testBit i <;> decide
  | cons p ps ih =>
    rcases p with ⟨x,y⟩
    simp only [borrow,ih,List.map_cons,value]
    simp only [bit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]
    cases x.testBit i <;> cases y.testBit i <;> cases c.testBit i <;> simp <;> omega

def ltMask (ps qs : List Nat) : Nat := borrow (pairs ps qs) 0

theorem ltMask_sound (ps qs : List Nat) (i : Nat) : (ltMask ps qs).testBit i=true ↔ value ps i<value qs i := by
  rw [ltMask,borrow_sound,pairs_fst,pairs_snd]; simp [bit]

def diffMask : List (Nat×Nat)→Nat
  | [] => 0
  | (x,y)::rs => (x^^^y)|||diffMask rs

theorem diffMask_sound (ps : List (Nat×Nat)) (i : Nat) : (diffMask ps).testBit i=false ↔ value (ps.map Prod.fst) i=value (ps.map Prod.snd) i := by
  induction ps with
  | nil => simp [diffMask,value]
  | cons p ps ih =>
    rcases p with ⟨x,y⟩
    simp only [diffMask,Nat.testBit_or,Nat.testBit_xor,Bool.or_eq_false_iff,ih,List.map_cons,value]
    unfold bit
    cases x.testBit i <;> cases y.testBit i <;> simp <;> omega

def equalOn (q : Nat) (ps qs : List Nat) : Prop := q&&&diffMask (pairs ps qs)=0

def leOn (q : Nat) (ps qs : List Nat) : Prop := q&&&ltMask qs ps=0

instance (q : Nat) (ps qs : List Nat) : Decidable (equalOn q ps qs) := by unfold equalOn; infer_instance
instance (q : Nat) (ps qs : List Nat) : Decidable (leOn q ps qs) := by unfold leOn; infer_instance

theorem equalOn_sound (q : Nat) (ps qs : List Nat) (h : equalOn q ps qs) (i : Nat) (hi : q.testBit i=true) : value ps i=value qs i := by
  change q&&&diffMask (pairs ps qs)=0 at h
  have he := congrArg (fun n=>n.testBit i) h
  simp [Nat.testBit_and,hi] at he
  rw [←pairs_fst ps qs i,←pairs_snd ps qs i]
  apply (diffMask_sound _ _).mp
  exact he

theorem leOn_sound (q : Nat) (ps qs : List Nat) (h : leOn q ps qs) (i : Nat) (hi : q.testBit i=true) : value ps i≤value qs i := by
  by_cases he : value ps i≤value qs i
  · exact he
  · have hlt := (ltMask_sound qs ps i).mpr (by omega)
    change q&&&ltMask qs ps=0 at h
    have hbit := congrArg (fun n=>n.testBit i) h
    simp [Nat.testBit_and,hi,hlt] at hbit

#print axioms addP_sound
#print axioms ltMask_sound
#print axioms equalOn_sound
#print axioms leOn_sound
end BB6.Agent12PlaneOps
