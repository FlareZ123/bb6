import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RA.Leaf1659
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,4⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | (4,false) => some (some ⟨true,false,5⟩)
  | (4,true) => some (some ⟨false,true,2⟩)
  | (5,false) => some (some ⟨false,false,0⟩)
  | (5,true) => some (some ⟨false,false,5⟩)
  | _ => none

def sectionWord (r : List Bool) : Z0 := ⟨0,[],r⟩
def front (q : Fin 6) (l r : List Bool) : Z0 := ⟨q,r.headD false::l,r.tail⟩
def bits (b : Bool) (n : Nat) : List Bool := rep [b] n

def stack : List Nat → List Bool
  | [] => []
  | [n] => bits true (n+1)
  | n::m::p => bits true (n+1) ++ false :: stack (m::p)

def frame (p : List Nat) : List Bool := if p.isEmpty then [] else false :: stack p

def output : List Nat → List Bool
  | [] => []
  | n::p => output p ++ bits false (n+1) ++ [true]

def D (a : Nat) (p : List Nat) (r : List Bool) : Z0 :=
  front 3 (false :: bits true (a+3) ++ frame p) r

def E (a : Nat) (p : List Nat) (r : List Bool) : Z0 :=
  front 4 ([true,false,true,false] ++ bits true (a+1) ++ frame p) r

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (sectionWord [false,false,true,false,true]) := by decide

theorem enterD (r : List Bool) :
    run0 table 6 (sectionWord (false::false::true::r)) = some (D 0 [] r) := by
  cases r <;> rfl

theorem readOne (a : Nat) (p : List Nat) (r : List Bool) :
    run0 table 3 (D a p (true::r)) = some (D (a+1) p r) := by
  cases r <;> rfl

theorem readZero (a : Nat) (p : List Nat) (r : List Bool) :
    run0 table 7 (D a p (false::r)) = some (E a p r) := by
  cases r <;> rfl

theorem continue100 (a : Nat) (p : List Nat) (r : List Bool) :
    run0 table 17 (E a p ([true,false,false]++r)) = some (D 2 (a::p) r) := by
  cases p <;> cases r <;> simp only [D,E,frame,stack,List.isEmpty,ite_true,List.append_nil] <;> rfl

theorem continue1010 (a : Nat) (p : List Nat) (r : List Bool) :
    run0 table 16 (E a p ([true,false,true,false]++r)) = some (D 1 (0::a::p) r) := by
  cases p <;> cases r <;> simp only [D,E,frame,stack,List.isEmpty,ite_true,List.append_nil] <;> rfl

theorem continue10111 (a : Nat) (p : List Nat) (r : List Bool) :
    run0 table 11 (E a p ([true,false,true,true,true]++r)) = some (D 0 (0::0::a::p) r) := by
  cases p <;> cases r <;> simp only [D,E,frame,stack,List.isEmpty,ite_true,List.append_nil] <;> rfl

theorem stack_cons (n : Nat) (p : List Nat) :
    stack (n::p) = bits true (n+1) ++ frame p := by
  cases p <;> simp [stack,frame]

theorem frame_cons (n : Nat) (p : List Nat) :
    frame (n::p) = false :: stack (n::p) := by rfl

theorem clearF (n : Nat) (L R : List Bool) :
    run0 table n ⟨5,bits true n++L,R⟩ = some ⟨5,L,bits false n++R⟩ := by
  have h := sweepL table 5 [] [] [true] [false] 1 (by intro L R; rfl) n L R
  simpa [bits] using h

theorem sweepEntry (n : Nat) (p : List Nat) (r : List Bool) :
    run0 table 1 (front 4 (stack (n::p)) (false::r)) =
      some ⟨5,bits true (n+1)++frame p,true::r⟩ := by
  rw [stack_cons]; rfl

theorem finishLast (r : List Bool) :
    run0 table 1 ⟨5,[],r⟩ = some (sectionWord (false::r)) := by rfl

theorem nextRun (n : Nat) (p : List Nat) (r : List Bool) :
    run0 table 2 ⟨5,frame (n::p),r⟩ =
      some (front 4 (stack (n::p)) (false::r)) := by
  rw [frame_cons,stack_cons]; rfl

theorem returnSweep (n : Nat) (p : List Nat) (r : List Bool) :
    ∃ t : Nat, 0<t ∧ run0 table t (front 4 (stack (n::p)) (false::r)) =
      some (sectionWord (false :: output (n::p) ++ r)) := by
  induction p generalizing n r with
  | nil =>
    have h1 := sweepEntry n [] r
    have h2 := clearF (n+1) [] (true::r)
    have h3 := finishLast (bits false (n+1)++true::r)
    have h := join0 (join0 h1 h2) h3
    refine ⟨1+(n+1)+1,by omega,?_⟩
    simpa only [output,List.nil_append,List.append_assoc,List.cons_append,frame,List.isEmpty,ite_true] using h
  | cons m p ih =>
    have h1 := sweepEntry n (m::p) r
    have h2 := clearF (n+1) (frame (m::p)) (true::r)
    have h3 := nextRun m p (bits false (n+1)++true::r)
    obtain ⟨t,ht,h4⟩ := ih m (bits false (n+1)++true::r)
    have h := join0 (join0 (join0 h1 h2) h3) h4
    refine ⟨1+(n+1)+2+t,by omega,?_⟩
    simpa only [output,List.append_assoc,List.cons_append,List.nil_append] using h

theorem returnE (a : Nat) (p : List Nat) (r : List Bool) :
    ∃ t : Nat, 0<t ∧ run0 table t (E a p (false::r)) =
      some (sectionWord (false :: output (0::0::a::p) ++ r)) := by
  have h := returnSweep 0 (0::a::p) r
  have hs : stack (0::0::a::p) = [true,false,true,false] ++ bits true (a+1) ++ frame p := by
    rw [stack_cons,frame_cons,stack_cons,frame_cons,stack_cons]; rfl
  simpa only [E,hs] using h

def emitRun (a : Nat) : List Bool := bits false (a+1) ++ [true]

def place (d : Bool) (a : Nat) (p : List Nat) (r : List Bool) : Z0 :=
  if d then D a p r else E a p r

/-- Exact sufficient parser, including the implicit zero suffix of the tape. -/
inductive Parse : Bool → Nat → List Bool → List Bool → Prop where
  | one : Parse true (a+1) r v → Parse true a (true::r) v
  | zero : Parse false a r v → Parse true a (false::r) v
  | zeroEmpty : Parse false a [] v → Parse true a [] v
  | stop : Parse false a (false::r) (emitRun a ++ [false,true,false,true] ++ r)
  | stopEmpty : Parse false a [] (emitRun a ++ [false,true,false,true])
  | more100 : Parse true 2 r v → Parse false a ([true,false,false]++r) (emitRun a ++ v)
  | more1 : Parse true 2 [] v → Parse false a [true] (emitRun a ++ v)
  | more10 : Parse true 2 [] v → Parse false a [true,false] (emitRun a ++ v)
  | more1010 : Parse true 1 r v → Parse false a ([true,false,true,false]++r) (emitRun a ++ [false,true] ++ v)
  | more101 : Parse true 1 [] v → Parse false a [true,false,true] (emitRun a ++ [false,true] ++ v)
  | more10111 : Parse true 0 r v → Parse false a ([true,false,true,true,true]++r) (emitRun a ++ [false,true,false,true] ++ v)

theorem continue1 (a : Nat) (p : List Nat) :
    run0 table 17 (E a p [true]) = some (D 2 (a::p) []) := by
  cases p <;> simp only [D,E,frame,stack,List.isEmpty,ite_true,List.append_nil] <;> rfl

theorem continue10 (a : Nat) (p : List Nat) :
    run0 table 17 (E a p [true,false]) = some (D 2 (a::p) []) := by
  cases p <;> simp only [D,E,frame,stack,List.isEmpty,ite_true,List.append_nil] <;> rfl

theorem continue101 (a : Nat) (p : List Nat) :
    run0 table 16 (E a p [true,false,true]) = some (D 1 (0::a::p) []) := by
  cases p <;> simp only [D,E,frame,stack,List.isEmpty,ite_true,List.append_nil] <;> rfl

theorem join_positive {k : Nat} {s z w : Z0} (h : run0 table k s = some z)
    (H : ∃ t : Nat, 0<t ∧ run0 table t z = some w) :
    ∃ t : Nat, 0<t ∧ run0 table t s = some w := by
  obtain ⟨t,ht,hr⟩ := H
  exact ⟨k+t,by omega,join0 h hr⟩

theorem parse_sound {d : Bool} {a : Nat} {r v : List Bool} (h : Parse d a r v)
    (p : List Nat) : ∃ t : Nat, 0<t ∧ run0 table t (place d a p r) =
      some (sectionWord (false :: output p ++ v)) := by
  induction h generalizing p with
  | one h ih => exact join_positive (readOne _ p _) (ih p)
  | zero h ih => exact join_positive (readZero _ p _) (ih p)
  | zeroEmpty h ih => exact join_positive (readZero _ p []) (ih p)
  | stop =>
    simpa only [place,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append,List.nil_append, bits,rep] using returnE _ p _
  | stopEmpty =>
    rename_i a
    have h := returnE a p []
    rw [show E a p [false] = E a p [] from rfl] at h
    simpa only [place,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,bits,rep] using h
  | more100 h ih =>
    simpa only [place,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append] using join_positive (continue100 _ p _) (ih (_::p))
  | more1 h ih =>
    simpa only [place,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append] using join_positive (continue1 _ p) (ih (_::p))
  | more10 h ih =>
    simpa only [place,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append] using join_positive (continue10 _ p) (ih (_::p))
  | more1010 h ih =>
    simpa only [place,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append,List.nil_append,bits,rep] using join_positive (continue1010 _ p _) (ih (0::_::p))
  | more101 h ih =>
    simpa only [place,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append,List.nil_append,bits,rep] using join_positive (continue101 _ p) (ih (0::_::p))
  | more10111 h ih =>
    simpa only [place,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,output,emitRun,List.append_assoc,List.cons_append,List.nil_append,bits,rep] using join_positive (continue10111 _ p _) (ih (0::0::_::p))

theorem sectionReturn {r v : List Bool} (h : Parse true 0 r v) :
    ∃ t : Nat, 0<t ∧ run0 table t (sectionWord (false::false::true::r)) =
      some (sectionWord (false::v)) := by
  simpa only [place,ite_true,output,List.nil_append,List.cons_append] using join_positive (enterD r) (parse_sound h [])

/-- The only remaining obligation is an inductive language of authentic return tails. -/
theorem never_of_language (I : List Bool → Prop)
    (seed : I [false,true])
    (closed : ∀ r, I r → ∃ s, I s ∧ Parse true 0 r (false::true::s))
    (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t r, k ≤ t ∧ I r ∧
      run0 table t ⟨0,[],[]⟩ = some (sectionWord (false::false::true::r)) := by
    intro k
    induction k with
    | zero => exact ⟨17,[false,true],by omega,seed,entry⟩
    | succ k ih =>
      obtain ⟨t,r,ht,hr,h⟩ := ih
      obtain ⟨s,hs,hp⟩ := closed r hr
      obtain ⟨c,hc,hstep⟩ := sectionReturn hp
      exact ⟨t+c,s,by omega,hs,join0 h hstep⟩
  intro n
  obtain ⟨t,r,ht,hr,h⟩ := arbitrary n
  open Agent50Zipper in
    have hz : (zrun table t start).map project = some (sectionWord (false::false::true::r)) :=
      (run_project table t start).trans h
    cases hrun : zrun table t start with
    | none => simp [hrun] at hz
    | some z =>
      have H := zrun_sound table m hm t start z hrun
      rw [start_embed] at H
      rw [show t=n+(t-n) by omega,run_append] at H
      cases he : run m n blank with
      | none => simp [he] at H
      | some c => rfl

#print axioms never_of_language
#print axioms parse_sound
#print axioms sectionReturn
#print axioms returnSweep
#print axioms returnE
#print axioms continue100
#print axioms continue1010
#print axioms continue10111
end BB6.Agent32Raw42RA.Leaf1659
