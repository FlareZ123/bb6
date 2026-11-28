import Agent5PackedSweep

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent5Q0151SourceMacro
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,true,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

-- l is nearest first, excluding the head; r is head-inclusive.
def frame (q : Fin 6) (l r : List Bool) : P :=
  encode0 ⟨q,r.headD false :: l,r.tail⟩

def alt (n : Nat) := rep [true,false] n
def revAlt (n : Nat) := rep [false,true] n
def ones (n : Nat) := List.replicate n true

def Goes (a b : P) : Prop := ∃ k, 0 < k ∧ runP p k a = some b

theorem goes_join {a b c : P} (h : Goes a b) (g : Goes b c) : Goes a c := by
  obtain ⟨n,hn,h⟩ := h; obtain ⟨k,hk,g⟩ := g
  exact ⟨n+k,by omega,joinP h g⟩

theorem knownPacked (k : Nat) {a b : Z0} (h : Auto.knownRun p k a = some b) (L R : List Bool) :
    runP p k (encode0 (Auto.extend a L R)) = some (encode0 (Auto.extend b L R)) := by
  rw [← encode0_run,Auto.knownRun_sound p k h L R]; rfl

theorem pack_zero (xs : List Bool) : pack (xs++[false]) = pack xs := by
  simp [pack_append,cat,pack]

theorem frame_zero (q : Fin 6) (L R : List Bool) : frame q L (R++[false]) = frame q L R := by
  cases R with
  | nil => rfl
  | cons x xs => simp [frame,encode0,pack_zero]

theorem rightGadget (q q' : Fin 6) (I O : List Bool) (k : Nat)
    (hi : I ≠ [])
    (h : ∀ x : Bool, Auto.knownRun p k ⟨q,[I.headD false],I.tail++[x]⟩ =
      some ⟨q',x::O.reverse,[]⟩) (L R : List Bool) :
    runP p k (frame q L (I++R)) = some (frame q' (O.reverse++L) R) := by
  cases I with
  | nil => contradiction
  | cons i is =>
    cases R with
    | nil =>
      have hh := knownPacked k (h false) L []
      simp only [List.headD_cons,List.tail_cons,Auto.extend,List.append_nil,List.cons_append] at hh
      have he : frame q L ((i::is)++[false]) = frame q L (i::is) := frame_zero q L _
      change runP p k (frame q L ((i::is)++[false])) = some (frame q' (O.reverse++L) [false]) at hh
      rw [he] at hh
      have he2 : frame q' (O.reverse++L) [false] = frame q' (O.reverse++L) [] := frame_zero q' _ []
      rw [he2] at hh
      simpa using hh
    | cons x xs =>
      have hh := knownPacked k (h x) L xs
      simpa [frame,Auto.extend,List.append_assoc] using hh

theorem b10 (L R : List Bool) : runP p 2 (frame 1 L ([true,false]++R)) = some (frame 1 ([true,false]++L) R) :=
  rightGadget 1 1 [true,false] [false,true] 2 (by simp) (by intro x; cases x <;> decide +kernel) L R

theorem c10 (L R : List Bool) : runP p 2 (frame 2 L ([true,false]++R)) = some (frame 1 ([true,true]++L) R) :=
  rightGadget 2 1 [true,false] [true,true] 2 (by simp) (by intro x; cases x <;> decide +kernel) L R

theorem b11 (L R : List Bool) : runP p 2 (frame 1 L ([true,true]++R)) = some (frame 4 ([false,false]++L) R) :=
  rightGadget 1 4 [true,true] [false,false] 2 (by simp) (by intro x; cases x <;> decide +kernel) L R

theorem c11 (L R : List Bool) : runP p 2 (frame 2 L ([true,true]++R)) = some (frame 4 ([false,true]++L) R) :=
  rightGadget 2 4 [true,true] [true,false] 2 (by simp) (by intro x; cases x <;> decide +kernel) L R

theorem e4 (L R : List Bool) : runP p 4 (frame 4 L ([true,true,true,true]++R)) =
    some (frame 4 ([false,true,false,true]++L) R) :=
  rightGadget 4 4 [true,true,true,true] [true,false,true,false] 4 (by simp) (by intro x; cases x <;> decide +kernel) L R

theorem e2 (L R : List Bool) : runP p 5 (frame 4 L ([true,true,false]++R)) =
    some (frame 2 ([true,true,true]++L) R) :=
  rightGadget 4 2 [true,true,false] [true,true,true] 5 (by simp) (by intro x; cases x <;> decide +kernel) L R

theorem e3 (L R : List Bool) : runP p 4 (frame 4 L ([true,true,true,false]++R)) =
    some (frame 1 ([true,true,false,true]++L) R) :=
  rightGadget 4 1 [true,true,true,false] [true,false,true,true] 4 (by simp) (by intro x; cases x <;> decide +kernel) L R

theorem repOnes4 (n : Nat) : rep [true,true,true,true] n = ones (4*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,ih,ones,Nat.mul_succ]
    rfl

theorem repAlt4 (n : Nat) : rep [false,true,false,true] n = revAlt (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,ih,revAlt,Nat.mul_succ]
    rfl

theorem eLoop (n : Nat) (L R : List Bool) :
    runP p (4*n) (frame 4 L (rep [true,true,true,true] n++R)) =
      some (frame 4 (rep [false,true,false,true] n++L) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 := e4 L (rep [true,true,true,true] n++R)
    have h2 := ih ([false,true,false,true]++L)
    have h := joinP h1 h2
    rw [Nat.mul_succ,Nat.add_comm (4*n) 4]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep [false,true,false,true] n) [false,true,false,true] L,rep_snoc] using h


-- Physical right run, including its separator; implicit blank padding is harmless.
def rr (n : Nat) (R : List Bool) := ones n ++ false::R

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones]
  | succ a ih => rw [Nat.succ_add]; simp [ones,List.replicate_succ,← ih, List.cons_append]

theorem alt_reverse (n : Nat) : (alt n).reverse = revAlt n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ([true,false]++alt n).reverse = revAlt (n+1)
    rw [List.reverse_append,ih]
    exact rep_snoc [false,true] n

theorem alt_succ (n : Nat) : alt (n+1) = [true,false]++alt n := rfl

theorem revAlt_snoc (n : Nat) : revAlt (n+1) = revAlt n ++ [false,true] :=
  (rep_snoc [false,true] n).symm

def srcQ (b : Bool) : Fin 6 := if b then 1 else 2
def marker (b : Bool) : List Bool := if b then [false,false] else [false,true]

theorem enter (b : Bool) (L R : List Bool) : runP p 2 (frame (srcQ b) L ([true,true]++R)) =
    some (frame 4 (marker b++L) R) := by
  cases b <;> first | exact b11 L R | exact c11 L R

theorem rightOdd (b : Bool) (n : Nat) (L R : List Bool) :
    runP p (2+4*n+4) (frame (srcQ b) L (rr (4*n+5) R)) =
      some (frame 1 ([true,true,false,true] ++ revAlt (2*n) ++ marker b ++ L) R) := by
  have h1 := enter b L (rep [true,true,true,true] n ++ [true,true,true,false] ++ R)
  have h2 := eLoop n (marker b++L) ([true,true,true,false]++R)
  have h3 := e3 (rep [false,true,false,true] n++marker b++L) R
  have h := joinP (joinP h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
  have he : rr (4*n+5) R = [true,true] ++ (rep [true,true,true,true] n ++ [true,true,true,false] ++ R) := by
    rw [repOnes4,rr,show 4*n+5=2+(4*n+3) by omega,ones_add,ones_add]
    simp [ones,List.append_assoc]
  rw [he]
  simpa only [repAlt4,List.append_assoc] using h

theorem rightZero (b : Bool) (n : Nat) (L R : List Bool) :
    runP p (2+4*n+5) (frame (srcQ b) L (rr (4*n+4) R)) =
      some (frame 2 ([true,true,true] ++ revAlt (2*n) ++ marker b ++ L) R) := by
  have h1 := enter b L (rep [true,true,true,true] n ++ [true,true,false] ++ R)
  have h2 := eLoop n (marker b++L) ([true,true,false]++R)
  have h3 := e2 (rep [false,true,false,true] n++marker b++L) R
  have h := joinP (joinP h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
  have he : rr (4*n+4) R = [true,true] ++ (rep [true,true,true,true] n ++ [true,true,false] ++ R) := by
    rw [repOnes4,rr,show 4*n+4=2+(4*n+2) by omega,ones_add,ones_add]
    simp [ones,List.append_assoc]
  rw [he]
  simpa only [repAlt4,List.append_assoc] using h

theorem rightTwo (b : Bool) (n : Nat) (L R : List Bool) :
    runP p (2+4*n) (frame (srcQ b) L (rr (4*n+2) R)) =
      some (frame 4 (revAlt (2*n) ++ marker b ++ L) (false::R)) := by
  have h1 := enter b L (rep [true,true,true,true] n ++ false::R)
  have h2 := eLoop n (marker b++L) (false::R)
  have h := joinP h1 h2
  have he : rr (4*n+2) R = [true,true] ++ (rep [true,true,true,true] n ++ false::R) := by
    rw [repOnes4,rr,show 4*n+2=2+4*n by omega,ones_add]
    simp [ones,List.append_assoc]
  rw [he]
  simpa only [repAlt4,List.append_assoc] using h

#print axioms rightOdd
#print axioms rightZero
#print axioms rightTwo
end BB6.Agent5Q0151SourceMacro
