import SweepPumping

/-! Closed scan/drain grammar for 1RB0LF_1RC0RB_0RD0RC_1LD0LE_1LA1RC_0LB---.
The only absent transition is F1. Every section transition is a finite
arbitrary-tail computation or a pumped single-cell sweep. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option autoImplicit false
namespace BB6.Agent8Raw54.E1OneRC.M139
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev O (n : Nat) := rep [true] n
abbrev Z (n : Nat) := rep [false] n
abbrev A (l r : List Bool) : Z0 := ⟨0,l,true::false::r⟩

private theorem rep_add (p : List Bool) (a b : Nat) :
    rep p (a+b) = rep p a ++ rep p b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b = (a+b)+1 by omega]
    simp only [rep,ih,List.append_assoc]

-- Positive run of 1s, then 01: the C rightward sweep returns directly to A.
private theorem a0_one (a : Nat) (L R : List Bool) :
    run0 table (a+7) (A (false::L) (O (a+1) ++ [false,true] ++ R)) =
      some (A (Z (a+1) ++ [true,false,true] ++ L) R) := by
  have h1 : run0 table 3 (A (false::L) (O (a+1) ++ [false,true] ++ R)) =
      some (⟨2,[true,true,false,true] ++ L,O a ++ [false,true] ++ R⟩ : Z0) := by rfl
  have h2 : run0 table a ⟨2,[true,true,false,true] ++ L,O a ++ [false,true] ++ R⟩ =
      some ⟨2,[true] ++ Z a ++ [true,false,true] ++ L,[false,true] ++ R⟩ := by
    simpa only [Nat.one_mul,List.append_assoc,List.nil_append,List.cons_append] using
      (sweepR table 2 [true] [] [true] [false] 1 (fun _ _ => rfl) a ([true,false,true] ++ L) ([false,true] ++ R))
  have h3 : run0 table 4 ⟨2,[true] ++ Z a ++ [true,false,true] ++ L,[false,true] ++ R⟩ =
      some (A (Z (a+1) ++ [true,false,true] ++ L) R) := by rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 3+a+4=a+7 by omega] at h
  exact h

-- Positive run of 1s, then 00: sweep left across precisely the erased cells.
private theorem a0_zero (a : Nat) (L R : List Bool) :
    run0 table (2*a+10) (A (false::L) (O (a+1) ++ [false,false] ++ R)) =
      some (A (true::L) (O (a+3) ++ R)) := by
  have h1 : run0 table 3 (A (false::L) (O (a+1) ++ [false,false] ++ R)) =
      some (⟨2,[true,true,false,true] ++ L,O a ++ [false,false] ++ R⟩ : Z0) := by rfl
  have h2 : run0 table a ⟨2,[true,true,false,true] ++ L,O a ++ [false,false] ++ R⟩ =
      some ⟨2,[true] ++ Z a ++ [true,false,true] ++ L,[false,false] ++ R⟩ := by
    simpa only [Nat.one_mul,List.append_assoc,List.nil_append,List.cons_append] using
      (sweepR table 2 [true] [] [true] [false] 1 (fun _ _ => rfl) a ([true,false,true] ++ L) ([false,false] ++ R))
  have h3 : run0 table 2 ⟨2,[true] ++ Z a ++ [true,false,true] ++ L,[false,false] ++ R⟩ =
      some ⟨3,Z (a+3) ++ [true,false,true] ++ L,R⟩ := by rfl
  have h4 : run0 table (a+3) ⟨3,Z (a+3) ++ [true,false,true] ++ L,R⟩ =
      some ⟨3,[true,false,true] ++ L,O (a+3) ++ R⟩ := by
    simpa only [Nat.one_mul,List.nil_append,List.append_assoc] using
      (sweepL table 3 [] [] [false] [true] 1 (fun _ _ => rfl) (a+3) ([true,false,true] ++ L) R)
  have h5 : run0 table 2 ⟨3,[true,false,true] ++ L,O (a+3) ++ R⟩ =
      some (A (true::L) (O (a+3) ++ R)) := by rfl
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 3+a+2+(a+3)+2=2*a+10 by omega] at h
  exact h

-- Same sweep when the two zeros are implicit blank padding at the right end.
private theorem a0_end (a : Nat) (L : List Bool) :
    run0 table (2*a+8) (A (false::L) (O a)) = some (A (true::L) (O (a+2))) := by
  cases a with
  | zero => rfl
  | succ a =>
    have h1 : run0 table 3 (A (false::L) (O (a+1))) =
        some (⟨2,[true,true,false,true] ++ L,O a⟩ : Z0) := by rfl
    have h2 : run0 table a ⟨2,[true,true,false,true] ++ L,O a⟩ =
        some ⟨2,[true] ++ Z a ++ [true,false,true] ++ L,[]⟩ := by
      simpa only [Nat.one_mul,List.append_assoc,List.nil_append,List.cons_append,List.append_nil] using
        (sweepR table 2 [true] [] [true] [false] 1 (fun _ _ => rfl) a ([true,false,true] ++ L) [])
    have h3 : run0 table 2 ⟨2,[true] ++ Z a ++ [true,false,true] ++ L,[]⟩ =
        some ⟨3,Z (a+3) ++ [true,false,true] ++ L,[]⟩ := by rfl
    have h4 : run0 table (a+3) ⟨3,Z (a+3) ++ [true,false,true] ++ L,[]⟩ =
        some ⟨3,[true,false,true] ++ L,O (a+3)⟩ := by
      simpa only [Nat.one_mul,List.nil_append,List.append_assoc,List.append_nil] using
        (sweepL table 3 [] [] [false] [true] 1 (fun _ _ => rfl) (a+3) ([true,false,true] ++ L) [])
    have h5 : run0 table 2 ⟨3,[true,false,true] ++ L,O (a+3)⟩ =
        some (A (true::L) (O (a+3))) := by rfl
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show 3+a+2+(a+3)+2=2*(a+1)+8 by omega] at h
    exact h

private theorem a1_gap1 (L R : List Bool) :
    run0 table 7 (A ([true,false,true] ++ L) R) =
      some (A ([true,false] ++ L) (false::R)) := by rfl
private theorem a1_gap2 (L R : List Bool) :
    run0 table 11 (A ([true,false,false,true] ++ L) R) =
      some (A (true::L) ([true,true,false] ++ R)) := by rfl
private theorem a1_gap3 (L R : List Bool) :
    run0 table 8 (A ([true,false,false,false] ++ L) R) =
      some (A L ([true,true,true,false] ++ R)) := by rfl


-- Right block codes and left gap blocks. The terminal count is always positive.
abbrev X : List Bool := [true,true,true,false,false]
abbrev Y : List Bool := [true,true,false,false]
abbrev P : List Bool := X ++ Y
abbrev T (k : Nat) : List Bool := [true,true,false] ++ O (k+1)
abbrev K (j : Nat) : List Bool := [true,true,false] ++ O (7*j+4) ++ [false,false]
abbrev block (j : Nat) : List Bool := [true,false,true] ++ Z (7*j+1) ++ [true,false,true,false,false]

private theorem blank_scan (R : List Bool) :
    run0 table 31 (A [] (X ++ R)) =
      some (A [false,false,false,true,false,true] (O 4 ++ R)) := by rfl

private theorem scan_plain (j : Nat) (L R : List Bool) :
    run0 table (14*j+33) (A (Z 3 ++ true::L) (O (7*j+4) ++ P ++ R)) =
      some (A (true::L) (K (j+1) ++ R)) := by
  have h1 := a0_zero (7*j+6) (Z 2 ++ true::L) (Y ++ R)
  have h2 := a1_gap2 L (O (7*j+6+3) ++ (Y ++ R))
  have h := join0 h1 h2
  rw [show 2*(7*j+6)+10+11=14*j+33 by omega] at h
  have ho : O (7*j+6+1) = O (7*j+4) ++ [true,true,true] := by
    rw [show 7*j+6+1=(7*j+4)+3 by omega]; unfold O; rw [rep_add]; rfl
  have ho' : O (7*(j+1)+4) = O (7*j+6+3) ++ [true,true] := by
    rw [show 7*(j+1)+4=(7*j+6+3)+2 by omega]; unfold O; rw [rep_add]; rfl
  rw [ho] at h
  simp only [K,P,X,Y,ho',List.append_assoc,List.cons_append,List.nil_append] at h ⊢
  exact h

private theorem scan_counted (j k : Nat) (L R : List Bool) :
    run0 table (7*j+14*k+43) (A (Z 3 ++ true::L) (O (7*j+4) ++ K k ++ R)) =
      some (A (Z 3 ++ block j ++ true::L) (O (7*k+4) ++ R)) := by
  let U := [true,false,true,false,false,true] ++ L
  have h1 := a0_one (7*j+5) (Z 2 ++ true::L) (O (7*k+3) ++ [false,false] ++ R)
  have h1' : run0 table (7*j+12) (A (Z 3 ++ true::L) (O (7*j+4) ++ K k ++ R)) =
      some (A (Z (7*j+6) ++ U) (O (7*k+3) ++ [false,false] ++ R)) := by
    rw [show 7*j+5+7=7*j+12 by omega] at h1
    have ho : O (7*j+5+1) = O (7*j+4) ++ [true,true] := by
      rw [show 7*j+5+1=(7*j+4)+2 by omega]; unfold O; rw [rep_add]; rfl
    rw [ho] at h1
    simp only [U,K,List.append_assoc,List.cons_append,List.nil_append] at h1 ⊢
    exact h1
  have h2 := a0_zero (7*k+2) (Z (7*j+5) ++ U) R
  have h2' : run0 table (14*k+14) (A (Z (7*j+6) ++ U) (O (7*k+3) ++ [false,false] ++ R)) =
      some (A (true::(Z (7*j+5) ++ U)) (O (7*k+5) ++ R)) := by
    rw [show 2*(7*k+2)+10=14*k+14 by omega] at h2
    exact h2
  have h3 := a1_gap3 (Z (7*j+2) ++ U) (O (7*k+5) ++ R)
  have h3' : run0 table 8 (A (true::(Z (7*j+5) ++ U)) (O (7*k+5) ++ R)) =
      some (A (Z (7*j+2) ++ U) ([true,true,true,false] ++ O (7*k+5) ++ R)) := by
    exact h3
  have h4 := a0_one 2 (Z (7*j+1) ++ U) (O (7*k+4) ++ R)
  have h4' : run0 table 9 (A (Z (7*j+2) ++ U) ([true,true,true,false] ++ O (7*k+5) ++ R)) =
      some (A (Z 3 ++ block j ++ true::L) (O (7*k+4) ++ R)) := by
    simpa only [U,block,O,Z,rep_add,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h4
  have h := join0 (join0 (join0 h1' h2') h3') h4'
  rw [show (7*j+12)+(14*k+14)+8+9=7*j+14*k+43 by omega] at h
  exact h

private theorem scan_terminal (j k : Nat) (L : List Bool) :
    run0 table (7*j+4*k+58) (A (Z 3 ++ true::L) (O (7*j+4) ++ T k)) =
      some (A (block j ++ true::L) (T (k+2))) := by
  let U := [true,false,true,false,false,true] ++ L
  have h1 := a0_one (7*j+5) (Z 2 ++ true::L) (O k)
  have h1' : run0 table (7*j+12) (A (Z 3 ++ true::L) (O (7*j+4) ++ T k)) =
      some (A (Z (7*j+6) ++ U) (O k)) := by
    rw [show 7*j+5+7=7*j+12 by omega] at h1
    have ho : O (7*j+5+1) = O (7*j+4) ++ [true,true] := by
      rw [show 7*j+5+1=(7*j+4)+2 by omega]; unfold O; rw [rep_add]; rfl
    rw [ho] at h1
    simp only [U,T,List.append_assoc,List.cons_append,List.nil_append] at h1 ⊢
    exact h1
  have h2 := a0_end k (Z (7*j+5) ++ U)
  have h2' : run0 table (2*k+8) (A (Z (7*j+6) ++ U) (O k)) =
      some (A (true::(Z (7*j+5) ++ U)) (O (k+2))) := by exact h2
  have h3 := a1_gap3 (Z (7*j+2) ++ U) (O (k+2))
  have h3' : run0 table 8 (A (true::(Z (7*j+5) ++ U)) (O (k+2))) =
      some (A (Z (7*j+2) ++ U) ([true,true,true,false] ++ O (k+2))) := by exact h3
  have h4 := a0_one 2 (Z (7*j+1) ++ U) (O (k+1))
  have h4' : run0 table 9 (A (Z (7*j+2) ++ U) ([true,true,true,false] ++ O (k+2))) =
      some (A (Z 3 ++ block j ++ true::L) (O (k+1))) := by
    simpa only [U,block,O,Z,rep_add,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h4
  have h5 := a0_end (k+1) (Z 2 ++ block j ++ true::L)
  have h6 := a1_gap2 ([false,true] ++ Z (7*j+1) ++ [true,false,true,false,false,true] ++ L) (O (k+3))
  have h56 : run0 table (2*k+21) (A (Z 3 ++ block j ++ true::L) (O (k+1))) =
      some (A (block j ++ true::L) (T (k+2))) := by
    have h5' : run0 table (2*(k+1)+8) (A (Z 3 ++ block j ++ true::L) (O (k+1))) =
        some (A (true::false::false::true::([false,true] ++ Z (7*j+1) ++ [true,false,true,false,false,true] ++ L)) (O (k+3))) := by
      simpa only [block,O,Z,rep_add,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h5
    have h := join0 h5' h6
    rw [show 2*(k+1)+8+11=2*k+21 by omega] at h
    simpa only [block,T,O,Z,rep_add,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h
  have h := join0 (join0 (join0 (join0 h1' h2') h3') h4') h56
  rw [show (7*j+12)+(2*k+8)+8+9+(2*k+21)=7*j+4*k+58 by omega] at h
  exact h

private theorem drain_base (R : List Bool) :
    run0 table 15 (A [true,false,true] R) = some (A [] (X ++ R)) := by rfl

private theorem drain_zero (L R : List Bool) :
    run0 table 33 (A (block 0 ++ L) R) = some (A L (P ++ R)) := by rfl

private theorem drain_succ (j : Nat) (L R : List Bool) :
    run0 table 46 (A (block (j+1) ++ true::L) R) =
      some (A (Z 3 ++ block j ++ true::L) (O 4 ++ R)) := by
  let U := [true,false,true,false,false,true] ++ L
  have h1 := a1_gap1 (Z (7*j+8) ++ U) R
  have h1' : run0 table 7 (A (block (j+1) ++ true::L) R) =
      some (A (true::false::(Z (7*j+8) ++ U)) (false::R)) := by
    simp only [block,show 7*(j+1)+1=7*j+8 by omega]
    simpa only [U,List.append_assoc,List.cons_append,List.nil_append] using h1
  have h2 := a1_gap3 (Z (7*j+6) ++ U) (false::R)
  have h2' : run0 table 8 (A (true::false::(Z (7*j+8) ++ U)) (false::R)) =
      some (A (Z (7*j+6) ++ U) (X ++ R)) := by exact h2
  have h3 := a0_zero 2 (Z (7*j+5) ++ U) R
  have h3' : run0 table 14 (A (Z (7*j+6) ++ U) (X ++ R)) =
      some (A (true::(Z (7*j+5) ++ U)) (O 5 ++ R)) := by exact h3
  have h4 := a1_gap3 (Z (7*j+2) ++ U) (O 5 ++ R)
  have h4' : run0 table 8 (A (true::(Z (7*j+5) ++ U)) (O 5 ++ R)) =
      some (A (Z (7*j+2) ++ U) ([true,true,true,false] ++ O 5 ++ R)) := by exact h4
  have h5 := a0_one 2 (Z (7*j+1) ++ U) (O 4 ++ R)
  have h5' : run0 table 9 (A (Z (7*j+2) ++ U) ([true,true,true,false] ++ O 5 ++ R)) =
      some (A (Z 3 ++ block j ++ true::L) (O 4 ++ R)) := by
    simpa only [U,block,O,Z,rep_add,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h5
  exact join0 (join0 (join0 (join0 h1' h2') h3') h4') h5'


/-- A finite right word of ordinary or counted blocks ending in a positive
    terminal run. No restriction on counts or the order of the blocks. -/
inductive Word where
  | terminal (k : Nat)
  | plain (w : Word)
  | counted (j : Nat) (w : Word)

def word : Word → List Bool
  | .terminal k => T k
  | .plain w => P ++ word w
  | .counted j w => K j ++ word w

def stackTail : List Nat → List Bool
  | [] => [false,true]
  | j::s => [false,true] ++ Z (7*j+1) ++ [true,false,true,false,false,true] ++ stackTail s
abbrev stack (s : List Nat) : List Bool := true::stackTail s
private theorem stack_cons (j : Nat) (s : List Nat) :
    stack (j::s) = block j ++ stack s := by
  simp only [stack,stackTail,block,List.append_assoc,List.cons_append,List.nil_append]

inductive Section where
  | blank (w : Word)
  | scan (s : List Nat) (j : Nat) (w : Word)
  | drain (s : List Nat) (w : Word)

def config : Section → Z0
  | .blank w => A [] (X ++ word w)
  | .scan s j w => A (Z 3 ++ stack s) (O (7*j+4) ++ word w)
  | .drain s w => A (stack s) (word w)

def advance : Section → Section
  | .blank w => .scan [] 0 w
  | .scan s j (.plain w) => .drain s (.counted (j+1) w)
  | .scan s j (.counted k w) => .scan (j::s) k w
  | .scan s j (.terminal k) => .drain (j::s) (.terminal (k+2))
  | .drain [] w => .blank w
  | .drain (0::s) w => .drain s (.plain w)
  | .drain (Nat.succ j::s) w => .scan (j::s) 0 w

def duration : Section → Nat
  | .blank _ => 31
  | .scan _ j (.plain _) => 14*j+33
  | .scan _ j (.counted k _) => 7*j+14*k+43
  | .scan _ j (.terminal k) => 7*j+4*k+58
  | .drain [] _ => 15
  | .drain (0::_) _ => 33
  | .drain (Nat.succ _::_) _ => 46

theorem duration_pos (s : Section) : 0 < duration s := by
  cases s with
  | blank w => simp [duration]
  | scan s j w => cases w <;> simp only [duration] <;> omega
  | drain s w => cases s with
    | nil => simp [duration]
    | cons j s => cases j <;> simp [duration]

theorem closed (s : Section) : run0 table (duration s) (config s) = some (config (advance s)) := by
  cases s with
  | blank w => exact blank_scan (word w)
  | scan s j w =>
    cases w with
    | plain w =>
      simp only [duration,config,word,advance,List.append_assoc]
      have h := scan_plain j (stackTail s) (word w)
      simp only [List.append_assoc] at h
      exact h
    | counted k w =>
      simp only [duration,config,word,advance,stack_cons,List.append_assoc]
      have h := scan_counted j k (stackTail s) (word w)
      simp only [List.append_assoc] at h
      exact h
    | terminal k =>
      simp only [duration,config,word,advance,stack_cons]
      exact scan_terminal j k (stackTail s)
  | drain s w =>
    cases s with
    | nil => exact drain_base (word w)
    | cons j s =>
      cases j with
      | zero =>
        simp only [duration,config,word,advance,stack_cons]
        exact drain_zero (stack s) (word w)
      | succ j =>
        simp only [duration,config,advance,stack_cons]
        exact drain_succ j (stackTail s) (word w)

def orbitSection : Nat → Section
  | 0 => .blank (.terminal 1)
  | n+1 => advance (orbitSection n)

theorem entry : run0 table 61 ⟨0,[],[]⟩ = some (config (orbitSection 0)) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => config (orbitSection n)) 61 (fun n => duration (orbitSection n))
    entry (fun n => duration_pos (orbitSection n)) (fun n => closed (orbitSection n)) m hm

#print axioms closed
#print axioms never
end BB6.Agent8Raw54.E1OneRC.M139
