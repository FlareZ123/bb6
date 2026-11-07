import Lean.Elab.Tactic.Omega

namespace BB429OddExcursion

structure Zipper where
  state : Nat
  left : List Bool
  current : Bool
  right : List Bool
  deriving Repr, DecidableEq

def z (s : Nat) (l : List Bool) (b : Bool) (r : List Bool) : Zipper :=
  ⟨s,l,b,r⟩

def action : Nat → Bool → Option (Nat × Bool × Bool)
 | 0, false => some (1,true,true)
 | 0, true => some (5,false,false)
 | 1, false => some (2,true,true)
 | 1, true => some (0,true,true)
 | 2, false => some (3,false,true)
 | 2, true => some (1,false,true)
 | 3, false => some (4,true,false)
 | 3, true => none
 | 4, false => some (0,false,false)
 | 4, true => some (4,true,false)
 | 5, false => some (3,true,true)
 | 5, true => some (0,true,false)
 | _, _ => none

def one (c : Zipper) : Option Zipper := do
  let (s,w,rightward) ← action c.state c.current
  if rightward then
    match c.right with
    | [] => some (z s (w::c.left) false [])
    | a::rest => some (z s (w::c.left) a rest)
  else
    match c.left with
    | [] => some (z s [] false (w::c.right))
    | a::rest => some (z s rest a (w::c.right))

def run : Nat → Zipper → Option Zipper
 | 0,c => some c
 | n+1,c => (one c).bind (run n)

theorem run_add (m n : Nat) (c : Zipper) :
  run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add,run]
    cases h : one c with
    | none => simp
    | some d => simpa [h] using ih d

def tens : Nat → List Bool
 | 0 => []
 | n+1 => true :: false :: tens n

theorem apair (l r : List Bool) :
  run 2 (z 0 (true::true::l) true r) =
    some (z 0 l true (true::false::r)) := by rfl

theorem apair_low (r : List Bool) :
  run 2 (z 0 [true] true r) =
    some (z 0 [] false (true::false::r)) := by rfl

theorem af_pairs (j : Nat) (l r : List Bool) :
  run (2*j) (z 0 ((List.replicate (2*j) true) ++ l) true r) =
    some (z 0 l true ((tens j) ++ r)) := by
  induction j generalizing l r with
  | zero => simp [run,tens]
  | succ j ih =>
    have hrep : List.replicate (2*(j+1)) true ++ l =
      List.replicate (2*j) true ++ (true::true::l) := by
      rw [show 2*(j+1)=2*j+2 by omega, ← List.replicate_append_replicate]
      simp [List.append_assoc]
    rw [show 2*(j+1)=2*j+2 by omega,run_add]
    have hrep' : List.replicate (2*j+2) true ++ l =
        List.replicate (2*j) true ++ (true::true::l) := by
      simpa [show 2*(j+1)=2*j+2 by omega] using hrep
    rw [hrep',ih]
    simp [apair,tens]

theorem nine (r : List Bool) :
  run 9 (z 0 [] true (true::r)) =
    some (z 0 [true,false,true,true] true r) := by rfl

theorem four (r : List Bool) :
  run 4 (z 0 [true,false,true,true] true r) =
    some (z 0 [true,true,true,true] false r) := by rfl

theorem a_right_two (l r : List Bool) :
  run 2 (z 0 l false (true::false::r)) =
    some (z 0 (true::true::l) false r) := by rfl

theorem b_right_two (l r : List Bool) :
  run 2 (z 1 l false (true::false::r)) =
    some (z 1 (false::true::l) false r) := by rfl

theorem a_right_pairs (j : Nat) (l r : List Bool) :
  ∃ l', run (2*j) (z 0 l false (tens j ++ r)) = some (z 0 l' false r) := by
  induction j generalizing l with
  | zero => exact ⟨l,by simp [run,tens]⟩
  | succ j ih =>
    obtain ⟨l',hl'⟩ := ih (true::true::l)
    refine ⟨l',?_⟩
    rw [show 2*(j+1)=2+2*j by omega,run_add]
    simp [tens,a_right_two,hl']

theorem b_right_pairs (j : Nat) (l r : List Bool) :
  ∃ l', run (2*j) (z 1 l false (tens j ++ r)) = some (z 1 l' false r) := by
  induction j generalizing l with
  | zero => exact ⟨l,by simp [run,tens]⟩
  | succ j ih =>
    obtain ⟨l',hl'⟩ := ih (false::true::l)
    refine ⟨l',?_⟩
    rw [show 2*(j+1)=2+2*j by omega,run_add]
    simp [tens,b_right_two,hl']

theorem e_first (l r : List Bool) :
  run 1 (z 4 (true::l) false r) = some (z 0 l true (false::r)) := by rfl

theorem a_zero (l r : List Bool) :
  run 1 (z 0 l false (false::r)) = some (z 1 (true::l) false r) := by rfl

theorem b_zero (l r : List Bool) :
  run 1 (z 1 l false (false::r)) = some (z 2 (true::l) false r) := by rfl

theorem a_even_end (l : List Bool) :
  run 2 (z 0 l false [false,true]) = some (z 2 (true::true::l) true []) := by rfl

/-- Synthetic input: E scans zero, n marked cells immediately to its
    left, a marked cell one position to its right, and blank otherwise. -/
def prepared (n : Nat) : Zipper := z 4 (List.replicate n true) false [true]

/-- A genuine-table synthetic run with any odd left block length >= 3
    reaches the fatal C/01 configuration after 2*n+12 successful moves. -/
theorem odd_prepared_fatal (k : Nat) :
  ∃ l, run (2*(2*k+3)+12) (prepared (2*k+3)) = some (z 2 l false [true]) := by
  have hs : prepared (2*k+3) =
      z 4 (true::(List.replicate (2*(k+1)) true)) false [true] := by
    change z 4 (List.replicate (2*k+3) true) false [true] = _
    rw [show 2*k+3=(2*(k+1))+1 by omega,List.replicate_succ]
  have h1 : run 1 (prepared (2*k+3)) =
      some (z 0 (List.replicate (2*(k+1)) true) true [false,true]) := by
    rw [hs];exact e_first _ _
  have h2 : run (2*(k+1)) (z 0 (List.replicate (2*(k+1)) true) true [false,true]) =
      some (z 0 [] true (tens (k+1) ++ [false,true])) := by
    simpa using af_pairs (k+1) [] [false,true]
  have h9 := nine (false::tens k ++ [false,true])
  have h4 := four (false::tens k ++ [false,true])
  have hA := a_zero [true,true,true,true] (tens k ++ [false,true])
  obtain ⟨l',hp⟩ := b_right_pairs k (true::[true,true,true,true]) [false,true]
  have hB := b_zero l' [true]
  refine ⟨true::l',?_⟩
  have hn : 2*(2*k+3)+12 = 1+2*(k+1)+9+4+1+2*k+1 := by omega
  rw [hn]
  rw [show 1+2*(k+1)+9+4+1+2*k+1 =
       1+(2*(k+1)+(9+(4+(1+(2*k+1))))) by omega]
  rw [run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,h2]
  simp only [Option.bind_some]
  have h9' : run 9 (z 0 [] true (tens (k+1) ++ [false,true])) =
      some (z 0 [true,false,true,true] true (false::tens k ++ [false,true])) := by
    simpa [tens] using h9
  rw [run_add,h9']
  simp only [Option.bind_some]
  rw [run_add,h4]
  simp only [Option.bind_some]
  have hA' : run 1 (z 0 [true,true,true,true] false
      (false::tens k ++ [false,true])) =
      some (z 1 (true::[true,true,true,true]) false (tens k ++ [false,true])) := by
    simpa only [List.cons_append] using hA
  rw [run_add,hA']
  simp only [Option.bind_some]
  rw [run_add,hp]
  simp only [Option.bind_some]
  simpa using hB

/-- An even block of positive length reaches C reading the marked right
    boundary after 2*n+3 moves, unlike the odd fatal C/0 event. -/
theorem even_prepared_crosses (k : Nat) :
  ∃ l, run (2*(2*k+2)+3) (prepared (2*k+2)) = some (z 2 l true []) := by
  have hs : prepared (2*k+2) = z 4
      (true::(List.replicate (2*k) true ++ [true])) false [true] := by
    change z 4 (List.replicate (2*k+2) true) false [true] = _
    rw [show 2*k+2=(2*k+1)+1 by omega,List.replicate_succ]
    rw [show 2*k+1=(2*k)+1 by omega,List.replicate_succ']
  have h1 : run 1 (prepared (2*k+2)) =
      some (z 0 (List.replicate (2*k) true ++ [true]) true [false,true]) := by
    rw [hs];exact e_first _ _
  have h2 := af_pairs k [true] [false,true]
  have hlow := apair_low (tens k ++ [false,true])
  obtain ⟨l',hR⟩ := a_right_pairs (k+1) [] [false,true]
  refine ⟨true::true::l',?_⟩
  have hn : 2*(2*k+2)+3=1+2*k+2+2*(k+1)+2 := by omega
  rw [hn]
  rw [show 1+2*k+2+2*(k+1)+2 =
       1+(2*k+(2+(2*(k+1)+2))) by omega]
  rw [run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,h2]
  simp only [Option.bind_some]
  rw [run_add,hlow]
  simp only [Option.bind_some]
  have hR' : run (2*(k+1))
       (z 0 [] false (true::false::(tens k ++ [false,true]))) =
       some (z 0 l' false [false,true]) := by
    simpa [tens] using hR
  rw [run_add,hR']
  simp only [Option.bind_some]
  exact a_even_end _

/-- No fixed-length left context distinguishes these two synthetic outcomes. -/
theorem arbitrary_width_prefix_ambiguity (width : Nat) :
   (prepared (2*width+3)).left.take width =
     (prepared (2*width+4)).left.take width ∧
   (∃ l, run (2*(2*width+3)+12) (prepared (2*width+3)) =
      some (z 2 l false [true])) ∧
   (∃ l, run (2*(2*width+4)+3) (prepared (2*width+4)) =
      some (z 2 l true [])) := by
  constructor
  · change (List.replicate (2*width+3) true).take width =
        (List.replicate (2*width+4) true).take width
    simp only [List.take_replicate]
    rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]
  constructor
  · exact odd_prepared_fatal width
  · have h := even_prepared_crosses (width+1)
    simpa [show 2*(width+1)+2=2*width+4 by omega] using h

#print axioms odd_prepared_fatal
#print axioms even_prepared_crosses
#print axioms arbitrary_width_prefix_ambiguity
end BB429OddExcursion
