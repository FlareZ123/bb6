-- Appendix to be inserted before the final namespace end in Row109Runs.lean
-- The literal original rooted machine string used by the external accelerator.
def rawRLE : String := "1RB0LE_0RC---_1RD0LA_1RE0RF_1LC1RD_1RE1RA"

private def qIndex : Q → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

private def charState : Char → Option Q
  | 'A' => some .A | 'B' => some .B | 'C' => some .C
  | 'D' => some .D | 'E' => some .E | 'F' => some .F
  | _ => none

private def charWrite : Char → Option Bool
  | '0' => some false | '1' => some true | _ => none

private def charMove : Char → Option Int
  | 'L' => some (-1) | 'R' => some 1 | _ => none

private def decodeTriple : List Char → Option (Bool × Int × Q)
  | [w, d, q] => do
    let v ← charWrite w
    let dir ← charMove d
    let st ← charState q
    some (v, dir, st)
  | _ => none

-- Kernel-reducible character representation of the exact 6x2 RLE above.
def rawChars : List Char :=
  ['1','R','B','0','L','E','_',
   '0','R','C','-','-','-','_',
   '1','R','D','0','L','A','_',
   '1','R','E','0','R','F','_',
   '1','L','C','1','R','D','_',
   '1','R','E','1','R','A']

private def decodedAction (q : Q) (b : Bool) : Option (Bool × Int × Q) :=
  decodeTriple ((rawChars.drop (7 * qIndex q + if b then 3 else 0)).take 3)

theorem exact_RLE_table (q : Q) (b : Bool) : decodedAction q b = action q b := by
  cases q <;> cases b <;> decide


def blank : Cfg := ⟨.A, 0, fun _ => false⟩

def root42Writes : List (Int × Bool) :=
  [(0, true), (1, false), (2, true), (3, true), (4, true), (3, false), (2, false), (1, true), (0, false), (-1, true), (0, false), (1, false), (0, true), (1, false), (2, true), (3, true), (4, true), (5, true), (6, true), (5, false), (4, false), (3, true), (4, true), (5, true), (4, false), (3, false), (2, true), (3, true), (4, true), (3, false), (2, false), (1, true), (0, false), (-1, false), (-2, true), (-3, true), (-2, false), (-1, true), (0, true), (-1, false), (-2, true), (-1, false)]

def root42T : Int → Bool :=
  root42Writes.foldl (fun tape (i,b) => write tape i b) (fun _ => false)

set_option maxRecDepth 4096 in
theorem blank42_full_trace : run 42 blank = some ⟨.C,0,root42T⟩ := by
  rfl

def root42Mask (i : Int) : Bool :=
  decide (i = -3 ∨ i = -2 ∨ i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 ∨ i = 6)

theorem root42T_mask (i : Int) : root42T i = root42Mask i := by
  by_cases lo : i < -3
  · simp [root42T, root42Writes, write, root42Mask,
      show i ≠ -3 by omega, show i ≠ -2 by omega, show i ≠ -1 by omega,
      show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
      show i ≠ 3 by omega, show i ≠ 4 by omega, show i ≠ 5 by omega,
      show i ≠ 6 by omega]
  by_cases hi : 6 < i
  · simp [root42T, root42Writes, write, root42Mask,
      show i ≠ -3 by omega, show i ≠ -2 by omega, show i ≠ -1 by omega,
      show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
      show i ≠ 3 by omega, show i ≠ 4 by omega, show i ≠ 5 by omega,
      show i ≠ 6 by omega]
  have cases_i : i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨
      i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases_i with h | h | h | h | h | h | h | h | h | h
  all_goals subst i <;> decide

theorem blank42_full : run 42 blank = some ⟨.C, 0, root42Mask⟩ := by
  rw [blank42_full_trace]
  congr 1
  apply congrArg (fun tape : Int → Bool => Cfg.mk .C 0 tape)
  funext i
  exact root42T_mask i

theorem terminal_B1 (t : Int → Bool) (h : Int) (h1 : t h = true) :
    run 1 ⟨.B,h,t⟩ = none := by
  simp [run, step, action, h1]

theorem terminal_A0_next_B1 (t : Int → Bool) (h : Int)
    (h0 : t h = false) (h1 : t (h+1) = true) :
    run 2 ⟨.A,h,t⟩ = none := by
  have first : step ⟨.A,h,t⟩ = some ⟨.B,h+1,write t h true⟩ := by
    simp [step,action,h0]
  have second : step ⟨.B,h+1,write t h true⟩ = none := by
    simp [step,action,write,h1,show h+1 ≠ h by omega]
  simp only [run,first,second,Option.bind_some,Option.bind_none]

#print axioms BB6Row109Runs.exact_RLE_table
#print axioms BB6Row109Runs.terminal_B1
#print axioms BB6Row109Runs.terminal_A0_next_B1

#print axioms BB6Row109Runs.blank42_full
