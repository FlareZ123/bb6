import Agent49Eleven81Source

/-!
Exactly eleven distinct neutral radix-81 digits for the full original #623
B-drain: nine pair compositions from residues 0,6,8 modulo 9 plus two
new primitive digits 30 and 48. The complete output theorem and unique-word
code hold for arbitrary starting first counters and all word lengths.
This construction is synthetic and does not settle blank-root reachability.
-/
namespace BB6.Agent49Eleven81FamilySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8SafeBudgetSource
open BB6.Agent49ThirdNinefoldSource
open BB6.Agent49Eleven81Source

def residue9 : Digit → Nat
  | .zero => 0
  | .six => 6
  | .eight => 8

def charge9 : Digit → Nat
  | .zero => 2
  | .six => 4
  | .eight => 2

theorem drain9_step (z : Digit) (a b d : Nat) (hb : 0<b) :
    drainB a (9*b+residue9 z) d =
      drainB a b (d+24*b+3*residue9 z+charge9 z) := by
  cases z with
  | zero => simpa [residue9,charge9] using drainB_nine_zero a b d hb
  | six => simpa [residue9,charge9,Nat.add_assoc] using drainB_nine_pump a b d
  | eight => simpa [residue9,charge9,Nat.add_assoc] using drain_nine_eight a b d

theorem drain9_twice (outer inner : Digit) (a b d : Nat) (hb : 0<b) :
    drainB a (9*(9*b+residue9 inner)+residue9 outer) d =
      drainB a b
        (d+240*b+3*(9*residue9 inner+residue9 outer)+charge9 inner+charge9 outer) := by
  have hp : 0<9*b+residue9 inner := by
    cases inner <;> simp only [residue9] <;> omega
  rw [drain9_step outer a (9*b+residue9 inner) d hp]
  rw [drain9_step inner a b
    (d+24*(9*b+residue9 inner)+3*residue9 outer+charge9 outer) hb]
  congr 1 <;> omega

theorem drain9_twice_norm (outer inner : Digit) (a b d : Nat) (hb : 0<b) :
    drainB a (81*b+9*residue9 inner+residue9 outer) d =
      drainB a b
        (d+240*b+3*(9*residue9 inner+residue9 outer)+charge9 inner+charge9 outer) := by
  have h := drain9_twice outer inner a b d hb
  have lhs :
      9*(9*b+residue9 inner)+residue9 outer =
        81*b+9*residue9 inner+residue9 outer := by omega
  rw [lhs] at h
  exact h

inductive Letter where
  | r00 | r06 | r08 | r30 | r48 | r54 | r60 | r62 | r72 | r78 | r80
  deriving DecidableEq

def residue81 : Letter → Nat
  | .r00 => 0 | .r06 => 6 | .r08 => 8 | .r30 => 30 | .r48 => 48
  | .r54 => 54 | .r60 => 60 | .r62 => 62 | .r72 => 72 | .r78 => 78 | .r80 => 80

def charge81 : Letter → Nat
  | .r00 => 4 | .r06 => 6 | .r08 => 4 | .r30 => 6 | .r48 => 8
  | .r54 => 6 | .r60 => 8 | .r62 => 6 | .r72 => 4 | .r78 => 6 | .r80 => 4

theorem residue81_lt (z : Letter) : residue81 z<81 := by
  cases z <;> decide

theorem residue81_even (z : Letter) : residue81 z%2=0 := by
  cases z <;> decide

theorem charge81_even (z : Letter) : charge81 z%2=0 := by
  cases z <;> decide

theorem residue81_injective (x y : Letter) (h : residue81 x=residue81 y) : x=y := by
  cases x <;> cases y <;> simp_all [residue81]

/-- Uniform all-outcome conjugacy for each of eleven distinct residues mod 81. -/
theorem drain81_step (z : Letter) (a b d : Nat) (hb : 0<b) :
    drainB a (81*b+residue81 z) d =
      drainB a b (d+240*b+3*residue81 z+charge81 z) := by
  cases z with
  | r00 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .zero .zero a b d hb
  | r06 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .six .zero a b d hb
  | r08 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .eight .zero a b d hb
  | r30 => simpa [residue81,charge81,Nat.add_assoc] using drain_81_thirty a b d
  | r48 => simpa [residue81,charge81,Nat.add_assoc] using drain_81_fortyeight a b d
  | r54 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .zero .six a b d hb
  | r60 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .six .six a b d hb
  | r62 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .eight .six a b d hb
  | r72 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .zero .eight a b d hb
  | r78 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .six .eight a b d hb
  | r80 => simpa [residue81,charge81,residue9,charge9,Nat.add_assoc] using
      drain9_twice_norm .eight .eight a b d hb

def block81 : List Letter → Nat
  | [] => 6
  | z :: w => 81*block81 w+residue81 z

def blockCharge81 : List Letter → Nat
  | [] => 4
  | z :: w => blockCharge81 w + charge81 z

theorem block81_positive (w : List Letter) : 0<block81 w := by
  induction w with
  | nil => decide
  | cons z w ih => simp only [block81]; omega

theorem block81_six (w : List Letter) : 6≤block81 w := by
  cases w with
  | nil => decide
  | cons z w =>
    have hp := block81_positive w
    simp only [block81]
    omega

theorem block81_even (w : List Letter) : block81 w%2=0 := by
  induction w with
  | nil => decide
  | cons z w ih =>
    simp only [block81]
    have h := residue81_even z
    omega

theorem blockCharge81_even (w : List Letter) : blockCharge81 w%2=0 := by
  induction w with
  | nil => decide
  | cons z w ih =>
    simp only [blockCharge81]
    have h := charge81_even z
    omega

/-- Every finite word over the eleven-symbol alphabet has a unique block. -/
theorem block81_injective : ∀ x y : List Letter,
    block81 x=block81 y → x=y := by
  intro x
  induction x with
  | nil =>
    intro y he
    cases y with
    | nil => rfl
    | cons z w =>
      simp only [block81] at he
      have hp := block81_positive w
      omega
  | cons z x ih =>
    intro y he
    cases y with
    | nil =>
      simp only [block81] at he
      have hp := block81_positive x
      omega
    | cons z' y =>
      simp only [block81] at he
      have hres : residue81 z = residue81 z' := by
        have hz := residue81_lt z
        have hz' := residue81_lt z'
        omega
      have hz : z=z' := residue81_injective z z' hres
      subst z'
      have hblocks : block81 x=block81 y := by omega
      cases ih y hblocks
      rfl

/-- Every word has a completely explicit successful return for all a,d. -/
theorem block81_drain (a : Nat) (w : List Letter) (d : Nat) :
    drainB a (block81 w) d =
      some (.D a (d+3*block81 w+blockCharge81 w)) := by
  induction w generalizing d with
  | nil =>
    simp only [block81,blockCharge81]
    have h : drainB a 6 d = drainB a 0 (d+22) := by
      simpa only [Nat.zero_mul, Nat.zero_add] using drainB_nine_pump a 0 d
    rw [h]
    simp [drainB]
  | cons z w ih =>
    simp only [block81,blockCharge81]
    rw [drain81_step z a (block81 w) d (block81_positive w), ih]
    simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
    omega

#print axioms drain81_step
#print axioms block81_injective
#print axioms block81_drain
end BB6.Agent49Eleven81FamilySource
