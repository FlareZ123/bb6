import WallTelescopingSource
import wall_prefix_carry_cylinders
import WallPrefixListBridge

namespace BB6.Agent9WallCarryBridge

open BB6.Agent43WallTelescoping
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6WallCarry

/-- The source and bridge weighted-list folds are extensionally equal. -/
theorem source_costWeightedSum_eq (n : Nat) :
    ∀ A : List Nat,
      BB6.Agent43WallTelescoping.costWeightedSum n A =
        BB6WallBridge.costWeightedSum n A := by
  intro A
  induction A with
  | nil => rfl
  | cons s A ih =>
      simp [BB6.Agent43WallTelescoping.costWeightedSum,
        BB6WallBridge.costWeightedSum, BB6WallBridge.weight, ih]

/-- The two independently named Boolean folds have the same recursion. -/
theorem sumBits_eq (n j : Nat) :
    ∀ xs : List Bool,
      BB6WallBridge.sumBits n j xs = BB6WallCarry.sumBits n j xs := by
  intro xs
  induction xs generalizing j with
  | nil => rfl
  | cons b xs ih =>
      simp [BB6WallBridge.sumBits, BB6WallCarry.sumBits, ih]

theorem bitExpr_eq (n : Nat) (rest : List Bool) :
    BB6WallBridge.bitExpr n rest = BB6WallCarry.bitExpr n rest := by
  simp [BB6WallBridge.bitExpr, BB6WallCarry.bitExpr, sumBits_eq]

/-- Compose Agent 43's duplicate-free source wall list with Agent 50's
    characteristic-prefix bridge and carry obstruction. -/
theorem sourceWall_noPrefix_of_carry
    (n b d m z K : Nat)
    (hn : 14 ≤ n)
    (hsrc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20 = 12*2^n)
    (hK : 1 ≤ K) (hKn : K ≤ n) (hKm : K ≤ m)
    (hcarry : ¬ ∃ rest : List Bool,
      rest.length = K-1 ∧ bitExpr n rest % 2^K = 1) :
    False := by
  obtain ⟨A, hnd, hlt, hzero, hstart, hId⟩ :=
    source_wall_cost_list_identity n b d m z hn hsrc hw
  have hmpos : 0 < m := by omega
  have h0 : 0 ∈ A := hstart hmpos
  have hKn' : (K-1)+1 ≤ n := by
    simpa [Nat.sub_add_cancel hK] using hKn
  have hKm' : (K-1)+1 ≤ m := by
    simpa [Nat.sub_add_cancel hK] using hKm
  have hcarry' : ¬ ∃ rest : List Bool,
      rest.length = K-1 ∧
        BB6WallBridge.bitExpr n rest % 2^((K-1)+1) = 1 := by
    intro hex
    rcases hex with ⟨rest, hlen, hbit⟩
    apply hcarry
    refine ⟨rest, hlen, ?_⟩
    simpa [Nat.sub_add_cancel hK, bitExpr_eq] using hbit
  have hneq := BB6WallBridge.wall_identity_impossible
    n m (K-1) (costPowSum A) A hnd h0 hKn' hKm' hcarry'
  have hId' := hId
  rw [source_costWeightedSum_eq n A] at hId'
  exact hneq hId'

theorem sourceWall_excludes_familyI_h1
    (t b d m z u : Nat)
    (hU : 1058*u+636 = 17*2^(5362+595056*(1+2^56*t)))
    (hWallCost : m = 14*u-(5362+595056*(1+2^56*t))+6)
    (hsrc : CountCone
      (14*2^(5362+595056*(1+2^56*t))-2*(5362+595056*(1+2^56*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(5362+595056*(1+2^56*t))+20 =
      12*2^(5362+595056*(1+2^56*t))) : False := by
  let n := 5362+595056*(1+2^56*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1058*u+636 = 17*2^n := by simpa [n] using hU
  have hWallCost' : m = 14*u-n+6 := by simpa [n] using hWallCost
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hWallCost']
    have hrestart := familyI_terminal_m_ge_n n u hn hU'
    omega
  have hKn : 60 ≤ n := by dsimp [n]; omega
  have hKm : 60 ≤ m := by omega
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 60-1 ∧ bitExpr n rest % 2^60 = 1 := by
    simpa [n] using noPrefix_familyI_h1 t
  exact sourceWall_noPrefix_of_carry n b d m z 60 hn hsrc' hw'
    (by decide) hKn hKm hcarry

theorem sourceWall_excludes_familyI_h2
    (t b d m z u : Nat)
    (hU : 1058*u+636 = 17*2^(5362+595056*(2+2^8*t)))
    (hWallCost : m = 14*u-(5362+595056*(2+2^8*t))+6)
    (hsrc : CountCone
      (14*2^(5362+595056*(2+2^8*t))-2*(5362+595056*(2+2^8*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(5362+595056*(2+2^8*t))+20 =
      12*2^(5362+595056*(2+2^8*t))) : False := by
  let n := 5362+595056*(2+2^8*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1058*u+636 = 17*2^n := by simpa [n] using hU
  have hWallCost' : m = 14*u-n+6 := by simpa [n] using hWallCost
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hWallCost']
    have hrestart := familyI_terminal_m_ge_n n u hn hU'
    omega
  have hKn : 12 ≤ n := by dsimp [n]; omega
  have hKm : 12 ≤ m := by omega
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 12-1 ∧ bitExpr n rest % 2^12 = 1 := by
    simpa [n] using noPrefix_familyI_h2 t
  exact sourceWall_noPrefix_of_carry n b d m z 12 hn hsrc' hw'
    (by decide) hKn hKm hcarry

theorem sourceWall_excludes_familyII_h1
    (t b d m z u : Nat)
    (hU : 1198*u+712 = 87*2^(9538+703248*(1+2^10*t)))
    (hWallCost : m = 14*u-(9538+703248*(1+2^10*t))+6)
    (hsrc : CountCone
      (14*2^(9538+703248*(1+2^10*t))-2*(9538+703248*(1+2^10*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(9538+703248*(1+2^10*t))+20 =
      12*2^(9538+703248*(1+2^10*t))) : False := by
  let n := 9538+703248*(1+2^10*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1198*u+712 = 87*2^n := by simpa [n] using hU
  have hWallCost' : m = 14*u-n+6 := by simpa [n] using hWallCost
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hWallCost']
    have hrestart := familyII_terminal_m_ge_n n u hn hU'
    omega
  have hKn : 14 ≤ n := by dsimp [n]; omega
  have hKm : 14 ≤ m := by omega
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 14-1 ∧ bitExpr n rest % 2^14 = 1 := by
    simpa [n] using noPrefix_familyII_h1 t
  exact sourceWall_noPrefix_of_carry n b d m z 14 hn hsrc' hw'
    (by decide) hKn hKm hcarry

theorem sourceWall_excludes_familyII_h2
    (t b d m z u : Nat)
    (hU : 1198*u+712 = 87*2^(9538+703248*(2+2^18*t)))
    (hWallCost : m = 14*u-(9538+703248*(2+2^18*t))+6)
    (hsrc : CountCone
      (14*2^(9538+703248*(2+2^18*t))-2*(9538+703248*(2+2^18*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(9538+703248*(2+2^18*t))+20 =
      12*2^(9538+703248*(2+2^18*t))) : False := by
  let n := 9538+703248*(2+2^18*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1198*u+712 = 87*2^n := by simpa [n] using hU
  have hWallCost' : m = 14*u-n+6 := by simpa [n] using hWallCost
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hWallCost']
    have hrestart := familyII_terminal_m_ge_n n u hn hU'
    omega
  have hKn : 22 ≤ n := by dsimp [n]; omega
  have hKm : 22 ≤ m := by omega
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 22-1 ∧ bitExpr n rest % 2^22 = 1 := by
    simpa [n] using noPrefix_familyII_h2 t
  exact sourceWall_noPrefix_of_carry n b d m z 22 hn hsrc' hw'
    (by decide) hKn hKm hcarry

#print axioms sourceWall_noPrefix_of_carry
#print axioms sourceWall_excludes_familyI_h1
#print axioms sourceWall_excludes_familyI_h2
#print axioms sourceWall_excludes_familyII_h1
#print axioms sourceWall_excludes_familyII_h2

end BB6.Agent9WallCarryBridge
