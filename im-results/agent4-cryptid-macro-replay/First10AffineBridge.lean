import DRegularShift

open DRegular
open BB6.DRegularShift

def cryptidCylinderC : Nat := 1975700577069254261393123959451562008800234946348086
def cryptidCylinderC10 : Nat := 35925965576050291197954676646168812866911688985763244505

def cryptidStart : DRegular.L := ⟨cryptidCylinderC, 0, 0⟩
def cryptidCheckpoint10 : DRegular.L := ⟨cryptidCylinderC10, 4, 1⟩

theorem cryptid_first10_base : DRegular.run 10 cryptidStart = some cryptidCheckpoint10 := by
  decide

theorem cryptid_first10_affine (k : Nat) :
    DRegular.run 10 ⟨3^108*k + cryptidCylinderC, 0, 0⟩ =
      some ⟨3^98*(8^10*k) + cryptidCylinderC10, 4, 1⟩ := by
  have hcanon : DRegular.Canon cryptidStart := by
    simp [DRegular.Canon, cryptidStart, cryptidCylinderC]
  have h := BB6.DRegularShift.run_shift 10 cryptidStart (3^98*k) hcanon
  rw [cryptid_first10_base] at h
  have h3 : 3^108*k = 3^10*(3^98*k) := by
    have hp : 108 = 10+98 := by omega
    rw [hp, Nat.pow_add]
    omega
  have h8 : 8^10*(3^98*k) = 3^98*(8^10*k) := by omega
  simpa [shiftNat, cryptidStart, cryptidCheckpoint10, cryptidCylinderC,
    cryptidCylinderC10, h3, h8, Nat.add_comm] using h

#print axioms cryptid_first10_base
#print axioms cryptid_first10_affine
