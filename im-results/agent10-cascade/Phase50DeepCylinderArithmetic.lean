import Std

namespace Agent10Phase50DeepCylinder

def period : Nat := 3188646
def modulus : Nat := 4782969
def modulus13 : Nat := 3^13
def modulus10 : Nat := 3^10
def modulus7 : Nat := 3^7
def modulus6 : Nat := 3^6

def kModM (a : Nat) : Nat :=
  (97 * 2 ^ ((a - 7) % period) + 48) % modulus

def kModP (a : Nat) : Nat :=
  (97 * 2 ^ ((a - 7) % period) + 48) % period

def rModP (a : Nat) : Nat :=
  (kModP a + 4 + period - (a % period)) % period

def pModM (a : Nat) : Nat :=
  2 ^ (kModP a) % modulus

def qMod243 (a : Nat) : Nat :=
  2 ^ ((kModP a % 162 + 162 - (a % 162)) % 162) % 243

def bModM (a : Nat) : Nat :=
  ((2 * kModM a + 7) * (2 ^ (rModP a) % modulus)) % modulus

def xMod3_13 (a : Nat) : Nat :=
  (80 * pModM a + 2 * kModM a + 13 + 3 * modulus
    - 2 * bModM a) % modulus / 3

def x1Mod27 (a : Nat) : Nat :=
  (((248 * pModM a + 20 * modulus - 8 * bModM a
    - 10 * kModM a + 25) % modulus) / 9) % 27

def x2Mod3_10 (a : Nat) : Nat :=
  (16 * (xMod3_13 a / 27) + 10 * modulus10
    - 4 * (pModM a % modulus10)
    - 2 * (kModM a % modulus10) - 1) % modulus10

def x5Mod3_7 (a : Nat) : Nat :=
  (128 * (xMod3_13 a / 729) + 3 * modulus7
    - (pModM a % modulus7)
    - 2 * (kModM a % modulus7) + 3) % modulus7

def x6Mod3_6 (a : Nat) : Nat :=
  (256 * (xMod3_13 a / 729) + 10 * modulus6
    - 3 * (pModM a % modulus6)
    - 6 * (kModM a % modulus6) + 9) % modulus6

def g0Mod9 (a : Nat) : Nat :=
  ((26368 * qMod243 a + 74 * (kModM a % 243) + 243 - 23) % 243) / 27

def a0Mod3 (a : Nat) : Nat :=
  (4 * (pModM a % 3) + 2 * (kModM a % 3) + 1) % 3

def kMod54 (a : Nat) : Nat :=
  (97 * 2 ^ ((a - 7) % 18) + 48) % 54

def rhoMod54 (a : Nat) : Nat :=
  (kMod54 a + 6 * a) % 54

theorem period_divides_486 : period % 486 = 0 ∧ period / 486 = 6561 := by
  decide

/-- Exact representative arithmetic for the a = 1238 phase-50 cylinder.
    The general period lift and the interval/parent-tree argument are
    recorded separately in the accompanying research note. -/
theorem phase50_266_1238_residues :
    1238 % 486 = 266 ∧
    kMod54 1238 = 44 ∧
    rhoMod54 1238 = 20 ∧
    xMod3_13 1238 = 712233 ∧
    x1Mod27 1238 = 21 ∧
    x2Mod3_10 1238 = 32799 ∧
    x5Mod3_7 1238 = 1595 ∧
    x6Mod3_6 1238 = 14 ∧
    g0Mod9 1238 = 1 ∧
    a0Mod3 1238 = 0 := by
  decide

#print axioms phase50_266_1238_residues

end Agent10Phase50DeepCylinder
