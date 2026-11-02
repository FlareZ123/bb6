from pathlib import Path

path = Path("im-results/agent12-backwards/P1R382AffineReflection.lean")
source = path.read_text(encoding="utf-8")
old = """    dsimp [n]
    omega
  intro hr
"""
new = """    have hmult : (14*2^n)%4=0 := by
      rw [Nat.mul_mod,hp]
    have hnmod : n%2=0 := by dsimp [n]; omega
    omega
  intro hr
"""
assert source.count(old) == 1
path.write_text(source.replace(old, new).replace("private ", ""), encoding="utf-8")
