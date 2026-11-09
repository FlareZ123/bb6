"""Deterministically generate 41 kernel-checkable Sheep inverse row theorems."""
from math import gcd
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import os

BASE = 1296
PERIOD = 340200

def order_two(modulus: int) -> int:
    assert modulus > 1 and modulus % 2 == 1
    exponent, value = 0, 1
    while True:
        exponent += 1
        value = (2 * value) % modulus
        if value == 1:
            return exponent

def generate(path: Path) -> None:
    src = ["import SheepPower1296Core", "set_option maxRecDepth 4096",
           "set_option maxHeartbeats 0", "namespace SheepPower1296", ""]
    cases, representatives = 0, 0
    for h in range(6):
        D = 3**h
        shift = 3*D
        for a in (range(1, 2) if h == 0 else range(1, 2*h+3)):
            modulus = D*(2**(a+1)+1)
            C = 2*a*D+2**(h+1)
            base = BASE+h+1
            period = order_two(modulus)
            cycle = period//gcd(period, PERIOD)
            assert pow(2, PERIOD*cycle, modulus) == 1
            assert all((pow(2,base+PERIOD*t,modulus)+shift)%modulus
                       != C%modulus for t in range(cycle))
            src += [f"theorem no_h{h}_a{a} (k v : Nat)",
                    f"    (heq : {modulus}*v+{C} = 2^({base}+340200*k)+{shift}) : False := by",
                    "  exact no_generic_equation",
                    f"    {modulus} {base} {shift} {C} {cycle} k v",
                    "    (by decide) (by decide)",
                    "    (by rw [←Nat.powMod_def]; decide)",
                    "    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using",
                    f"      (show ∀ t : Fin {cycle},",
                    f"        (Nat.powMod 2 ({base}+340200*t.val) {modulus}+{shift})%{modulus} ≠ {C}%{modulus} from by decide))",
                    "    heq", ""]
            cases += 1
            representatives += cycle
    assert cases == 41 and representatives == 88
    src += ["#print axioms no_h0_a1", "#print axioms no_h5_a12",
            "end SheepPower1296", ""]
    with FileLock(str(path)+".lock"):
        with NamedTemporaryFile("w",encoding="utf-8",dir=path.parent,delete=False) as f:
            f.write("\n".join(src))
            f.flush()
            os.fsync(f.fileno())
            tmp = f.name
        os.replace(tmp, path)
    print("Generated",cases,"rows and",representatives,"period representatives")

if __name__ == "__main__":
    generate(Path(__file__).with_name("SheepPower1296Rows.lean"))
