"""Reproducible Lean kernel certificate for the first three B-machine samples."""
from pathlib import Path
from tempfile import NamedTemporaryFile
import argparse
import hashlib
import os
from filelock import FileLock

TOTAL = 227097
CHUNK = 8192

def write(path: Path, value: str) -> None:
    with FileLock(str(path)+".lock"):
        with NamedTemporaryFile("w", encoding="utf-8", newline="\n",
                                dir=path.parent, delete=False) as f:
            f.write(value)
            f.flush()
            os.fsync(f.fileno())
            tmp = f.name
        os.replace(tmp, path)

def generate(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    z = 0
    at = 0
    idx = 0
    while at < TOTAL:
        idx += 1
        before = at
        count = min(CHUNK, TOTAL-at)
        for _ in range(count):
            z = 3*(z//2)+4+5*(z%2)
        at += count
        name = f"BTrace{idx:02}"
        parent = f"BTrace{idx-1:02}" if idx>1 else "BTraceCore"
        prev = f"v{idx-1:02}" if idx>1 else "0"
        code = [f"import {parent}", "set_option maxRecDepth 1000000",
                "set_option maxHeartbeats 0", "namespace BB6.BTrace",
                f"def v{idx:02} : Nat := 0x{z:x}",
                f"theorem block{idx:02} : iterG {count} {prev} = v{idx:02} := by decide"]
        if idx==1:
            code.append(f"theorem prefix01 : iterG {at} 0 = v01 := block01")
        else:
            code += [f"theorem prefix{idx:02} : iterG {at} 0 = v{idx:02} := by",
                     "  calc",
                     f"    iterG {at} 0 = iterG {count} (iterG {before} 0) := by",
                     f"      simpa using (iterG_add {before} {count} 0)",
                     f"    _ = iterG {count} v{idx-1:02} := by rw [prefix{idx-1:02}]",
                     f"    _ = v{idx:02} := block{idx:02}"]
        code += ["end BB6.BTrace",""]
        write(out/f"{name}.lean","\n".join(code))
        print(name, at, z.bit_length(), flush=True)
    assert z%2==1
    code = [f"import BTrace{idx:02}", "namespace BB6.BTrace",
            "theorem sample0_odd : (iterG 3 0)%2 = 1 := by decide",
            "theorem sample1_odd : (iterG 25 0)%2 = 1 := by decide",
            "theorem third_sample_odd : (iterG 227097 0)%2 = 1 := by",
            f"  rw [prefix{idx:02}]", "  decide",
            "#print axioms third_sample_odd", "end BB6.BTrace", ""]
    write(out/"BTraceFinal.lean","\n".join(code))
    digest = hashlib.sha256(z.to_bytes((z.bit_length()+7)//8,"big")).hexdigest()
    print("boundary-sha256", digest, "bits", z.bit_length(), flush=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    generate(parser.parse_args().output)
