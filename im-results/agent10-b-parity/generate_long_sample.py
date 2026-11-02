"""Generate kernel-checked Lean certificates for Machine B's third parity sample.

The generator computes candidate values. Lean verifies every recurrence step:
a generated certificate cannot prove an incorrect claim.
"""
from pathlib import Path
import hashlib
import os
import sys
import tempfile
from filelock import FileLock

sys.set_int_max_str_digits(0)


def generate(total: int = 227097, step: int = 500, group: int = 20) -> None:
    values = [(0, 0)]
    z = 0
    for n in range(1, total + 1):
        z = 3 * (z // 2) + 4 + 5 * (z & 1)
        if n % step == 0 or n == total:
            values.append((n, z))
    assert z % 2 == 1
    points = values[1:]
    batches = [points[i:i + group] for i in range(0, len(points), group)]
    root = Path.cwd()

    with FileLock(str(root / ".agent10_cert_generation.lock")):
        for gi, batch in enumerate(batches):
            prev = values[gi * group]
            module = "Agent10Growth" if gi == 0 else f"SamplePart{gi - 1}"
            lines = [
                f"import {module}",
                "",
                "namespace BB6.Agent10B",
                "set_option maxRecDepth 1000000",
                "set_option maxHeartbeats 0",
                f"theorem section_{batch[-1][0]} : "
                f"iterG {batch[-1][0]} 0 = {batch[-1][1]} := by",
            ]
            if gi > 0:
                lines.append(
                    f"  have h0 : iterG {prev[0]} 0 = {prev[1]}"
                    f" := section_{prev[0]}"
                )
            for hi, (n, value) in enumerate(batch, start=1):
                earlier, _ = values[gi * group + hi - 1]
                lines.append(f"  have h{hi} : iterG {n} 0 = {value} := by")
                if earlier > 0:
                    lines.append(
                        f"    change iterG ({earlier}+{n-earlier}) 0 = {value}"
                    )
                    lines.append(f"    rw [G_iter_add, h{hi-1}]")
                lines.append("    decide")
            lines.append(f"  exact h{len(batch)}")
            if gi == len(batches) - 1:
                lines.extend([
                    "",
                    f"theorem third_sample_odd : (iterG {total} 0)%2=1 := by",
                    f"  rw [section_{total}]",
                    "#print axioms third_sample_odd",
                ])
            lines.append("end BB6.Agent10B")
            result = "\n".join(lines) + "\n"
            path = root / f"SamplePart{gi}.lean"
            with tempfile.NamedTemporaryFile(
                "w", dir=root, encoding="utf-8", delete=False
            ) as output:
                output.write(result)
                temporary = Path(output.name)
            os.replace(temporary, path)
            print(path.name, len(result), hashlib.sha256(result.encode()).hexdigest())
    print("certificate_parts", len(batches))


if __name__ == "__main__":
    generate()
