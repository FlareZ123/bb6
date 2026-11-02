"""Rebuild finite, kernel-checkable Lean P1 rank brackets (Python 3.11+).

Requires filelock. All generated mathematical assertions are checked by Lean;
the Python simulator is used only to propose exact numeral certificates.
"""
from __future__ import annotations

import argparse
import os
import tempfile
from pathlib import Path

from filelock import FileLock


def drain(k: int, c: int) -> tuple[int, int]:
    while c < 2 * k:
        k -= c // 2 + 1
        c = 2 * c + 3
    if c <= 2 * k + 1:
        return 0, 2 * c + 3
    return 4 * k + 4, c - (2 * k + 2)


def step(a: int, c: int) -> tuple[int, int] | None:
    if c == 0:
        return 2, a + 1
    if c == 1:
        return a + 2, 0
    if a % 2 == 0:
        return a + 3, c - 2
    if c == 2:
        return None
    if c == 3:
        return drain(a // 2, 1)
    return drain(a // 2 + 1, c - 2)


def critical(n: int) -> int:
    return 14 * (2**n) - 2 * n - 10


def make_certificate(limit: int) -> str:
    highest_mass = 2 + critical(limit)
    states = [(2, 1)]
    while sum(states[-1]) <= highest_mass:
        following = step(*states[-1])
        if following is None:
            raise ValueError(f"Unexpected halting transition at step {len(states)-1}")
        states.append(following)

    crossings: list[tuple[int, int, int]] = []
    for n in range(limit + 1):
        threshold = 2 + critical(n)
        crossing = next(i for i, s in enumerate(states) if sum(s) >= threshold)
        before, after = states[crossing - 1], states[crossing]
        if crossing < 1 or sum(before) >= threshold or after == (2, critical(n)):
            raise ValueError(f"Target cannot be excluded by bracket at n={n}")
        crossings.append((n, crossing - 1, crossing))

    points = sorted(
        {0, len(states) - 1}
        | set(range(10, len(states), 10))
        | {i for _, p, q in crossings for i in (p, q)}
    )
    sections = [
        "import RankBase\n\nnamespace BB6.Agent7\nopen BB6.P1Reduction\n",
        "theorem trace_0 : iterT 0 (2,1) = some (2,1) := rfl\n",
    ]
    for p, q in zip(points, points[1:]):
        a, c = states[p]
        b, d = states[q]
        count = q - p
        if not 1 <= count <= 10:
            raise AssertionError("Chunk exceeds ten steps")
        sections.append(
            f"""theorem trace_{q} : iterT {q} (2,1) = some ({b},{d}) := by
  rw [show {q} = {p}+{count} by omega, iterT_add, trace_{p}]
  change iterT {count} ({a},{c}) = some ({b},{d})
  rw [← iterFast_correct]
  decide
"""
        )
    for n, p, q in crossings:
        a, c = states[p]
        b, d = states[q]
        sections.append(
            f"""theorem no_critical_{n} :
    ∀ t, iterT t (2,1) ≠ some (2,critical {n}) := by
  apply no_target_bracket {p} ({a},{c}) ({b},{d}) (2,critical {n})
  · exact trace_{p}
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide
"""
        )

    name = "no_first_nine" if limit == 8 else f"no_first_{limit + 1}"
    cases = " ∨ ".join(f"i = {n}" for n in range(limit + 1))
    branches = "|".join("h" for _ in range(limit + 1))
    alternatives = "\n".join(
        f"    | exact no_critical_{n}" for n in range(limit + 1)
    )
    sections.append(
        f"""theorem {name} (i : Nat) (hi : i ≤ {limit}) :
    ∀ t, iterT t (2,1) ≠ some (2,critical i) := by
  have hd : {cases} := by omega
  rcases hd with {branches}
  all_goals subst i
  all_goals first
{alternatives}

#print axioms BB6.Agent7.{name}
#print axioms BB6.Agent7.no_target_bracket
#print axioms BB6.Agent7.no_critical_0
end BB6.Agent7
"""
    )
    print(
        f"n=0..{limit}; computed transitions={len(states)-1}; "
        f"checkpoints={len(points)}; targets={len(crossings)}"
    )
    return "\n".join(sections)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-target", type=int, default=8)
    args = parser.parse_args()
    if args.max_target < 0:
        parser.error("--max-target must be nonnegative")
    path = Path(__file__).with_name("RankCertificate.lean")
    content = make_certificate(args.max_target)
    with FileLock(str(path) + ".lock"):
        if path.exists() and path.read_text(encoding="utf-8") == content:
            print("Existing certificate already matches.")
            return
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(
                "w", encoding="utf-8", dir=path.parent, delete=False
            ) as handle:
                temporary = Path(handle.name)
                handle.write(content)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()


if __name__ == "__main__":
    main()
