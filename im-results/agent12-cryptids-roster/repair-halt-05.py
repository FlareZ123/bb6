"""Fifth proof-only compatibility patch for the pinned Cryptids halt source.

The local Lean 4.36.0-rc2 rewrite gate checked both ListBlank rewrite sequences
against the exact helper-lemma types. This patch uses the already proved
zeros_append_cons_zero helper rather than brittle nested append rewrites.
It changes no transition, semantic definition, or final theorem statement.
"""
from pathlib import Path
import fcntl
import os
import sys
import tempfile

target = Path(sys.argv[1])
lock = target.with_suffix(target.suffix + ".agent12-fix05.lock")

with open(lock, "a+", encoding="utf-8") as guard:
    fcntl.flock(guard.fileno(), fcntl.LOCK_EX)
    original = target.read_text(encoding="utf-8")

    first_old = """  rw [← h_z1] at h12
  rw [ListBlank.append_pow_comm ([0] : List (Fin 2)) (d0 + 1)] at h12
  rw [encM_replicate_zero] at h12"""
    first_new = """  rw [zeros_append_cons_zero (d0 + 1) ((0 : Fin 2) >> encM L1)] at h12
  rw [zeros_append_cons_zero (d0 + 2) (encM L1)] at h12
  rw [encM_replicate_zero] at h12"""

    second_old = """  rw [ListBlank.append_pow_succ, encM_replicate_zero] at h12"""
    second_new = """  rw [zeros_append_cons_zero d2 (encM (bumpM L))] at h12
  rw [encM_replicate_zero] at h12
  simp only [List.replicate_succ, List.cons_append, encM_cons_zero,
    ListBlank.append_cons, ListBlank.append_nil] at h12"""

    if original.count(first_old) != 1:
        raise ValueError(f"Expected exactly one first failed rewrite block, found {original.count(first_old)}")
    if original.count(second_old) != 1:
        raise ValueError(f"Expected exactly one second failed rewrite block, found {original.count(second_old)}")
    if original.count("private lemma zeros_append_cons_zero") != 1:
        raise ValueError("The previously proved zeros_append_cons_zero helper is missing or duplicated")

    out = original.replace(first_old, first_new, 1).replace(second_old, second_new, 1)

    assert out.split("-- END TRUSTED DEFINITIONS")[0] == original.split("-- END TRUSTED DEFINITIONS")[0]
    assert out.count("def target_tm") == original.count("def target_tm") == 1
    assert out.count("theorem is_halt") == original.count("theorem is_halt") == 1
    assert out[out.index("theorem is_halt"):].split(":=", 1)[0] == (
        original[original.index("theorem is_halt"):].split(":=", 1)[0]
    )

    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=str(target.parent), delete=False
    ) as writer:
        writer.write(out)
        temp_name = writer.name
    os.replace(temp_name, target)

print("Agent12 proof-only rewrite repair05:", target)
print("Original bytes", len(original), "repaired bytes", len(out))
