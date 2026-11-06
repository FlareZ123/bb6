"""Proof-only follow-up for two exact failed Lean rewrites in patch03.

Fixes automatic nested application of append_pow_succ. Uses the *proved*
ListBlank.append_pow_comm for a unary zero-block, preserving the original
symbolic reachability lemmas, machine and final is_halt statement.
"""
from pathlib import Path
import fcntl
import os
import sys
import tempfile

target = Path(sys.argv[1])
lock = target.with_suffix(target.suffix + ".agent12-fix04.lock")
with open(lock, "a+", encoding="utf-8") as guard:
    fcntl.flock(guard.fileno(), fcntl.LOCK_EX)
    original = target.read_text(encoding="utf-8")
    one = """  rw [ListBlank.append_pow_succ] at h12
  rw [h_z2] at h12
  rw [ListBlank.append_pow_succ, encM_replicate_zero] at h12"""
    one_fixed = """  rw [← h_z1] at h12
  rw [ListBlank.append_pow_comm ([0] : List (Fin 2)) (d0 + 1)] at h12
  rw [encM_replicate_zero] at h12"""
    two = """  rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ,
    encM_replicate_zero] at h12"""
    two_fixed = """  rw [ListBlank.append_pow_succ, encM_replicate_zero] at h12"""
    assert original.count(one) == 1 and original.count(two) == 1
    out = original.replace(one, one_fixed, 1).replace(two, two_fixed, 1)
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
        tmp = writer.name
    os.replace(tmp, target)
print("Agent12 proof-only rewrite repair04:", target)
