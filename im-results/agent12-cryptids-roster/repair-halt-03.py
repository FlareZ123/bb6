"""Third asserted proof-only compatibility patch for one original Cryptids halter.

Both remaining Lean errors after patches 01 and 02 were ordinary
ListBlank zero-power rewrites in two macro-step composition lemmas.
The existing original source ListBlank.append_pow_succ and explicitly
proved zero-shift helper replace obsolete rewrite order.

No machine transition, semantic definition or final theorem statement changes.
"""
from pathlib import Path
import fcntl
import os
import sys
import tempfile

target = Path(sys.argv[1])
lock = target.with_suffix(target.suffix + ".agent12-fix03.lock")
with open(lock, "a+", encoding="utf-8") as guard:
    fcntl.flock(guard.fileno(), fcntl.LOCK_EX)
    original = target.read_text(encoding="utf-8")
    out = original
    old = "  rw [h_z1, h_z2, encM_replicate_zero] at h12"
    assert out.count(old) == 2, "Expected exactly two previously failing rewrites"
    one = """  rw [ListBlank.append_pow_succ] at h12
  rw [h_z2] at h12
  rw [ListBlank.append_pow_succ, encM_replicate_zero] at h12"""
    two = """  rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ,
    encM_replicate_zero] at h12"""
    out = out.replace(old, one, 1)
    out = out.replace(old, two, 1)
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
        tempname = writer.name
    os.replace(tempname, target)
print("Agent12 proof-only rewrite repair03:", target)
print("Original bytes", len(original), "repaired bytes", len(out))
