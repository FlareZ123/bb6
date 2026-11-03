"""Second, explicitly asserted proof-only compatibility patch for pinned Cryptids halt file.

Run after Agent12's repair-halt-01.py. No changes to the machine or final
theorem statements. This attempts to resolve obsolete list and tactic lemmas.
"""
from pathlib import Path
import fcntl
import os
import sys
import tempfile

target = Path(sys.argv[1])
lock_path = target.with_suffix(target.suffix + ".agent19.lock")
with open(lock_path, "a+", encoding="utf-8") as guard:
    fcntl.flock(guard.fileno(), fcntl.LOCK_EX)
    source = target.read_text(encoding="utf-8")
    out = source

    def replace_once(before: str, after: str) -> None:
        global out
        n = out.count(before)
        if n != 1:
            raise ValueError(f"Expected exactly one occurrence, found {n}: {before[:100]!r}")
        out = out.replace(before, after, 1)

    replace_once(
        "rw [h, pow_succ_list, ih, pow_succ_list]",
        "rw [h, pow_succ_list, ih]",
    )

    helper = """
private lemma zeros_append_cons_zero (k : ℕ) (b : ListBlank (Fin 2)) :
    ((([0] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> b)) =
      ((([0] : List (Fin 2)) ^ (k + 1)) +> b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons] using
      congrArg (fun t : ListBlank (Fin 2) => (0 : Fin 2) >> t) ih

"""
    replace_once("\ndef encLeft :", "\n" + helper + "def encLeft :")
    replace_once(
        "      rw [zeros_append_cons_zero k V]\n      simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]",
        "      exact zeros_append_cons_zero k V",
    )

    assert out.split("-- END TRUSTED DEFINITIONS")[0] == source.split("-- END TRUSTED DEFINITIONS")[0]
    assert out.count("def target_tm") == source.count("def target_tm") == 1
    assert out.count("theorem is_halt") == source.count("theorem is_halt") == 1
    assert out[out.index("theorem is_halt"):].split(":=", 1)[0] == (
        source[source.index("theorem is_halt"):].split(":=", 1)[0]
    )
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=str(target.parent), delete=False
    ) as writer:
        writer.write(out)
        temp_name = writer.name
    os.replace(temp_name, target)

print("Agent19 applied asserted proof-only compatibility patch", target)
print("Input bytes", len(source), "output bytes", len(out))
