"""Minimal proof-only compatibility repair for one pinned upstream Cryptids Halt module.

Derived from independently observed Lean 4.35 compilation errors. No trusted
TM transition or final theorem statement is modified. All changes asserted.
"""
from pathlib import Path
import fcntl
import os
import sys
import tempfile

target = Path(sys.argv[1])
lock_path = target.with_suffix(target.suffix + ".agent12.lock")
old = target.read_text(encoding="utf-8")

start_marker = "omit [Inhabited Γ] in\ntheorem list_pow_add "
end_marker = "\ndef encLeft :"
start, end = old.index(start_marker), old.index(end_marker, old.index(start_marker))
replacement = """omit [Inhabited Γ] in
theorem list_pow_add (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := by
  induction n with
  | zero => simp [pow_zero_list]
  | succ n ih =>
    have h : (n + 1) + m = (n + m) + 1 := by omega
    rw [h, pow_succ_list, ih, pow_succ_list]
    simp only [List.append_assoc]
"""

marker = "-- END TRUSTED DEFINITIONS\n"
assert old.count(marker) == 1
helpers = """-- Agent 12: nonaxiomatic compatibility names for authentic Basic.lean lemmas.
private theorem stepPlus_stepStar {M : Machine Γ Λ} {c d : Cfg Γ Λ}
    (h : c [M]⊢⁺ d) : c [M]⊢* d :=
  ReachesPlus.to_star h

private theorem stepPlus_stepStar_stepPlus {M : Machine Γ Λ} {c d e : Cfg Γ Λ}
    (h : c [M]⊢⁺ d) (h' : d [M]⊢* e) : c [M]⊢⁺ e :=
  ReachesPlus.trans_star h h'

private theorem stepPlus_trans {M : Machine Γ Λ} {c d e : Cfg Γ Λ}
    (h : c [M]⊢⁺ d) (h' : d [M]⊢⁺ e) : c [M]⊢⁺ e :=
  ReachesPlus.trans h h'

private theorem stepStar_trans {M : Machine Γ Λ} {c d e : Cfg Γ Λ}
    (h : c [M]⊢* d) (h' : d [M]⊢* e) : c [M]⊢* e :=
  ReachesStar.trans h h'

private theorem step_stepStar_stepPlus {M : Machine Γ Λ} {c d e : Cfg Γ Λ}
    (h : c [M]⊢ d) (h' : d [M]⊢* e) : c [M]⊢⁺ e :=
  ReachesPlus.head h h'

"""
old_macro = "  iterate $n step\n  finish))"
assert old.count(old_macro) == 1
new_macro = "  iterate $n (all_goals step)\n  all_goals finish))"

patched = old[:start] + replacement + old[end:]
patched = patched.replace(marker, marker + helpers, 1)
patched = patched.replace(old_macro, new_macro, 1)
assert patched.count("def target_tm") == 1
assert patched.count("theorem is_halt") == 1
assert patched.split("-- END TRUSTED DEFINITIONS")[0] == old.split("-- END TRUSTED DEFINITIONS")[0]
assert patched[patched.index("theorem is_halt"):].split(":=", 1)[0] == old[old.index("theorem is_halt"):].split(":=", 1)[0]
with open(lock_path, "a+", encoding="utf-8") as guard:
    fcntl.flock(guard.fileno(), fcntl.LOCK_EX)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=str(target.parent), delete=False) as writer:
        writer.write(patched)
        temp_name = writer.name
    os.replace(temp_name, target)
print("Agent12 patched proof-only compatibility declarations:", target)
print("Original bytes", len(old), "patched bytes", len(patched))
