from pathlib import Path
import sys
p = Path(sys.argv[1])
s = p.read_text()
old = "(by rw [← h, hc.2])"
new = "(hc.2.symm.trans (congrArg decode h))"
assert s.count(old) == 3
p.write_text(s.replace(old, new))


# Source BB6Coverage unfolds blank during simp; preserve the exact run
# expression and prove the two HaltsAfter components directly.
import re
core = p.with_name("Box6Core.lean")
s = core.read_text()
def replace(pattern, replacement):
    global s
    s, count = re.subn(pattern, lambda _: replacement, s, flags=re.M)
    assert count == 1, (pattern, count)

replace(r"^    · simp \[hd\]\s*\n    · simp \[run,\s*hd,\s*rawStep,\s*hs,\s*hh\]$",
"""    · change (run m n blank).isSome = true
      rw [hd]
      rfl
    · intro a ha
      change run m n blank = some a at ha
      rw [hd] at ha
      have he : d = a := Option.some.inj ha
      subst a
      rw [hs]
      exact hh""")
replace(r"^    \| none => simp \[hr\] at ih\s*\n    \| some c =>\s*\n      obtain ⟨mv,hv⟩ := ht \(readSlot c\)\s*\n      simp \[run,\s*hr,\s*rawStep,\s*hv\]$",
"""    | none =>
      change (run m n blank).isSome = true at ih
      simp only [hr,Option.isSome_none,Bool.false_eq_true] at ih
    | some c =>
      obtain ⟨mv,hv⟩ := ht (readSlot c)
      change ((run m n blank).bind (rawStep m)).isSome = true
      rw [hr]
      simp only [Option.bind_some,rawStep,hv,Option.map_some,Option.isSome_some]""")
core.write_text(s)
