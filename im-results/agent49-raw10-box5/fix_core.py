from pathlib import Path
import sys
p=Path(sys.argv[1]);s=p.read_text()
changes=[('''    · simp [hd]
    · simp [run,hd,rawStep,hs,hh]''','''    · rw [hd]
      rfl
    · change (run m n blank).bind (rawStep m) = none
      rw [hd]
      simp only [Option.bind_some,rawStep,hs,hh,Option.map_none]'''),('''    | none => simp [hr] at ih
    | some c =>
      obtain ⟨mv,hv⟩ := ht (readSlot c)
      simp [run,hr,rawStep,hv]''','''    | none => simp only [hr,Option.isSome_none,Bool.false_eq_true] at ih
    | some c =>
      obtain ⟨mv,hv⟩ := ht (readSlot c)
      change ((run m n blank).bind (rawStep m)).isSome = true
      rw [hr]
      simp only [Option.bind_some,rawStep,hv,Option.map_some,Option.isSome_some]'''),('''      | none => simp [hr] at ih
      | some c =>
        obtain ⟨v,hv⟩ := ht (readSlot c)
        simp [run,hr,rawStep,hv]''','''      | none => simp only [hr,Option.isSome_none,Bool.false_eq_true] at ih
      | some c =>
        obtain ⟨v,hv⟩ := ht (readSlot c)
        change ((run m k blank).bind (rawStep m)).isSome = true
        rw [hr]
        simp only [Option.bind_some,rawStep,hv,Option.map_some,Option.isSome_some]''')]
for a,b in changes:
    assert s.count(a)==1,a
    s=s.replace(a,b)
p.write_text(s)
