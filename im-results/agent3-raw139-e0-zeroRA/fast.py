from pathlib import Path
import hashlib
p=Path('Agent3PackedAudit.lean')
s=p.read_text().replace('namespace BB6.Agent3PackedAudit','namespace BB6.Agent3PackedFast').replace('end BB6.Agent3PackedAudit','end BB6.Agent3PackedFast')
s=s.replace('def pqueryOK (B : Nat)', '''theorem margin_weightOK (B : Nat) (p : PartialMachine) (s : Slot) (n : Nat)
    (h : n+6 ≤ B) : weightOK p s n B = true := by
  unfold weightOK
  apply List.all_eq_true.mpr
  intro d hd
  have hlt : d < 6 := List.mem_range.mp (List.mem_filter.mp hd).1
  exact decide_eq_true (by omega)

def quickWeight (B : Nat) (p : PartialMachine) (s : Slot) (n : Nat) : Bool :=
  if n+6 ≤ B then true else weightOK p s n B

theorem quickWeight_sound {B p s n} (h : quickWeight B p s n = true) : weightOK p s n = true := by
  by_cases hb : n+6 ≤ B
  · exact margin_weightOK B p s n hb
  · simpa [quickWeight,hb] using h

def pqueryOK (B : Nat)''').replace('(decide (p s = none) && weightOK p s n)','(decide (p s = none) && quickWeight B p s n)').replace('exact ⟨by rw [packed_read hr,hs]; simp,h.2⟩','exact ⟨by rw [packed_read hr,hs]; simp,h.2.1,quickWeight_sound h.2.2⟩')
assert hashlib.sha256(s.encode()).hexdigest()=='28eaa75ca0e3c9c6d8bc7fc69c88c2c04fff24261c52cd4e33b33590583e0915'
Path('Agent3PackedFast.lean').write_text(s)
p=Path('emit_family.py')
p.write_text(p.read_text().replace('Agent3PackedAudit','Agent3PackedFast'))
