from pathlib import Path
import os
out=Path(os.environ.get('A3_BUILD','generated'));p=[7,24,11,24,14,24,24,16,1,11,24,24];order=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
s=''.join(f'import A3E0RAB{b:02}Cover\n' for b in range(24))+'''import Agent3PackedFast
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent3E0RA
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent3PackedFast
'''
s+=f'def parent : PartialMachine := fromCodes {p}\ndef rootAudit : PAudit 321796 := .split 9 (1,true) (pbyMove [\n'
s+=',\n'.join(f'.bound B{b:02}.parent B{b:02}.cover.sound' for b in order)+'''])
theorem checked : pcheck 321796 parent rootAudit = true := by decide +kernel
theorem cover : Cover (WeightedBound 321796) parent := pcheck_sound 321796 parent rootAudit (by decide) checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 321796 m := cover.sound
#print axioms cover
#print axioms all_completions_weighted
end BB6.Agent3E0RA
'''
(out/'A3E0RACover.lean').write_text(s)
