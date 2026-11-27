import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50.Raw47FAR609
open BB6Coverage BB6Coverage.FAR
-- Exact residual leaf of Raw47 depth-three parent 609.
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def certificate : Data 6 := ⟨0,[0, 1, 0, 2, 3, 2, 4, 5, 0, 1, 1, 2],[4194304, 4096, 32768, 512, 2048, 4096, 4194320, 4096, 32768, 32768, 131072, 4096, 4194304, 4096, 4194304, 32768, 131072, 4194304, 4194304, 68719476736, 32768, 8589934592, 34359738368, 4096, 68719476736, 4096, 32768, 512, 2048, 4096, 1024, 4096, 128, 32768, 131072, 128, 68719476736],[16, 64, 128, 32768, 68719476736, 2, 16, 4096, 8192, 4096, 68719476736, 2, 4194304, 4096, 8192, 4096, 68719476736, 524288, 268435456, 1073741824, 2147483648, 34359738368, 68719476736, 33554432, 16, 64, 128, 32768, 68719476736, 2, 1024, 4096, 8192, 4096, 68719476736, 128, 68719476736],68736778240⟩
theorem checked : certificate.fastValid (reflectPartial p) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  reflectNever m (certificate.sound (reflectPartial p) (certificate.fastValid_sound _ checked)
    (reflectTable m) (reflectCompatible p m hm))
#print axioms never
end BB6.Agent50.Raw47FAR609
