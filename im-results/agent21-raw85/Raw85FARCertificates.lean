import FastFAR

/-
INVALID CANDIDATE SCRATCH MODULE (2026-11-24).
CI run 45503416279 compiled the dependencies and found all fourteen
Cxx.fastValid pxx assertions below to be false. Do not import or treat this
file as a certificate. It is retained only to preserve candidate DFA strings
and the failed destination-mask attempt. The current raw85 generator
recomputes masks for each destination table and the generated Lean Audit is
the acceptance boundary.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent21Raw85FAR
open BB6Coverage BB6Coverage.FAR

def p00 : PartialMachine := fromCodes [7, 4, 11, 21, 14, 2, 13, 19, 24, 4, 0, 3]
def C00 : Data 5 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩],
  masks0 := [128, 256, 8, 0, 1073741824, 1048576, 524288, 1048576, 32768, 128, 1073741824, 1225913472, 8192, 16384, 32768, 1225913472, 1073741824, 1225913472, 8192, 16384, 134217728, 1048576, 1073741824, 1048576, 128, 256, 32768, 16777216, 1073741824, 16384, 1073741824],
  masks1 := [32768, 16777216, 1, 1024, 32768, 64, 128, 128, 4096, 4194304, 128, 262144, 1225913472, 1225913472, 4096, 65536, 1225913472, 4096, 1048576, 1048576, 16777216, 65536, 1048576, 4096, 32768, 16777216, 4096, 1024, 32768, 64, 1073741824],
  zmask := 1984953682
}
theorem C00_valid : C00.fastValid p00 = true := by decide
theorem p00_never (m : Machine) (hm : compatible p00 m) : NeverHalts m :=
  C00.sound p00 (C00.fastValid_sound p00 C00_valid) m hm

def p01 : PartialMachine := fromCodes [7, 12, 11, 21, 14, 10, 13, 19, 20, 4, 24, 3]
def C01 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩],
  masks0 := [128, 256, 8, 19948696, 16777344, 16777216, 8192, 16384, 8, 19948696, 8192, 16777216, 8192, 16384, 2097152, 16384, 8192, 16777216, 2, 4, 2097152, 1048576, 16777216, 16777216, 16777216],
  masks1 := [19948696, 19948696, 4, 1024, 18874376, 64, 8192, 8192, 4, 65536, 19948696, 4096, 8192, 8192, 1048576, 65536, 16384, 4096, 2097152, 16777216, 1048576, 16, 2097160, 1, 16777216],
  zmask := 30280510
}
theorem C01_valid : C01.fastValid p01 = true := by decide
theorem p01_never (m : Machine) (hm : compatible p01 m) : NeverHalts m :=
  C01.sound p01 (C01.fastValid_sound p01 C01_valid) m hm

def p02 : PartialMachine := fromCodes [7, 12, 11, 21, 14, 10, 13, 19, 7, 4, 24, 3]
def C02 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩],
  masks0 := [128, 256, 8, 19948696, 128, 16777216, 8192, 16384, 8, 19948696, 8192, 16777216, 8192, 16384, 2097152, 16384, 8192, 16777216, 2, 4, 2097152, 1048576, 2, 16777216, 16777216],
  masks1 := [19948696, 19948696, 4, 1024, 18874376, 64, 8192, 8192, 4, 65536, 19948696, 4096, 8192, 8192, 1048576, 65536, 16384, 4096, 2097152, 16777216, 1048576, 16, 2097160, 1, 16777216],
  zmask := 30280494
}
theorem C02_valid : C02.fastValid p02 = true := by decide
theorem p02_never (m : Machine) (hm : compatible p02 m) : NeverHalts m :=
  C02.sound p02 (C02.fastValid_sound p02 C02_valid) m hm

def p03 : PartialMachine := fromCodes [7, 20, 11, 21, 14, 6, 13, 19, 24, 4, 4, 3]
def C03 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩],
  masks0 := [128, 256, 8, 17301504, 16777216, 2097160, 8192, 16384, 8, 16777216, 16777216, 16777216, 8192, 16384, 2097152, 16384, 16777216, 16384, 8192, 16384, 8, 524288, 16777216, 2097152, 16777216],
  masks1 := [17301504, 16843776, 2, 1024, 2097160, 64, 8192, 8192, 2, 65536, 16777216, 4096, 8192, 8192, 524288, 65536, 16384, 4096, 2097152, 524288, 2, 65536, 2097152, 4096, 16777216],
  zmask := 22089534
}
theorem C03_valid : C03.fastValid p03 = true := by decide
theorem p03_never (m : Machine) (hm : compatible p03 m) : NeverHalts m :=
  C03.sound p03 (C03.fastValid_sound p03 C03_valid) m hm

def p04 : PartialMachine := fromCodes [7, 20, 11, 21, 14, 10, 13, 19, 24, 4, 24, 3]
def C04 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩],
  masks0 := [128, 256, 8, 19940376, 16777216, 16777216, 8192, 16384, 8, 16793600, 16777216, 16777216, 8192, 16384, 2097152, 16384, 16777216, 16777216, 2, 4, 2097152, 1048576, 16777216, 16777216, 16777216],
  masks1 := [16777344, 16777344, 4, 1024, 18874376, 64, 8192, 8192, 4, 65536, 16793600, 4096, 8192, 8192, 1048576, 65536, 16384, 4096, 16777216, 16777216, 1048576, 16, 2097160, 1, 16777216],
  zmask := 30347070
}
theorem C04_valid : C04.fastValid p04 = true := by decide
theorem p04_never (m : Machine) (hm : compatible p04 m) : NeverHalts m :=
  C04.sound p04 (C04.fastValid_sound p04 C04_valid) m hm

def p05 : PartialMachine := fromCodes [7, 6, 11, 21, 14, 10, 13, 19, 24, 4, 20, 3]
def C05 : Data 5 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩],
  masks0 := [128, 256, 8, 0, 1073741824, 0, 128, 256, 32768, 256, 1073741824, 128, 128, 256, 2097152, 16384, 1073741824, 256, 33554432, 67108864, 2097152, 1048576, 1073741824, 3194880, 33554432, 67108864, 134217728, 1546649600, 1073741824, 1580204032, 1073741824],
  masks1 := [2, 0, 4, 1024, 32768, 64, 8192, 8192, 16384, 1024, 256, 64, 524288, 8192, 1048576, 1024, 32768, 64, 524288, 269501440, 1048576, 268435456, 134250496, 16777216, 33554432, 1580204032, 67108864, 268435456, 1546649600, 16777216, 1073741824],
  zmask := 2135753744
}
theorem C05_valid : C05.fastValid p05 = true := by decide
theorem p05_never (m : Machine) (hm : compatible p05 m) : NeverHalts m :=
  C05.sound p05 (C05.fastValid_sound p05 C05_valid) m hm

def p06 : PartialMachine := fromCodes [7, 18, 11, 21, 14, 10, 13, 19, 0, 4, 24, 3]
def C06 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩],
  masks0 := [128, 256, 8, 16777216, 16384, 16777216, 8192, 16384, 8, 16777216, 16384, 16777216, 8192, 16384, 2097152, 16384, 16384, 16777216, 128, 256, 2097152, 1048576, 16384, 16777216, 16777216],
  masks1 := [16, 16777216, 4, 1024, 2097160, 64, 16, 16, 4, 65536, 16777216, 4096, 4194304, 4194304, 1048576, 65536, 16384, 4096, 4194304, 16777216, 1048576, 1024, 2097160, 64, 16777216],
  zmask := 25824046
}
theorem C06_valid : C06.fastValid p06 = true := by decide
theorem p06_never (m : Machine) (hm : compatible p06 m) : NeverHalts m :=
  C06.sound p06 (C06.fastValid_sound p06 C06_valid) m hm

def p07 : PartialMachine := fromCodes [7, 22, 11, 21, 14, 10, 13, 19, 24, 4, 0, 3]
def C07 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩],
  masks0 := [128, 256, 8, 2098176, 16777216, 16384, 8192, 16384, 8, 2097152, 16777216, 16384, 8192, 16384, 2097152, 16384, 16777216, 16384, 128, 256, 2097152, 1048576, 16777216, 16384, 16777216],
  masks1 := [32, 1048576, 4, 1024, 2097160, 64, 32, 32, 4, 65536, 2097152, 4096, 8388608, 8388608, 1048576, 65536, 16384, 4096, 8388608, 1048576, 1048576, 1024, 2097160, 64, 16777216],
  zmask := 21562654
}
theorem C07_valid : C07.fastValid p07 = true := by decide
theorem p07_never (m : Machine) (hm : compatible p07 m) : NeverHalts m :=
  C07.sound p07 (C07.fastValid_sound p07 C07_valid) m hm

def p08 : PartialMachine := fromCodes [7, 22, 11, 21, 14, 10, 13, 19, 24, 4, 20, 3]
def C08 : Data 5 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩],
  masks0 := [128, 256, 8, 0, 1073741824, 0, 128, 256, 32768, 256, 1073741824, 128, 128, 256, 2097152, 16384, 1073741824, 256, 33554432, 67108864, 2097152, 1048576, 1073741824, 3194880, 33554432, 67108864, 134217728, 2133852160, 1073741824, 2133852160, 1073741824],
  masks1 := [32, 0, 4, 1024, 32768, 64, 131072, 131072, 16384, 1024, 256, 64, 8388608, 131072, 1048576, 1024, 32768, 64, 8388608, 269501440, 1048576, 268435456, 134250496, 16777216, 536870912, 2133852160, 67108864, 268435456, 2133852160, 16777216, 1073741824],
  zmask := 2135753744
}
theorem C08_valid : C08.fastValid p08 = true := by decide
theorem p08_never (m : Machine) (hm : compatible p08 m) : NeverHalts m :=
  C08.sound p08 (C08.fastValid_sound p08 C08_valid) m hm

def p09 : PartialMachine := fromCodes [7, 17, 11, 21, 14, 20, 13, 19, 11, 4, 24, 3]
def C09 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩],
  masks0 := [128, 256, 8, 16778368, 256, 16777216, 8192, 16384, 8, 16777216, 16384, 16777216, 128, 256, 2097152, 16384, 256, 16777216, 128, 256, 8, 128, 256, 16777216, 16777216],
  masks1 := [8320, 16777216, 16777216, 1024, 2097160, 64, 1152, 1152, 8192, 65536, 16777216, 4096, 16777216, 16777216, 128, 1024, 16384, 64, 8192, 16777216, 16777216, 1024, 8, 64, 16777216],
  zmask := 31140734
}
theorem C09_valid : C09.fastValid p09 = true := by decide
theorem p09_never (m : Machine) (hm : compatible p09 m) : NeverHalts m :=
  C09.sound p09 (C09.fastValid_sound p09 C09_valid) m hm

def p10 : PartialMachine := fromCodes [7, 17, 11, 21, 14, 10, 13, 19, 11, 4, 24, 3]
def C10 : Data 5 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩],
  masks0 := [128, 256, 8, 1076888584, 256, 1073741824, 8192, 16384, 8, 1075838984, 16384, 1073741824, 33554432, 67108864, 2097152, 16384, 67108864, 1073741824, 128, 256, 2097152, 1048576, 256, 1073741824, 2, 4, 8, 1073758208, 4, 1073741824, 1073741824],
  masks1 := [1074790404, 1074790404, 4, 1024, 2097160, 64, 1024, 1024, 4, 65536, 1075838984, 4096, 1073742848, 1073742848, 1048576, 268435456, 16384, 16777216, 4, 1073741824, 1048576, 1024, 8, 64, 1048576, 1048576, 4, 16, 1073758208, 1, 1073741824],
  zmask := 2144025470
}
theorem C10_valid : C10.fastValid p10 = true := by decide
theorem p10_never (m : Machine) (hm : compatible p10 m) : NeverHalts m :=
  C10.sound p10 (C10.fastValid_sound p10 C10_valid) m hm

def p11 : PartialMachine := fromCodes [7, 7, 11, 21, 14, 10, 13, 19, 24, 4, 24, 3]
def C11 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩],
  masks0 := [128, 256, 8, 19940376, 16777216, 16777216, 8192, 16384, 8, 16793600, 16777216, 16777216, 8192, 16384, 2097152, 16384, 16777216, 16777216, 2, 4, 2097152, 1048576, 16777216, 16777216, 16777216],
  masks1 := [128, 16777344, 4, 1024, 18874376, 64, 8192, 8192, 4, 65536, 16793600, 4096, 8192, 8192, 1048576, 65536, 16384, 4096, 2, 16777216, 1048576, 16, 2097160, 1, 16777216],
  zmask := 30347070
}
theorem C11_valid : C11.fastValid p11 = true := by decide
theorem p11_never (m : Machine) (hm : compatible p11 m) : NeverHalts m :=
  C11.sound p11 (C11.fastValid_sound p11 C11_valid) m hm

def p12 : PartialMachine := fromCodes [7, 19, 11, 21, 14, 10, 13, 19, 11, 4, 24, 3]
def C12 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩],
  masks0 := [128, 256, 8, 19940376, 256, 16777216, 8192, 16384, 8, 16793600, 16384, 16777216, 8192, 16384, 2097152, 16384, 16384, 16777216, 2, 4, 2097152, 1048576, 4, 16777216, 16777216],
  masks1 := [1024, 16778240, 4, 1024, 18874376, 64, 65536, 65536, 4, 65536, 16793600, 4096, 65536, 65536, 1048576, 65536, 16384, 4096, 16, 16777216, 1048576, 16, 2097160, 1, 16777216],
  zmask := 30280510
}
theorem C12_valid : C12.fastValid p12 = true := by decide
theorem p12_never (m : Machine) (hm : compatible p12 m) : NeverHalts m :=
  C12.sound p12 (C12.fastValid_sound p12 C12_valid) m hm

def p13 : PartialMachine := fromCodes [7, 23, 11, 21, 14, 10, 13, 19, 24, 4, 11, 3]
def C13 : Data 4 := {
  start := ⟨0, by decide⟩,
  dfa := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩],
  masks0 := [128, 256, 8, 3163160, 16777216, 256, 8192, 16384, 8, 2113544, 16777216, 16384, 8192, 16384, 2097152, 16384, 16777216, 16384, 2, 4, 2097152, 1048576, 16777216, 4, 16777216],
  masks1 := [2048, 1050628, 4, 1024, 2097160, 64, 131072, 131072, 4, 65536, 2113544, 4096, 131072, 131072, 1048576, 65536, 16384, 4096, 32, 1048580, 1048576, 16, 2097160, 1, 16777216],
  zmask := 30213950
}
theorem C13_valid : C13.fastValid p13 = true := by decide
theorem p13_never (m : Machine) (hm : compatible p13 m) : NeverHalts m :=
  C13.sound p13 (C13.fastValid_sound p13 C13_valid) m hm

end BB6.Agent21Raw85FAR
#print axioms BB6.Agent21Raw85FAR.p00_never