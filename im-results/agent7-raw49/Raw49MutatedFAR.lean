import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49MutatedFAR
open BB6Coverage BB6Coverage.FAR
namespace M110
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none
def cert : Data 6 := ⟨0,[0, 1, 2, 3, 5, 4, 1, 4, 4, 4, 4, 1],[64, 17179869184, 2097152, 512, 16, 65536, 64, 69004755024, 86318841920, 2097152, 65536, 69004689472, 69004755008, 86184624192, 134217728, 134217728, 17179869184, 65536, 69004754944, 17179869184, 86184624208, 134217728, 1024, 16777216, 69004755008, 86184624192, 86320939072, 134217728, 268435456, 69005017152, 69004755008, 86184624192, 134217728, 512, 268435456, 69004754944, 68719476736],[16, 17179869184, 1, 17179869184, 64, 68719476736, 65536, 69004755008, 4096, 69004755024, 262144, 68719476736, 17179869184, 69004755008, 1073741824, 86184624192, 16777216, 68719476736, 1024, 68719476736, 64, 17179869184, 16777216, 68719476736, 268435456, 86184624192, 16777216, 86184624192, 16777216, 68719476736, 268435456, 17179869184, 16777216, 86184624192, 64, 68719476736, 68719476736],106964466048⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M110
namespace M111
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none
def cert : Data 6 := ⟨0,[0, 1, 2, 3, 5, 4, 1, 4, 4, 4, 4, 1],[64, 17179869184, 2097152, 512, 69004755024, 65536, 64, 69004755024, 86318841936, 2097152, 86184624192, 69004689472, 69004755008, 86184624192, 134217728, 134217728, 17179869184, 65536, 69004754944, 17179869184, 86184624208, 134217728, 69004755008, 16777216, 69004755008, 86184624192, 86320939088, 134217728, 86184624208, 69005017152, 69004755008, 86184624192, 134217728, 512, 86184624192, 69004754944, 68719476736],[16, 17179869184, 1, 17179869184, 64, 68719476736, 65536, 69004755008, 4096, 69004755024, 262144, 68719476736, 17179869184, 86184624208, 1073741824, 86184624192, 16777216, 68719476736, 1024, 68719476736, 64, 17179869184, 16777216, 68719476736, 268435456, 86184624208, 16777216, 86184624192, 16777216, 68719476736, 268435456, 17179869184, 16777216, 86184624192, 64, 68719476736, 68719476736],124417686962⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M111
namespace M114
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
def cert : Data 6 := ⟨0,[0, 1, 2, 5, 1, 4, 0, 1, 4, 4, 3, 1],[17179869184, 1024, 8589934592, 512, 32, 1, 86167782400, 16, 134348800, 8589934592, 131072, 4096, 1024, 86167847936, 512, 134217728, 2048, 64, 17179869184, 1024, 8589934592, 512, 32, 1, 86167782400, 86167847936, 69399087104, 134217728, 536870912, 16777216, 68719476736, 1024, 32, 512, 8388608, 262144, 68719476736],[16, 68719476736, 1, 1024, 1024, 1024, 65536, 68719476736, 4096, 16, 17179869184, 17179870208, 1024, 68719476736, 64, 86167847936, 268435456, 86167782400, 16, 68719476736, 1, 1024, 1024, 68719476736, 268435456, 68719476736, 16777216, 86167847936, 268435456, 86167782400, 4194304, 68719476736, 262144, 1024, 1024, 268435456, 68719476736],72864185666⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M114
namespace M115
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 2, 3, 4, 1, 4, 5, 4, 5, 5, 5, 5, 3],[128, 256, 8, 0, 1, 32768, 524288, 1048576, 32768, 1048576, 4096, 32768, 128, 256, 134217728, 0, 16777216, 134217728, 2147483648, 4294967296, 134217728, 0, 16777216, 4398046511104, 2147483648, 4294967296, 134217728, 0, 16777216, 8589967360, 2147483648, 4294967296, 8589934592, 4402341478400, 1073741824, 4406770696192, 524288, 1048576, 8589934592, 0, 1073741824, 0, 4398046511104],[128, 256, 1048576, 256, 256, 4398046511104, 32768, 4398046511104, 1048576, 1048576, 4398046511104, 4398046511104, 128, 256, 4294967296, 256, 256, 4398046511104, 4398046511104, 4398046511104, 0, 4294967296, 4398046511104, 4398046511104, 2147483648, 4402341478656, 4296015872, 4294967296, 4402341478656, 4398046511104, 4408783962112, 4402341478656, 4402341478400, 4294967296, 4402341478656, 4398046511104, 0, 0, 0, 1048576, 0, 4398046511104, 4398046511104],5909670330432⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M115
namespace M117
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 5, 2, 3, 1, 4, 0, 1, 4, 4, 2, 3, 4, 4],[8388608, 34359739392, 2097152, 8589934592, 8388608, 2147483648, 4433254089872, 16, 4433388307600, 2097152, 4433254089872, 524288, 34359738368, 4433254089872, 512, 134217728, 34359738368, 33554432, 4398046511104, 1024, 8388608, 512, 4398046511104, 128, 4433254089872, 4433254089872, 4433388307600, 134217728, 4433254089872, 33554432, 4398046511104, 16, 4433254089872, 2097152, 4398046511104, 524288, 0, 0, 0, 134217728, 0, 33554432, 4398046511104],[16, 4398046511104, 1, 34359739392, 34359738368, 4398046511232, 65536, 4398046511104, 4096, 16, 8388608, 8912896, 1024, 4398046511104, 64, 4433254089872, 536870912, 4433254089872, 16, 4398046511104, 1, 1024, 2048, 34359738368, 268435456, 4398046511104, 16777216, 4433254089872, 536870912, 4433254089872, 65536, 4398046511104, 4096, 16, 8388608, 8388608, 268435456, 4398046511104, 16777216, 0, 536870912, 0, 4398046511104],6654906023234⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M117
namespace M119
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 2, 3, 1, 6, 0, 1, 4, 4, 5, 4, 4, 5],[8388608, 2199023256576, 2097152, 512, 8388608, 128, 6597615028224, 16, 6608352446464, 2097152, 6597615028224, 524288, 2048, 6615063332864, 512, 549755813888, 2048, 137438953472, 4398046511104, 1024, 8388608, 512, 4398046511104, 128, 6597615028224, 6615063332864, 6599930808448, 134217728, 6597615028224, 33554432, 6597615028224, 6615063332864, 134219776, 134217728, 6597615028224, 33554432, 4398046511104, 65536, 6599796590720, 8589934592, 4398046511104, 2147483648, 4398046511104],[16, 4398046511104, 1, 2199023256576, 2048, 6597069766656, 65536, 4398046511104, 4096, 16, 8388608, 2048, 1024, 4398046511104, 64, 6615063332864, 2199023255552, 6597615028224, 16, 4398046511104, 1, 1024, 2048, 2199023255552, 268435456, 4398046511104, 16777216, 6615063332864, 536870912, 6597615028224, 17179869184, 4398046511104, 1073741824, 6615063332864, 536870912, 6597615028224, 268435456, 4398046511104, 16777216, 65536, 34359738368, 8388608, 4398046511104],8237601471810⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M119
namespace M120
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 5, 2, 3, 1, 4, 0, 1, 4, 4, 2, 3, 4, 4],[8388608, 34359739392, 2097152, 8589934592, 8388608, 2147483648, 4433220009984, 16, 4433354227712, 2097152, 4433220009984, 524288, 34359738368, 4433220009984, 512, 134217728, 34359738368, 33554432, 4398046511104, 1024, 8388608, 512, 4398046511104, 128, 4433220009984, 4433220009984, 4433388306560, 134217728, 4433220009984, 33554432, 4398046511104, 16, 4433220534272, 2097152, 4398046511104, 524288, 0, 0, 0, 134217728, 0, 33554432, 4398046511104],[16, 4398046511104, 1, 34359739392, 34359738368, 16, 65536, 4398046511104, 4096, 16, 8388608, 4433220009984, 1024, 4398046511104, 64, 4433220009984, 536870912, 1024, 16, 4398046511104, 1, 1024, 2048, 34359738368, 268435456, 4398046511104, 16777216, 4433220009984, 536870912, 4433220009984, 65536, 4398046511104, 4096, 16, 8388608, 8388608, 268435456, 4398046511104, 16777216, 0, 536870912, 0, 4398046511104],6654906023234⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M120
namespace M121
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none
def cert : Data 8 := ⟨0,[0, 1, 7, 3, 0, 1, 4, 5, 5, 5, 5, 5, 2, 6, 4, 1],[128, 256, 8, 0, 140737488355328, 128, 524288, 1048576, 35184372088832, 1048576, 140737488355328, 524288, 128, 256, 8, 0, 131072, 128, 2147483648, 4294967296, 134217728, 128, 281474976710656, 2147483648, 2147483648, 4294967296, 8589934592, 140737488355328, 140771848093696, 2147483648, 2147483648, 4294967296, 8589934592, 422253268304000, 422246824804352, 2147483648, 137438953472, 274877906944, 32768, 0, 0, 137438953472, 128, 256, 134217728, 128, 536870912, 128, 281474976710656],[128, 32, 1048576, 256, 1024, 281474976710656, 140737488355328, 140737488355328, 1048576, 1048576, 4194304, 281474976710656, 0, 32, 274877906944, 256, 1024, 281474976710656, 281474976710656, 536870912, 128, 4294967296, 17179869184, 281474976710656, 281477124194304, 34359738368, 4296015872, 4294967296, 17179869184, 281474976710656, 422248972288128, 34359738368, 281481420210304, 4294967296, 17179869184, 281474976710656, 0, 131072, 0, 274877906944, 1099511627776, 281474976710656, 128, 536870912, 4294967296, 256, 1024, 281474976710656, 281474976710656],351912302741568⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M121
namespace M123
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 2, 3, 4, 1, 4, 5, 4, 5, 5, 5, 5, 3],[128, 256, 8, 0, 1, 32768, 524288, 1048576, 32768, 1048576, 4096, 32768, 128, 256, 134217728, 0, 16777216, 134217728, 2147483648, 4294967296, 134217728, 0, 16777216, 4398046511104, 2147483648, 4294967296, 134217728, 0, 16777216, 8589967360, 2147483648, 4294967296, 8589934592, 4402341478400, 1073741824, 4406770696192, 524288, 1048576, 8589934592, 0, 1073741824, 0, 4398046511104],[128, 256, 1048576, 256, 2048, 4398046511104, 32768, 4398046511104, 1048576, 1048576, 8388608, 4398046511104, 128, 256, 4294967296, 256, 2048, 4398046511104, 4398046511104, 4398046511104, 0, 4294967296, 34359738368, 4398046511104, 2147483648, 4402341478656, 4296015872, 4294967296, 34359738368, 4398046511104, 4408918179840, 4402341478656, 4402341478400, 4294967296, 34359738368, 4398046511104, 0, 0, 0, 1048576, 8388608, 4398046511104, 4398046511104],5909670330432⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M123
namespace M124
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
def cert : Data 6 := ⟨0,[0, 1, 0, 2, 3, 2, 0, 4, 5, 2, 0, 4],[128, 256, 8, 77376520192, 68719476736, 2048, 8192, 16384, 8, 68719476736, 68719476736, 131072, 8192, 16384, 2097152, 131072, 524288, 131072, 33554432, 67108864, 8, 524288, 68719476736, 536870912, 8192, 16384, 8589934592, 8589934592, 8589934592, 131072, 33554432, 67108864, 8, 67108864, 68719476736, 536870912, 68719476736],[68719476736, 68719476736, 16384, 256, 2048, 2, 131072, 68719476736, 68719476736, 16384, 131072, 2, 131072, 68719476736, 131072, 16384, 131072, 524288, 67108864, 68719476736, 16384, 67108864, 536870912, 2, 131072, 68719476736, 8589934592, 16384, 131072, 2147483648, 67108864, 68719476736, 16384, 67108864, 536870912, 2, 68719476736],90199557918⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M124
namespace M601
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 5, 2, 3, 4, 0, 1, 3, 0, 0, 6, 5, 2],[128, 256, 8, 4682118356992, 2, 128, 8192, 16384, 8589934592, 8192, 2147483648, 8192, 33554432, 67108864, 2097152, 67108864, 524288, 33554432, 128, 256, 8, 283467841536, 2, 128, 2, 4, 2097152, 8589934592, 524288, 2, 137438953472, 274877906944, 8, 536870912, 2, 137438953472, 8192, 16384, 8589934592, 8192, 2147483648, 8192, 4398046511104],[2048, 2048, 4398046527488, 256, 256, 4398046511104, 8192, 131072, 8192, 16384, 8589934592, 4398046511104, 274877906944, 536870912, 67108864, 67108864, 536870912, 4398046511104, 2048, 2048, 260, 256, 256, 4398046511104, 4398046511104, 32, 8589934592, 4, 2, 4398046511104, 2199023255552, 2199023255552, 67108864, 274877906944, 274877906944, 4398046511104, 8192, 131072, 8192, 16384, 8589934592, 4398046511104, 4398046511104],4402376216588⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M601
namespace M602
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
def cert : Data 8 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 2, 5, 6, 5, 5, 1, 7, 5, 2],[128, 256, 8, 0, 32768, 1048576, 524288, 1048576, 32768, 281474976759808, 281483566694400, 49152, 8192, 16384, 32768, 299355060879872, 299355060879872, 299355060879872, 8192, 16384, 134217728, 512, 281474976710656, 512, 137438953472, 274877906944, 8589934592, 1048576, 32768, 16384, 2147483648, 4294967296, 8589934592, 299355060879872, 299355060879872, 299355060879872, 8796093022208, 17592186044416, 512, 281474976710656, 134217728, 281474976710656, 8192, 16384, 8589934592, 299355060879872, 281474976710656, 299355060879872, 281474976710656],[16384, 512, 1048576, 256, 134217728, 281474976710656, 274877906944, 281474976710656, 49152, 1048576, 281474976710656, 281474976710656, 299355060879872, 299355060879872, 299355060879872, 16384, 299355060879872, 281474976710656, 281474976710656, 281474976710656, 512, 16384, 281474976710656, 281474976710656, 281474976710656, 1048576, 16384, 274877906944, 281474976759808, 281474976710656, 299355060879872, 299355060879872, 299355060879872, 4294967296, 299355060879872, 281474976710656, 299355060879872, 281474976710656, 281474976710656, 17592186044416, 281474976710656, 281474976710656, 281474976710656, 281474976710656, 299355060879872, 16384, 281474976710656, 281474976710656, 281474976710656],561850306527058⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M602
namespace M605
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 2, 3, 6, 4, 0, 1, 2, 3, 0, 6, 2, 5],[131072, 1099780063232, 8592031744, 512, 1024, 2, 4398046511104, 1024, 4415226511376, 2097152, 131072, 8192, 131104, 5497826574368, 549755814400, 134217728, 268435456, 137438953472, 4398046511104, 268435456, 131072, 512, 131104, 2, 4398046511104, 17179869184, 4415226511378, 2097152, 4398046642192, 8192, 4398046511104, 268435456, 131072, 549755813888, 131072, 2, 4398046642192, 1024, 4398048739344, 8589934592, 17180000256, 8192, 4398046511104],[1024, 4398046511104, 1, 1099780063232, 32, 16, 4194304, 4398046511104, 4096, 1024, 131072, 65536, 268435456, 4398046511104, 68719476736, 5497826574368, 2199023255552, 1099511627776, 1024, 4398046511104, 1, 268435456, 32, 16, 4194304, 4398046511104, 4096, 17179869184, 131072, 65536, 1099511627776, 4398046511104, 1, 268435456, 32, 16, 17179869184, 4398046511104, 4096, 1024, 131072, 65536, 4398046511104],6979150756194⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M605
namespace M606
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 2, 3, 6, 4, 0, 1, 2, 3, 0, 6, 2, 5],[131072, 2199291691008, 8592031744, 512, 1024, 2, 4398046511104, 1024, 4398046650368, 2097152, 131072, 8192, 131104, 6597338202112, 549755814400, 134217728, 268435456, 137438953472, 4398046511104, 268435456, 131072, 512, 131104, 2, 4398046511104, 17179869184, 4398046650368, 2097152, 4398046642176, 8192, 4398046511104, 268435456, 131072, 549755813888, 131072, 2, 4398046642176, 1024, 4398048739328, 8589934592, 17180000256, 8192, 4398046511104],[1024, 4398046511104, 1, 2199291691008, 32, 32, 4194304, 4398046511104, 4096, 1024, 131072, 131072, 268435456, 4398046511104, 68719476736, 6597338202112, 2199023255552, 2199023255552, 1024, 4398046511104, 1, 268435456, 32, 32, 4194304, 4398046511104, 4096, 17179869184, 131072, 131072, 1099511627776, 4398046511104, 1, 268435456, 32, 32, 17179869184, 4398046511104, 4096, 1024, 131072, 131072, 4398046511104],6979150756194⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M606
namespace M611
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 5, 4, 3, 3, 3, 3, 3, 3, 6, 6, 5, 4],[33554432, 1099511627776, 134217728, 512, 33554432, 1024, 4398046511104, 1024, 33554432, 134217728, 33554432, 33554432, 0, 0, 0, 2097152, 0, 0, 4398080589824, 4398050705408, 4398082686976, 2097152, 4398080589824, 4398084784128, 4398046511104, 1099511627776, 4398080589824, 2097152, 4398080589824, 4398080589824, 4398080589824, 5497558138880, 2097152, 549755813888, 4398047035392, 1099511627776, 4398080065536, 4398319140864, 4398214283264, 134217728, 33554432, 4398352695296, 4398046511104],[1024, 4398046511104, 1, 1099511627776, 128, 1099511627776, 268435456, 4398046511104, 1073741824, 1024, 33554432, 1024, 4194304, 4398046511104, 262144, 0, 524288, 0, 4194304, 4398046511104, 262144, 4398050705408, 524288, 5497562333184, 4194304, 4398046511104, 262144, 1099511627776, 524288, 1099511627776, 1099511627776, 4398046511104, 68719476736, 5497558138880, 137438953472, 1099511627776, 268435456, 4398046511104, 1073741824, 4398319140864, 33554432, 4398319140864, 4398046511104],7099410808896⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M611
namespace M612
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 0, 2, 3, 6, 4, 4, 4, 4, 5, 5, 3, 4],[128, 256, 8, 1120, 32, 64, 8192, 16384, 8, 32, 32, 4096, 137438953472, 274877906944, 2097152, 64, 8388608, 68719476736, 33554432, 67108864, 134217728, 32, 536870912, 16777216, 33554432, 67108864, 134217728, 4673983489120, 536870912, 16777216, 2147483648, 4294967296, 8589934592, 4465692246016, 34359738368, 1073741824, 33554432, 67108864, 2097152, 64, 8388608, 16777216, 4398046511104],[1024, 4398046511104, 274877923328, 256, 256, 1024, 32, 4398046511104, 32, 16384, 64, 65536, 32, 4398046511104, 64, 274877906944, 1024, 1099511627776, 268435456, 4398046511104, 67108864, 67108864, 67108864, 268435456, 4673983489120, 4398046511104, 4673983489120, 67108864, 4673983489120, 268435456, 4465692246016, 4398046511104, 4465692246016, 4294967296, 4465692246016, 17179869184, 64, 4398046511104, 64, 67108864, 32, 268435456, 4398046511104],7971457144832⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M612
namespace M614
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
def cert : Data 8 := ⟨0,[0, 1, 0, 2, 6, 4, 3, 4, 4, 4, 3, 3, 7, 3, 4, 1],[128, 256, 8, 264, 32, 2, 8192, 16384, 8, 264, 32, 2, 33554432, 67108864, 549755813888, 2199023255552, 2199023255552, 137438953472, 33554432, 67108864, 2097152, 293020623716616, 8388608, 524288, 33554432, 67108864, 134217728, 293020623716616, 536870912, 33554432, 524288, 1048576, 2097152, 0, 8388608, 524288, 524288, 1048576, 35184372088832, 8796093022208, 140737488355328, 8796093022208, 128, 256, 134217728, 281474976710656, 536870912, 33554432, 281474976710656],[264, 281474976710656, 67125248, 256, 1024, 264, 65536, 281474976710656, 264, 16384, 65536, 8, 268435456, 281474976710656, 2199023255552, 67108864, 268435456, 549755813888, 293020892152072, 281474976710656, 67109120, 67108864, 268435456, 293020623716616, 293020892152072, 281474976710656, 293020623716616, 67108864, 268435456, 293020623716616, 0, 281474976710656, 0, 1048576, 4194304, 0, 8796093022208, 281474976710656, 67108864, 1048576, 4194304, 8796093022208, 256, 281474976710656, 67108864, 256, 1024, 256, 281474976710656],546998444765248⟩
theorem checked : cert.fastValid (table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact cert.sound table (cert.fastValid_sound _ checked) m hm
#print axioms never
end M614
namespace M615
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def cert : Data 7 := ⟨0,[0, 1, 2, 3, 1, 6, 0, 1, 4, 4, 5, 4, 4, 5],[131072, 1099511629824, 2097152, 512, 640, 2, 4432943253536, 1024, 4441533196320, 2097152, 2228224, 8192, 4398046511136, 5532723317792, 512, 549755813888, 5535038581922, 128, 4398046511104, 1099511627776, 2228224, 512, 4398046511136, 2, 4432943253536, 5532723317792, 5535040679586, 134217728, 5535040679586, 33554432, 4432943253536, 5532723317792, 4398180728864, 134217728, 4433077471266, 2147483648, 4398046511104, 4194304, 5535040679586, 8589934592, 4432943253536, 33554432, 4398046511104],[1024, 4398046511104, 1, 1099511629824, 4398046511104, 32, 4194304, 4398046511104, 4096, 1024, 4398046511136, 131072, 1099511627776, 4398046511104, 64, 5532723317792, 4398046511104, 2048, 1024, 4398046511104, 1, 1099511627776, 2048, 32, 268435456, 4398046511104, 16777216, 5532723317792, 4432943120384, 536870912, 268435456, 4398046511104, 1073741824, 5532723317792, 4398583382016, 34359738368, 17179869184, 4398046511104, 16777216, 4194304, 131072, 536870912, 4398046511104],8237609728354⟩
theorem checked : cert.fastValid (reflectPartial table) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end M615
end BB6.Agent7Raw49MutatedFAR
