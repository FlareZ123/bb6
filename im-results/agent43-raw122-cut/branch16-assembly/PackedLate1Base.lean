import PackedAction122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def m0 : Motif := ⟨4,6,true,[false,true,false],[],[true,false],[true,true]⟩
theorem v0 : m0.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m1 : Motif := ⟨4,2,false,[true],[],[true,true],[true,false]⟩
theorem v1 : m1.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m2 : Motif := ⟨4,6,false,[true],[],[true,true,true,true,true,true],[true,false,true,false,true,false]⟩
theorem v2 : m2.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m3 : Motif := ⟨4,24,true,[false,true,false],[],[true,false,true,false,true,false,true,false],[true,true,true,true,true,true,true,true]⟩
theorem v3 : m3.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m4 : Motif := ⟨4,12,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v4 : m4.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m5 : Motif := ⟨4,12,true,[false,true,false],[],[true,false,true,false],[true,true,true,true]⟩
theorem v5 : m5.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m6 : Motif := ⟨4,10,false,[true],[],[true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false]⟩
theorem v6 : m6.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m7 : Motif := ⟨4,18,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v7 : m7.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m8 : Motif := ⟨4,30,true,[false,true,false],[],[true,false,true,false,true,false,true,false,true,false],[true,true,true,true,true,true,true,true,true,true]⟩
theorem v8 : m8.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m9 : Motif := ⟨4,22,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v9 : m9.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m10 : Motif := ⟨1,24,true,[false],[],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩
theorem v10 : m10.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m11 : Motif := ⟨4,14,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v11 : m11.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m12 : Motif := ⟨4,24,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v12 : m12.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m13 : Motif := ⟨4,30,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v13 : m13.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m14 : Motif := ⟨4,26,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v14 : m14.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m15 : Motif := ⟨4,28,false,[true],[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v15 : m15.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m16 : Motif := ⟨4,4,false,[true],[],[true,true,true,true],[true,false,true,false]⟩
theorem v16 : m16.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m17 : Motif := ⟨1,30,true,[false],[],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩
theorem v17 : m17.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m18 : Motif := ⟨1,26,true,[false],[],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩
theorem v18 : m18.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m19 : Motif := ⟨1,28,true,[false],[],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩
theorem v19 : m19.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
end BB6Coverage.Agent29PackedLate.M1
