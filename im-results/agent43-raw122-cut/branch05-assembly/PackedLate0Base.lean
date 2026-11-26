import PackedAction122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedLate.M0
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def m0 : Motif := ⟨2,4,true,[false],[],[true,false,false,false],[true,false,true,false]⟩
theorem v0 : m0.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m1 : Motif := ⟨5,2,false,[false],[],[true,false],[false,true]⟩
theorem v1 : m1.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m2 : Motif := ⟨1,2,true,[true],[],[false,true],[true,false]⟩
theorem v2 : m2.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m3 : Motif := ⟨5,4,false,[false],[],[true,false,true,false],[false,true,false,true]⟩
theorem v3 : m3.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m4 : Motif := ⟨2,5,false,[true],[],[true,false,true,false,true],[true,false,true,false,false]⟩
theorem v4 : m4.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m5 : Motif := ⟨1,4,true,[true],[],[false,true,false,true],[true,false,true,false]⟩
theorem v5 : m5.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m6 : Motif := ⟨5,6,false,[false],[],[true,false,true,false,true,false],[false,true,false,true,false,true]⟩
theorem v6 : m6.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m7 : Motif := ⟨2,2,false,[true],[],[false,true],[true,false]⟩
theorem v7 : m7.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m8 : Motif := ⟨1,6,true,[true],[],[false,true,false,true,false,true],[true,false,true,false,true,false]⟩
theorem v8 : m8.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m9 : Motif := ⟨5,8,false,[false],[],[true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true]⟩
theorem v9 : m9.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m10 : Motif := ⟨1,10,true,[true],[],[false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false]⟩
theorem v10 : m10.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m11 : Motif := ⟨5,10,false,[false],[],[true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true]⟩
theorem v11 : m11.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m12 : Motif := ⟨1,8,true,[true],[],[false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false]⟩
theorem v12 : m12.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m13 : Motif := ⟨1,4,true,[false],[],[false,true,false,false],[false,true,false,true]⟩
theorem v13 : m13.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m14 : Motif := ⟨1,12,true,[true],[],[false,true,false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v14 : m14.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m15 : Motif := ⟨5,12,false,[false],[],[true,false,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true,false,true]⟩
theorem v15 : m15.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m16 : Motif := ⟨2,4,false,[true],[],[false,true,false,true],[true,false,true,false]⟩
theorem v16 : m16.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m17 : Motif := ⟨5,14,false,[false],[],[true,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩
theorem v17 : m17.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m18 : Motif := ⟨1,14,true,[true],[],[false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v18 : m18.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m19 : Motif := ⟨2,12,false,[true],[],[false,true,false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v19 : m19.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m20 : Motif := ⟨2,8,false,[true],[],[false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false]⟩
theorem v20 : m20.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m21 : Motif := ⟨2,14,false,[true],[],[false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v21 : m21.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m22 : Motif := ⟨2,6,false,[true],[],[false,true,false,true,false,true],[true,false,true,false,true,false]⟩
theorem v22 : m22.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m23 : Motif := ⟨2,10,false,[true],[],[false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false]⟩
theorem v23 : m23.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m24 : Motif := ⟨2,9,false,[true],[],[true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,false]⟩
theorem v24 : m24.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m25 : Motif := ⟨5,22,false,[false],[],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩
theorem v25 : m25.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m26 : Motif := ⟨1,22,true,[true],[],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v26 : m26.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
def m27 : Motif := ⟨2,22,false,[true],[],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]⟩
theorem v27 : m27.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  intro L R
  rfl
end BB6Coverage.Agent29PackedLate.M0
