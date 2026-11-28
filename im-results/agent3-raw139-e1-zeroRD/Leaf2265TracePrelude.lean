import Leaf2265MacroAll

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Only fixed, small repetitions are unfolded in the astronomical trace.
The giant P-stack and giant Q-stack remain opaque to simplification. -/

@[simp] theorem S_consP (k : Nat) (r : Ray) :
    S k (cons false (cons true r)) = S (k+1) r := by
  simpa [pre,P] using S_push k r

@[simp] theorem repTrue0 (r : Ray) : rep [true] 0 r = r := by rfl
@[simp] theorem repTrue1 (r : Ray) : rep [true] 1 r = pre [true] r := by rfl
@[simp] theorem repTrue2 (r : Ray) : rep [true] 2 r = pre [true,true] r := by rfl
@[simp] theorem repTrue3 (r : Ray) : rep [true] 3 r = pre [true,true,true] r := by rfl
@[simp] theorem repTrue4 (r : Ray) : rep [true] 4 r = pre [true,true,true,true] r := by rfl
@[simp] theorem repTrue5 (r : Ray) : rep [true] 5 r = pre [true,true,true,true,true] r := by rfl
@[simp] theorem repTrue6 (r : Ray) : rep [true] 6 r = pre [true,true,true,true,true,true] r := by rfl

@[simp] theorem repGTrue0 (r : Ray) : rep [true,true,false,false] 0 r = r := by rfl
@[simp] theorem repGTrue1 (r : Ray) : rep [true,true,false,false] 1 r = pre [true,true,false,false] r := by rfl
@[simp] theorem repGTrue2 (r : Ray) : rep [true,true,false,false] 2 r = pre [true,true,false,false,true,true,false,false] r := by rfl

#print axioms S_consP
#print axioms repTrue6
#print axioms repGTrue2
end BB6.Agent3Leaf2265
