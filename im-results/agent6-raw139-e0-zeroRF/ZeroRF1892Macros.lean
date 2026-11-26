import PadGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E0ZeroRF1892
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def O (n : Nat) : List Bool := rep [true] n
def Zs (n : Nat) : List Bool := rep [false] n
def A (L R : List Bool) : Z0 := ⟨0,false::L,R⟩

theorem transfer (y : Nat) (U T : List Bool) : run0 p (3*y+5) ⟨2,false::(O (y+1)++false::U),T⟩ = some (A (true::U) (O (y+1)++T)) := by
  have block (L R : List Bool) : run0 p 3 ⟨2,[false,true]++[true]++L,R⟩ = some ⟨2,[false,true]++L,[true]++R⟩ := rfl
  have finish (L R : List Bool) : run0 p 5 ⟨2,[false,true,false]++L,R⟩ = some (A (true::L) (true::R)) := rfl
  exact join0 (sweepL p 2 [false,true] [] [true] [true] 3 block y (false::U) T) (finish U (O y++T))

theorem r00 (x : Nat) (U T : List Bool) : run0 p (3*x+10) (A (O x++false::U) ([false,false]++T)) = some (A (true::U) (O (x+2)++T)) := by
  have h (L R : List Bool) : run0 p 2 (A L ([false,false]++R)) = some ⟨2,[false,true,true]++L,R⟩ := rfl
  have H := join0 (h (O x++false::U) T) (transfer (x+1) U T)
  rw [show 3*x+10=2+(3*(x+1)+5) by omega]
  exact H

theorem r01 (x y : Nat) (U T : List Bool) : run0 p (x+3*y+10) (A (O x++false::(O (y+1)++false::U)) ([false,true]++T)) = some (A (true::U) (O (y+1)++(Zs (x+3)++T))) := by
  have h (L R : List Bool) : run0 p 2 (A L ([false,true]++R)) = some ⟨2,[true,true,true]++L,R⟩ := rfl
  have block (L R : List Bool) : run0 p 1 ⟨2,[true]++L,R⟩ = some ⟨2,L,[false]++R⟩ := rfl
  have h1 := sweepL p 2 [] [] [true] [false] 1 block (x+3) (false::(O (y+1)++false::U)) T
  have H := join0 (join0 (h (O x++false::(O (y+1)++false::U)) T) h1) (transfer y U (Zs (x+3)++T))
  rw [show x+3*y+10=2+1*(x+3)+(3*y+5) by omega]
  exact H

theorem r111 (x : Nat) (U T : List Bool) : run0 p (3*x+10) (A (O x++false::U) ([true,true,true]++T)) = some (A (true::U) (O (x+1)++[false,false]++T)) := by
  have h (L R : List Bool) : run0 p 5 (A L ([true,true,true]++R)) = some ⟨2,[false,true]++L,[false,false]++R⟩ := rfl
  have H := join0 (h (O x++false::U) T) (transfer x U ([false,false]++T))
  rw [show 3*x+10=5+(3*x+5) by omega]
  simpa only [List.append_assoc] using H

theorem r110 (L T : List Bool) : run0 p 8 (A L ([true,true,false]++T)) = some (A ([true,true]++L) (true::T)) := rfl
theorem r100 (L T : List Bool) : run0 p 5 (A L ([true,false,false]++T)) = some (A ([true,false,true]++L) T) := rfl
theorem r1011 (L T : List Bool) : run0 p 8 (A L ([true,false,true,true]++T)) = some (A ([true,false,false,true]++L) T) := rfl
theorem r10100 (L T : List Bool) : run0 p 5 (A L ([true,false,true,false,false]++T)) = some (A ([true,false,false,false,true]++L) T) := rfl

#print axioms r00
#print axioms r01
#print axioms r111
#print axioms r110
#print axioms r100
#print axioms r1011
#print axioms r10100
end BB6.Agent6E0ZeroRF1892
