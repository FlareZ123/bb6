import Q0HalfCoverage

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 8000000

def run (s : Bool) (w : List Bool) (p y : Nat) : Option (Nat × Nat) :=
  match w with
  | [] => some (p,y)
  | d::v => if numerator s d p y%4=0 then
      run (!s) v (p+len s d) (numerator s d p y/4) else none

theorem run_sound {s w p y P Y} (h : run s w p y=some (P,Y)) : Trace s w p y P Y := by
  induction w generalizing s p y with
  | nil => simp [run] at h; obtain ⟨rfl,rfl⟩ := h; exact .nil ..
  | cons d w ih =>
    by_cases hd : numerator s d p y%4=0
    · simp only [run,if_pos hd] at h
      exact .cons s d hd (ih h)
    · simp [run,hd] at h

def w56 : List Bool := List.replicate 47 false ++ [true,false,true,true,false,false,false,false,false]
def v56 : List Bool := List.replicate 46 false ++ [true,false,true,true,true,true,true,true,true,true]
def z56 : List Bool := List.replicate 46 true ++ [false,false,true,false,true,false,false,true,false,true]

theorem crossing56 : Cross2 2 2 56 := by
  let p : Nat := 10384593717069655257060992658440018
  let y : Nat := 16697335249881209147839387533312
  let h : Nat := 3208740581827705672538529988608
  let p2 : Nat := 10384593717069655257060992658440390
  let h2 : Nat := 3461488323768523192504134383173698
  let p3 : Nat := 10384593717069655257060992658440708
  let h3 : Nat := 2761104764795550259482406400207668
  refine ⟨false,w56,v56,z56,p,y,h,p2,h2,p3,h3,by decide,by decide,by decide,by decide,by decide,by unfold valid bit; decide,?_,?_,?_⟩
  all_goals apply run_sound; decide

#print axioms crossing56
end BB429Q0Macro.HalfStep
