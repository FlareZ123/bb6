import ListSym
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6OneLF14327
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6ListSym BB6.Agent6SymWord (Widths env)

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,true,5⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
def widths : Widths := ⟨6,8⟩
def initial : State := ⟨3,[],[.lit [false,true,false,false,true,false,false,true,false],.rep [false,true,false,false,true,false] false,.lit [true,true,true,false,true,false,false,true,false,true,true],.rep [false,true,false,false,true,false,true,true] true,.lit [true,true]]⟩
def shifted : State := ⟨3,[],[.lit [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,false,false,true,false] false,.lit [true,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true],.rep [false,true,false,false,true,false,true,true] true,.lit [true,true]]⟩
def s0 : State := ⟨3,[.lit []],[.lit [false],.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]]⟩
def d0 : State := ⟨5,[.lit [false,true]],[.lit [],.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule0 (R : List Bool) :
    run0 p 1 ⟨3,[],[false]++R⟩ =
      some ⟨5,[false,true],[]++R⟩ := rfl
theorem h0 (x y : Nat) : run0 p (1) (s0.eval x y)=some (d0.eval x y) := by
  simpa only [s0,d0,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule0 (ev [.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]] (env x y))
def s1 : State := ⟨5,[.lit [false],.lit [true]],[.lit [],.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]]⟩
def d1 : State := ⟨5,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true]],[.lit [],.lit [true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule1 (L R : List Bool) :
    run0 p 6 ⟨5,[false]++L,[]++[true,false,false,true,false,false]++R⟩ =
      some ⟨5,[false]++[true,false,true,true,false,true]++L,[]++R⟩ := rfl
theorem h1 (x y : Nat) : run0 p (6*x) (s1.eval x y)=some (d1.eval x y) := by
  simpa only [s1,d1,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepR p 5 [false] [] [true,false,false,true,false,false] [true,false,true,true,false,true] 6 rule1 x (ev [.lit [true]] (env x y)) (ev [.lit [true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]] (env x y))
def s2 : State := ⟨5,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true]],[.lit [true,false,false,true,false,false],.lit [true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]]⟩
def d2 : State := ⟨5,[.lit [false,true,false,true,true,false,true],.rep [true,false,true,true,false,true] false,.lit [true]],[.lit [],.lit [true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule2 (L : List Bool) (R : List Bool) :
    run0 p 6 ⟨5,[false]++L,[true,false,false,true,false,false]++R⟩ =
      some ⟨5,[false,true,false,true,true,false,true]++L,[]++R⟩ := rfl
theorem h2 (x y : Nat) : run0 p (6) (s2.eval x y)=some (d2.eval x y) := by
  simpa only [s2,d2,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule2 (ev [.rep [true,false,true,true,false,true] false,.lit [true]] (env x y)) (ev [.lit [true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,true,true]] (env x y))
def s3 : State := ⟨5,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true]],[.lit [true,false,true,true],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,true,true]]⟩
def d3 : State := ⟨3,[.lit [false,true,false,true],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true]],[.lit [false],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule3 (L : List Bool) (R : List Bool) :
    run0 p 5 ⟨5,[false]++L,[true,false,true,true]++R⟩ =
      some ⟨3,[false,true,false,true]++L,[false]++R⟩ := rfl
theorem h3 (x y : Nat) : run0 p (5) (s3.eval x y)=some (d3.eval x y) := by
  simpa only [s3,d3,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule3 (ev [.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true]] (env x y)) (ev [.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,true,true]] (env x y))
def s4 : State := ⟨3,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true]],[.lit [false],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,true,true]]⟩
def d4 : State := ⟨3,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true]],[.lit [false],.lit [true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule4 (L R : List Bool) :
    run0 p 22 ⟨3,[false]++L,[false]++[true,false,true,false,false,true,false,true]++R⟩ =
      some ⟨3,[false]++[false,true,true,false,true,true,true,true]++L,[false]++R⟩ := rfl
theorem h4 (x y : Nat) : run0 p (22*y) (s4.eval x y)=some (d4.eval x y) := by
  simpa only [s4,d4,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepR p 3 [false] [false] [true,false,true,false,false,true,false,true] [false,true,true,false,true,true,true,true] 22 rule4 y (ev [.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.lit [true,false,true,false,false,true,false,true,true,true,true]] (env x y))
def s5 : State := ⟨3,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true]],[.lit [false,true,false,true,false,false,true,false,true,true,true,true]]⟩
def d5 : State := ⟨3,[.lit [false,false,true,true,false,true,true,true,true],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true]],[.lit [false,true,true,true]]⟩
theorem rule5 (L : List Bool) :
    run0 p 22 ⟨3,[false]++L,[false,true,false,true,false,false,true,false,true,true,true,true]⟩ =
      some ⟨3,[false,false,true,true,false,true,true,true,true]++L,[false,true,true,true]⟩ := rfl
theorem h5 (x y : Nat) : run0 p (22) (s5.eval x y)=some (d5.eval x y) := by
  simpa only [s5,d5,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule5 (ev [.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true]] (env x y))
def s6 : State := ⟨3,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]],[.lit [false,true,true,true]]⟩
def d6 : State := ⟨3,[.lit [true,false,true,true,true,true],.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]],[.lit [true,true,true]]⟩
theorem rule6 (L : List Bool) :
    run0 p 17 ⟨3,[false]++L,[false,true,true,true]⟩ =
      some ⟨3,[true,false,true,true,true,true]++L,[true,true,true]⟩ := rfl
theorem h6 (x y : Nat) : run0 p (17) (s6.eval x y)=some (d6.eval x y) := by
  simpa only [s6,d6,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule6 (ev [.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]] (env x y))
def s7 : State := ⟨3,[.lit [],.rep [true,false,true,true,true,true,false,true] true,.lit [true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.lit [true,true,true]]⟩
def d7 : State := ⟨3,[.lit [],.lit [true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [false,true,false,true,true,false,true,false] true,.lit [true,true,true]]⟩
theorem rule7 (L R : List Bool) :
    run0 p 12 ⟨3,[]++[true,false,true,true,true,true,false,true]++L,[]++R⟩ =
      some ⟨3,[]++L,[]++[false,true,false,true,true,false,true,false]++R⟩ := rfl
theorem h7 (x y : Nat) : run0 p (12*y) (s7.eval x y)=some (d7.eval x y) := by
  simpa only [s7,d7,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepL p 3 [] [] [true,false,true,true,true,true,false,true] [false,true,false,true,true,false,true,false] 12 rule7 y (ev [.lit [true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.lit [true,true,true]] (env x y))
def s8 : State := ⟨3,[.lit [true,false,true,true,true,true,false,true],.lit [true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [false,true,false,true,true,false,true,false] true,.lit [true,true,true]]⟩
def d8 : State := ⟨3,[.lit [],.lit [true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]],[.lit [false,true,false,true,true,false,true,false],.rep [false,true,false,true,true,false,true,false] true,.lit [true,true,true]]⟩
theorem rule8 (L : List Bool) (R : List Bool) :
    run0 p 12 ⟨3,[true,false,true,true,true,true,false,true]++L,[]++R⟩ =
      some ⟨3,[]++L,[false,true,false,true,true,false,true,false]++R⟩ := rfl
theorem h8 (x y : Nat) : run0 p (12) (s8.eval x y)=some (d8.eval x y) := by
  simpa only [s8,d8,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule8 (ev [.lit [true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.rep [false,true,false,true,true,false,true,false] true,.lit [true,true,true]] (env x y))
def s9 : State := ⟨3,[.lit [true,false,true,true,true,true,true],.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true]],[.lit [],.rep [false,true,false,true,true,false,true,false] true,.lit [false,true,false,true,true,false,true,false,true,true,true]]⟩
def d9 : State := ⟨3,[.lit [true],.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true]],[.lit [true,true,true,false,true,false],.rep [false,true,false,true,true,false,true,false] true,.lit [false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule9 (L : List Bool) (R : List Bool) :
    run0 p 12 ⟨3,[true,false,true,true,true,true,true]++L,[]++R⟩ =
      some ⟨3,[true]++L,[true,true,true,false,true,false]++R⟩ := rfl
theorem h9 (x y : Nat) : run0 p (12) (s9.eval x y)=some (d9.eval x y) := by
  simpa only [s9,d9,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule9 (ev [.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.rep [false,true,false,true,true,false,true,false] true,.lit [false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s10 : State := ⟨3,[.lit [],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true]],[.lit [],.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d10 : State := ⟨3,[.lit [],.lit [true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule10 (L R : List Bool) :
    run0 p 6 ⟨3,[]++[true,false,true,true,false,true]++L,[]++R⟩ =
      some ⟨3,[]++L,[]++[false,true,false,false,true,false]++R⟩ := rfl
theorem h10 (x y : Nat) : run0 p (6*x) (s10.eval x y)=some (d10.eval x y) := by
  simpa only [s10,d10,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepL p 3 [] [] [true,false,true,true,false,true] [false,true,false,false,true,false] 6 rule10 x (ev [.lit [true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s11 : State := ⟨3,[.lit [true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d11 : State := ⟨3,[.lit [true]],[.lit [false,true,false,false,true,false,false,true,false],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule11 (R : List Bool) :
    run0 p 9 ⟨3,[true,false,true,true,false,true,true,false,true,true],[]++R⟩ =
      some ⟨3,[true],[false,true,false,false,true,false,false,true,false]++R⟩ := rfl
theorem h11 (x y : Nat) : run0 p (9) (s11.eval x y)=some (d11.eval x y) := by
  simpa only [s11,d11,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule11 (ev [.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s12 : State := ⟨3,[.lit [true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d12 : State := ⟨0,[.lit [true,true]],[.lit [false],.rep [false,true,false,false,true,false] false,.lit [false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule12 (R : List Bool) :
    run0 p 3 ⟨3,[true],[]++R⟩ =
      some ⟨0,[true,true],[false]++R⟩ := rfl
theorem h12 (x y : Nat) : run0 p (3) (s12.eval x y)=some (d12.eval x y) := by
  simpa only [s12,d12,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule12 (ev [.rep [false,true,false,false,true,false] false,.lit [false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s13 : State := ⟨0,[.lit [true],.lit [true]],[.lit [],.rep [false,false,true,false,false,true] false,.lit [false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d13 : State := ⟨0,[.lit [true],.rep [true,true,false,true,true,false] false,.lit [true]],[.lit [],.lit [false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule13 (L R : List Bool) :
    run0 p 6 ⟨0,[true]++L,[]++[false,false,true,false,false,true]++R⟩ =
      some ⟨0,[true]++[true,true,false,true,true,false]++L,[]++R⟩ := rfl
theorem h13 (x y : Nat) : run0 p (6*x) (s13.eval x y)=some (d13.eval x y) := by
  simpa only [s13,d13,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepR p 0 [true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 rule13 x (ev [.lit [true]] (env x y)) (ev [.lit [false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s14 : State := ⟨0,[.lit [true],.rep [true,true,false,true,true,false] false,.lit [true]],[.lit [false,false,true,false,false,true],.lit [false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d14 : State := ⟨0,[.lit [true,true,true,false,true,true,false],.rep [true,true,false,true,true,false] false,.lit [true]],[.lit [],.lit [false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule14 (L : List Bool) (R : List Bool) :
    run0 p 6 ⟨0,[true]++L,[false,false,true,false,false,true]++R⟩ =
      some ⟨0,[true,true,true,false,true,true,false]++L,[]++R⟩ := rfl
theorem h14 (x y : Nat) : run0 p (6) (s14.eval x y)=some (d14.eval x y) := by
  simpa only [s14,d14,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule14 (ev [.rep [true,true,false,true,true,false] false,.lit [true]] (env x y)) (ev [.lit [false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s15 : State := ⟨0,[.lit [true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true]],[.lit [false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d15 : State := ⟨5,[.lit [true,true,false,true,true,false],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true]],[.lit [],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule15 (L : List Bool) (R : List Bool) :
    run0 p 5 ⟨0,[true]++L,[false,false,true,false,true]++R⟩ =
      some ⟨5,[true,true,false,true,true,false]++L,[]++R⟩ := rfl
theorem h15 (x y : Nat) : run0 p (5) (s15.eval x y)=some (d15.eval x y) := by
  simpa only [s15,d15,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule15 (ev [.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true]] (env x y)) (ev [.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s16 : State := ⟨5,[.lit [],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d16 : State := ⟨5,[.lit [],.lit [true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [true,false,false,true,false,false] false,.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule16 (L R : List Bool) :
    run0 p 6 ⟨5,[]++[true,true,false,true,true,false]++L,[]++R⟩ =
      some ⟨5,[]++L,[]++[true,false,false,true,false,false]++R⟩ := rfl
theorem h16 (x y : Nat) : run0 p (6*x) (s16.eval x y)=some (d16.eval x y) := by
  simpa only [s16,d16,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepL p 5 [] [] [true,true,false,true,true,false] [true,false,false,true,false,false] 6 rule16 x (ev [.lit [true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y)) (ev [.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s17 : State := ⟨5,[.lit [true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [true,false,false,true,false,false] false,.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d17 : State := ⟨5,[.lit [true]],[.lit [true,false,false,true,false,false,true,false,false,true,false,false],.rep [true,false,false,true,false,false] false,.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule17 (R : List Bool) :
    run0 p 12 ⟨5,[true,true,false,true,true,false,true,true,false,true,true,false,true],[]++R⟩ =
      some ⟨5,[true],[true,false,false,true,false,false,true,false,false,true,false,false]++R⟩ := rfl
theorem h17 (x y : Nat) : run0 p (12) (s17.eval x y)=some (d17.eval x y) := by
  simpa only [s17,d17,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule17 (ev [.rep [true,false,false,true,false,false] false,.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s18 : State := ⟨5,[.lit [true]],[.lit [],.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,true,false,true,false,false,true] true,.lit [false,true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d18 : State := ⟨5,[.lit [false,true]],[.lit [],.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,true,false,true,false,false,true] true,.lit [false,true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule18 (R : List Bool) :
    run0 p 2 ⟨5,[true],[]++R⟩ =
      some ⟨5,[false,true],[]++R⟩ := rfl
theorem h18 (x y : Nat) : run0 p (2) (s18.eval x y)=some (d18.eval x y) := by
  simpa only [s18,d18,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule18 (ev [.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,true,false,true,false,false,true] true,.lit [false,true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s19 : State := ⟨5,[.lit [false],.lit [true]],[.lit [],.rep [true,false,false,true,false,false] false,.lit [true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,true,false,true,false,false,true] true,.lit [false,true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d19 : State := ⟨5,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true]],[.lit [],.lit [true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,true,false,true,false,false,true] true,.lit [false,true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule19 (L R : List Bool) :
    run0 p 6 ⟨5,[false]++L,[]++[true,false,false,true,false,false]++R⟩ =
      some ⟨5,[false]++[true,false,true,true,false,true]++L,[]++R⟩ := rfl
theorem h19 (x y : Nat) : run0 p (6*x) (s19.eval x y)=some (d19.eval x y) := by
  simpa only [s19,d19,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepR p 5 [false] [] [true,false,false,true,false,false] [true,false,true,true,false,true] 6 rule19 x (ev [.lit [true]] (env x y)) (ev [.lit [true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,true,false,true,false,false,true] true,.lit [false,true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s20 : State := ⟨5,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true]],[.lit [true,false,false,true,false,false,true,false,false,true,false,false],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d20 : State := ⟨5,[.lit [false,true,false,true,true,false,true,true,false,true,true,false,true],.rep [true,false,true,true,false,true] false,.lit [true]],[.lit [],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule20 (L : List Bool) (R : List Bool) :
    run0 p 12 ⟨5,[false]++L,[true,false,false,true,false,false,true,false,false,true,false,false]++R⟩ =
      some ⟨5,[false,true,false,true,true,false,true,true,false,true,true,false,true]++L,[]++R⟩ := rfl
theorem h20 (x y : Nat) : run0 p (12) (s20.eval x y)=some (d20.eval x y) := by
  simpa only [s20,d20,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule20 (ev [.rep [true,false,true,true,false,true] false,.lit [true]] (env x y)) (ev [.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s21 : State := ⟨5,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d21 : State := ⟨5,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
theorem rule21 (L R : List Bool) :
    run0 p 10 ⟨5,[false]++L,[]++[true,true,false,true,false,false,true,false]++R⟩ =
      some ⟨5,[false]++[false,true,true,false,true,true,true,true]++L,[]++R⟩ := rfl
theorem h21 (x y : Nat) : run0 p (10*y) (s21.eval x y)=some (d21.eval x y) := by
  simpa only [s21,d21,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepR p 5 [false] [] [true,true,false,true,false,false,true,false] [false,true,true,false,true,true,true,true] 10 rule21 y (ev [.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]] (env x y))
def s22 : State := ⟨5,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]]⟩
def d22 : State := ⟨5,[.lit [false,false,true,true,false,true,true,true,true],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [true,true,false,true,false,true,true,true]]⟩
theorem rule22 (L : List Bool) :
    run0 p 10 ⟨5,[false]++L,[true,true,false,true,false,false,true,false,true,true,false,true,false,true,true,true]⟩ =
      some ⟨5,[false,false,true,true,false,true,true,true,true]++L,[true,true,false,true,false,true,true,true]⟩ := rfl
theorem h22 (x y : Nat) : run0 p (10) (s22.eval x y)=some (d22.eval x y) := by
  simpa only [s22,d22,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule22 (ev [.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]] (env x y))
def s23 : State := ⟨5,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [true,true,false,true,false,true,true,true]]⟩
def d23 : State := ⟨5,[.lit [true,true,false,true,true,true,true],.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [true,true]]⟩
theorem rule23 (L : List Bool) :
    run0 p 8 ⟨5,[false]++L,[true,true,false,true,false,true,true,true]⟩ =
      some ⟨5,[true,true,false,true,true,true,true]++L,[true,true]⟩ := rfl
theorem h23 (x y : Nat) : run0 p (8) (s23.eval x y)=some (d23.eval x y) := by
  simpa only [s23,d23,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule23 (ev [.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]] (env x y))
def s24 : State := ⟨5,[.lit [],.rep [true,true,false,true,true,true,true,false] true,.lit [true,true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.lit [true,true]]⟩
def d24 : State := ⟨5,[.lit [],.lit [true,true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [true,false,true,true,false,true,false,false] true,.lit [true,true]]⟩
theorem rule24 (L R : List Bool) :
    run0 p 12 ⟨5,[]++[true,true,false,true,true,true,true,false]++L,[]++R⟩ =
      some ⟨5,[]++L,[]++[true,false,true,true,false,true,false,false]++R⟩ := rfl
theorem h24 (x y : Nat) : run0 p (12*y) (s24.eval x y)=some (d24.eval x y) := by
  simpa only [s24,d24,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepL p 5 [] [] [true,true,false,true,true,true,true,false] [true,false,true,true,false,true,false,false] 12 rule24 y (ev [.lit [true,true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.lit [true,true]] (env x y))
def s25 : State := ⟨5,[.lit [true,true,false,true,true,true,true,false],.lit [true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [true,false,true,true,false,true,false,false] true,.lit [true,true]]⟩
def d25 : State := ⟨5,[.lit [],.lit [true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [true,false,true,true,false,true,false,false],.rep [true,false,true,true,false,true,false,false] true,.lit [true,true]]⟩
theorem rule25 (L : List Bool) (R : List Bool) :
    run0 p 12 ⟨5,[true,true,false,true,true,true,true,false]++L,[]++R⟩ =
      some ⟨5,[]++L,[true,false,true,true,false,true,false,false]++R⟩ := rfl
theorem h25 (x y : Nat) : run0 p (12) (s25.eval x y)=some (d25.eval x y) := by
  simpa only [s25,d25,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule25 (ev [.lit [true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.rep [true,false,true,true,false,true,false,false] true,.lit [true,true]] (env x y))
def s26 : State := ⟨5,[.lit [true,true,false,true,true,true,true,true],.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [true,false,true,true,false,true,false,false] true,.lit [true,false,true,true,false,true,false,false,true,true]]⟩
def d26 : State := ⟨3,[.lit [true],.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [true,true,true,false,true,false,false],.rep [true,false,true,true,false,true,false,false] true,.lit [true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule26 (L : List Bool) (R : List Bool) :
    run0 p 13 ⟨5,[true,true,false,true,true,true,true,true]++L,[]++R⟩ =
      some ⟨3,[true]++L,[true,true,true,false,true,false,false]++R⟩ := rfl
theorem h26 (x y : Nat) : run0 p (13) (s26.eval x y)=some (d26.eval x y) := by
  simpa only [s26,d26,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule26 (ev [.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.rep [true,false,true,true,false,true,false,false] true,.lit [true,false,true,true,false,true,false,false,true,true]] (env x y))
def s27 : State := ⟨3,[.lit [],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d27 : State := ⟨3,[.lit [],.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule27 (L R : List Bool) :
    run0 p 6 ⟨3,[]++[true,false,true,true,false,true]++L,[]++R⟩ =
      some ⟨3,[]++L,[]++[false,true,false,false,true,false]++R⟩ := rfl
theorem h27 (x y : Nat) : run0 p (6*x) (s27.eval x y)=some (d27.eval x y) := by
  simpa only [s27,d27,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepL p 3 [] [] [true,false,true,true,false,true] [false,true,false,false,true,false] 6 rule27 x (ev [.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]] (env x y)) (ev [.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]] (env x y))
def s28 : State := ⟨3,[.lit [true,false,true,true,false,true,true,false,true,true,false,true,true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d28 : State := ⟨3,[.lit [true]],[.lit [false,true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule28 (R : List Bool) :
    run0 p 12 ⟨3,[true,false,true,true,false,true,true,false,true,true,false,true,true],[]++R⟩ =
      some ⟨3,[true],[false,true,false,false,true,false,false,true,false,false,true,false]++R⟩ := rfl
theorem h28 (x y : Nat) : run0 p (12) (s28.eval x y)=some (d28.eval x y) := by
  simpa only [s28,d28,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule28 (ev [.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]] (env x y))
def s29 : State := ⟨3,[.lit [true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [false,true,false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d29 : State := ⟨0,[.lit [true,true]],[.lit [false],.rep [false,true,false,false,true,false] false,.lit [false,true,false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule29 (R : List Bool) :
    run0 p 3 ⟨3,[true],[]++R⟩ =
      some ⟨0,[true,true],[false]++R⟩ := rfl
theorem h29 (x y : Nat) : run0 p (3) (s29.eval x y)=some (d29.eval x y) := by
  simpa only [s29,d29,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule29 (ev [.rep [false,true,false,false,true,false] false,.lit [false,true,false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]] (env x y))
def s30 : State := ⟨0,[.lit [true],.lit [true]],[.lit [],.rep [false,false,true,false,false,true] false,.lit [false,false,true,false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d30 : State := ⟨0,[.lit [true],.rep [true,true,false,true,true,false] false,.lit [true]],[.lit [],.lit [false,false,true,false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule30 (L R : List Bool) :
    run0 p 6 ⟨0,[true]++L,[]++[false,false,true,false,false,true]++R⟩ =
      some ⟨0,[true]++[true,true,false,true,true,false]++L,[]++R⟩ := rfl
theorem h30 (x y : Nat) : run0 p (6*x) (s30.eval x y)=some (d30.eval x y) := by
  simpa only [s30,d30,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepR p 0 [true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 rule30 x (ev [.lit [true]] (env x y)) (ev [.lit [false,false,true,false,false,true,false,false,true,false,false,true,false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]] (env x y))
def s31 : State := ⟨0,[.lit [true],.rep [true,true,false,true,true,false] false,.lit [true]],[.lit [false,false,true,false,false,true,false,false,true,false,false,true],.lit [false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d31 : State := ⟨0,[.lit [true,true,true,false,true,true,false,true,true,false,true,true,false],.rep [true,true,false,true,true,false] false,.lit [true]],[.lit [],.lit [false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule31 (L : List Bool) (R : List Bool) :
    run0 p 12 ⟨0,[true]++L,[false,false,true,false,false,true,false,false,true,false,false,true]++R⟩ =
      some ⟨0,[true,true,true,false,true,true,false,true,true,false,true,true,false]++L,[]++R⟩ := rfl
theorem h31 (x y : Nat) : run0 p (12) (s31.eval x y)=some (d31.eval x y) := by
  simpa only [s31,d31,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule31 (ev [.rep [true,true,false,true,true,false] false,.lit [true]] (env x y)) (ev [.lit [false,true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]] (env x y))
def s32 : State := ⟨0,[.lit [true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [false,true,true],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d32 : State := ⟨3,[.lit [false,true,false],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [false],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule32 (L : List Bool) (R : List Bool) :
    run0 p 4 ⟨0,[true]++L,[false,true,true]++R⟩ =
      some ⟨3,[false,true,false]++L,[false]++R⟩ := rfl
theorem h32 (x y : Nat) : run0 p (4) (s32.eval x y)=some (d32.eval x y) := by
  simpa only [s32,d32,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule32 (ev [.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y)) (ev [.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]] (env x y))
def s33 : State := ⟨3,[.lit [false],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [false],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d33 : State := ⟨3,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [false],.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
theorem rule33 (L R : List Bool) :
    run0 p 22 ⟨3,[false]++L,[false]++[true,false,true,false,false,true,false,true]++R⟩ =
      some ⟨3,[false]++[false,true,true,false,true,true,true,true]++L,[false]++R⟩ := rfl
theorem h33 (x y : Nat) : run0 p (22*y) (s33.eval x y)=some (d33.eval x y) := by
  simpa only [s33,d33,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepR p 3 [false] [false] [true,false,true,false,false,true,false,true] [false,true,true,false,true,true,true,true] 22 rule33 y (ev [.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y)) (ev [.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]] (env x y))
def s34 : State := ⟨3,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [false,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]]⟩
def d34 : State := ⟨3,[.lit [false,false,true,true,false,true,true,true,true],.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [false,true,false,true,false,false,true,true]]⟩
theorem rule34 (L : List Bool) :
    run0 p 22 ⟨3,[false]++L,[false,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true]⟩ =
      some ⟨3,[false,false,true,true,false,true,true,true,true]++L,[false,true,false,true,false,false,true,true]⟩ := rfl
theorem h34 (x y : Nat) : run0 p (22) (s34.eval x y)=some (d34.eval x y) := by
  simpa only [s34,d34,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule34 (ev [.rep [false,true,true,false,true,true,true,true] true,.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y))
def s35 : State := ⟨3,[.lit [false],.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [false,true,false,true,false,false,true,true]]⟩
def d35 : State := ⟨2,[.lit [false,true,false,true,true,false,true,true,true,true],.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [true,true,true]]⟩
theorem rule35 (L : List Bool) :
    run0 p 33 ⟨3,[false]++L,[false,true,false,true,false,false,true,true]⟩ =
      some ⟨2,[false,true,false,true,true,false,true,true,true,true]++L,[true,true,true]⟩ := rfl
theorem h35 (x y : Nat) : run0 p (33) (s35.eval x y)=some (d35.eval x y) := by
  simpa only [s35,d35,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule35 (ev [.rep [false,true,true,false,true,true,true,true] true,.lit [false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y))
def s36 : State := ⟨2,[.lit [false],.rep [true,false,true,true,false,true,true,true] true,.lit [true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.lit [true,true,true]]⟩
def d36 : State := ⟨2,[.lit [false],.lit [true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [true,false,true,false,false,true,false,true] true,.lit [true,true,true]]⟩
theorem rule36 (L R : List Bool) :
    run0 p 12 ⟨2,[false]++[true,false,true,true,false,true,true,true]++L,[]++R⟩ =
      some ⟨2,[false]++L,[]++[true,false,true,false,false,true,false,true]++R⟩ := rfl
theorem h36 (x y : Nat) : run0 p (12*y) (s36.eval x y)=some (d36.eval x y) := by
  simpa only [s36,d36,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepL p 2 [false] [] [true,false,true,true,false,true,true,true] [true,false,true,false,false,true,false,true] 12 rule36 y (ev [.lit [true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,true],.rep [true,true,false,true,true,false] false,.lit [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y)) (ev [.lit [true,true,true]] (env x y))
def s37 : State := ⟨2,[.lit [false,true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,true,true],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [true,false,true,false,false,true,false,true] true,.lit [true,true,true]]⟩
def d37 : State := ⟨2,[.lit [false,true],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true],.rep [true,false,true,false,false,true,false,true] true,.lit [true,true,true]]⟩
theorem rule37 (L : List Bool) (R : List Bool) :
    run0 p 24 ⟨2,[false,true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,true,true]++L,[]++R⟩ =
      some ⟨2,[false,true]++L,[true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true]++R⟩ := rfl
theorem h37 (x y : Nat) : run0 p (24) (s37.eval x y)=some (d37.eval x y) := by
  simpa only [s37,d37,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule37 (ev [.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y)) (ev [.rep [true,false,true,false,false,true,false,true] true,.lit [true,true,true]] (env x y))
def s38 : State := ⟨2,[.lit [false,true,true],.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]]⟩
def d38 : State := ⟨3,[.lit [true],.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [true,true],.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule38 (L : List Bool) (R : List Bool) :
    run0 p 4 ⟨2,[false,true,true]++L,[]++R⟩ =
      some ⟨3,[true]++L,[true,true]++R⟩ := rfl
theorem h38 (x y : Nat) : run0 p (4) (s38.eval x y)=some (d38.eval x y) := by
  simpa only [s38,d38,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule38 (ev [.rep [false,true,true,false,true,true] false,.lit [false,true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y)) (ev [.rep [true,false,true,false,false,true,false,true] true,.lit [true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]] (env x y))
def s39 : State := ⟨3,[.lit [],.rep [true,false,true,true,false,true] false,.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]]⟩
def d39 : State := ⟨3,[.lit [],.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule39 (L R : List Bool) :
    run0 p 6 ⟨3,[]++[true,false,true,true,false,true]++L,[]++R⟩ =
      some ⟨3,[]++L,[]++[false,true,false,false,true,false]++R⟩ := rfl
theorem h39 (x y : Nat) : run0 p (6*x) (s39.eval x y)=some (d39.eval x y) := by
  simpa only [s39,d39,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using sweepL p 3 [] [] [true,false,true,true,false,true] [false,true,false,false,true,false] 6 rule39 x (ev [.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]] (env x y)) (ev [.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]] (env x y))
def s40 : State := ⟨3,[.lit [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]],[.lit [],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]]⟩
def d40 : State := ⟨3,[.lit []],[.lit [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false],.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]]⟩
theorem rule40 (R : List Bool) :
    run0 p 15 ⟨3,[true,false,true,true,false,true,true,false,true,true,false,true,true,false,true],[]++R⟩ =
      some ⟨3,[],[false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]++R⟩ := rfl
theorem h40 (x y : Nat) : run0 p (15) (s40.eval x y)=some (d40.eval x y) := by
  simpa only [s40,d40,State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using rule40 (ev [.rep [false,true,false,false,true,false] false,.lit [true],.rep [true,true,false,true,false,false,true,false] true,.lit [true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,true,true]] (env x y))
theorem period (x y : Nat) : run0 p (48*x+90*y+296) (initial.eval x y)=some (shifted.eval x y) := by
  have H0 := h0 x y
  rw [← State.same_sound widths initial s0 (by decide +kernel) x y] at H0
  have H1 := h1 x y
  rw [← State.same_sound widths d0 s1 (by decide +kernel) x y] at H1
  have H2 := h2 x y
  rw [← State.same_sound widths d1 s2 (by decide +kernel) x y] at H2
  have H3 := h3 x y
  rw [← State.same_sound widths d2 s3 (by decide +kernel) x y] at H3
  have H4 := h4 x y
  rw [← State.same_sound widths d3 s4 (by decide +kernel) x y] at H4
  have H5 := h5 x y
  rw [← State.same_sound widths d4 s5 (by decide +kernel) x y] at H5
  have H6 := h6 x y
  rw [← State.same_sound widths d5 s6 (by decide +kernel) x y] at H6
  have H7 := h7 x y
  rw [← State.same_sound widths d6 s7 (by decide +kernel) x y] at H7
  have H8 := h8 x y
  rw [← State.same_sound widths d7 s8 (by decide +kernel) x y] at H8
  have H9 := h9 x y
  rw [← State.same_sound widths d8 s9 (by decide +kernel) x y] at H9
  have H10 := h10 x y
  rw [← State.same_sound widths d9 s10 (by decide +kernel) x y] at H10
  have H11 := h11 x y
  rw [← State.same_sound widths d10 s11 (by decide +kernel) x y] at H11
  have H12 := h12 x y
  rw [← State.same_sound widths d11 s12 (by decide +kernel) x y] at H12
  have H13 := h13 x y
  rw [← State.same_sound widths d12 s13 (by decide +kernel) x y] at H13
  have H14 := h14 x y
  rw [← State.same_sound widths d13 s14 (by decide +kernel) x y] at H14
  have H15 := h15 x y
  rw [← State.same_sound widths d14 s15 (by decide +kernel) x y] at H15
  have H16 := h16 x y
  rw [← State.same_sound widths d15 s16 (by decide +kernel) x y] at H16
  have H17 := h17 x y
  rw [← State.same_sound widths d16 s17 (by decide +kernel) x y] at H17
  have H18 := h18 x y
  rw [← State.same_sound widths d17 s18 (by decide +kernel) x y] at H18
  have H19 := h19 x y
  rw [← State.same_sound widths d18 s19 (by decide +kernel) x y] at H19
  have H20 := h20 x y
  rw [← State.same_sound widths d19 s20 (by decide +kernel) x y] at H20
  have H21 := h21 x y
  rw [← State.same_sound widths d20 s21 (by decide +kernel) x y] at H21
  have H22 := h22 x y
  rw [← State.same_sound widths d21 s22 (by decide +kernel) x y] at H22
  have H23 := h23 x y
  rw [← State.same_sound widths d22 s23 (by decide +kernel) x y] at H23
  have H24 := h24 x y
  rw [← State.same_sound widths d23 s24 (by decide +kernel) x y] at H24
  have H25 := h25 x y
  rw [← State.same_sound widths d24 s25 (by decide +kernel) x y] at H25
  have H26 := h26 x y
  rw [← State.same_sound widths d25 s26 (by decide +kernel) x y] at H26
  have H27 := h27 x y
  rw [← State.same_sound widths d26 s27 (by decide +kernel) x y] at H27
  have H28 := h28 x y
  rw [← State.same_sound widths d27 s28 (by decide +kernel) x y] at H28
  have H29 := h29 x y
  rw [← State.same_sound widths d28 s29 (by decide +kernel) x y] at H29
  have H30 := h30 x y
  rw [← State.same_sound widths d29 s30 (by decide +kernel) x y] at H30
  have H31 := h31 x y
  rw [← State.same_sound widths d30 s31 (by decide +kernel) x y] at H31
  have H32 := h32 x y
  rw [← State.same_sound widths d31 s32 (by decide +kernel) x y] at H32
  have H33 := h33 x y
  rw [← State.same_sound widths d32 s33 (by decide +kernel) x y] at H33
  have H34 := h34 x y
  rw [← State.same_sound widths d33 s34 (by decide +kernel) x y] at H34
  have H35 := h35 x y
  rw [← State.same_sound widths d34 s35 (by decide +kernel) x y] at H35
  have H36 := h36 x y
  rw [← State.same_sound widths d35 s36 (by decide +kernel) x y] at H36
  have H37 := h37 x y
  rw [← State.same_sound widths d36 s37 (by decide +kernel) x y] at H37
  have H38 := h38 x y
  rw [← State.same_sound widths d37 s38 (by decide +kernel) x y] at H38
  have H39 := h39 x y
  rw [← State.same_sound widths d38 s39 (by decide +kernel) x y] at H39
  have H40 := h40 x y
  rw [← State.same_sound widths d39 s40 (by decide +kernel) x y] at H40
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (H0) H1) H2) H3) H4) H5) H6) H7) H8) H9) H10) H11) H12) H13) H14) H15) H16) H17) H18) H19) H20) H21) H22) H23) H24) H25) H26) H27) H28) H29) H30) H31) H32) H33) H34) H35) H36) H37) H38) H39) H40
  rw [State.same_sound widths d40 shifted (by decide +kernel) x y] at H
  rw [show 1+6*x+6+5+22*y+22+17+12*y+12+12+6*x+9+3+6*x+6+5+6*x+12+2+6*x+12+10*y+10+8+12*y+12+13+6*x+12+3+6*x+12+4+22*y+22+33+12*y+24+4+6*x+15=48*x+90*y+296 by omega] at H
  exact H
def family (k : Nat) := initial.eval k k
theorem shift_eq (k : Nat) : shifted.eval k k=family (k+1) := by
  unfold family shifted initial State.eval
  simp only [ev,env,Bool.false_eq_true,ite_false,ite_true,rep,List.append_assoc,List.cons_append,List.nil_append]
theorem seed : run0 p 191 ⟨0,[],[]⟩=some (family 0) := by decide +kernel
theorem growth (k : Nat) : run0 p (138*k+296) (family k)=some (family (k+1)) := by
  have h:=period k k
  rw [shift_eq,show 48*k+90*k+296=138*k+296 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 191 (fun k => 138*k+296) seed (by intro k; omega) growth m hm
#print axioms period
#print axioms never
end BB6.Agent6OneLF14327
