import Hybrid
import PadGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6OneLFTriple
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth

inductive Kind where
  | a | b | c
def p (v : Kind) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (match v with | .c => ⟨true,false,5⟩ | _ => ⟨true,false,0⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some (match v with | .a => ⟨false,true,0⟩ | _ => ⟨true,true,1⟩))
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
def overhead : Kind → Nat | .a => 4 | _ => 2
def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def W : List Bool := [false,true,true]
def t : List Bool := [false,true,false,true,true]
def F (m : Nat) : Z0 := ⟨5,[],rep P (m+1)++[true,true]++rep W m⟩
theorem rep_add (w : List Bool) (a b : Nat) : rep w (a+b)=rep w a++rep w b := by
  induction a with
  | zero => simp only [Nat.zero_add,rep,List.nil_append]
  | succ a ih =>
    rw [Nat.succ_add,rep,ih,rep,List.append_assoc]
theorem rep_double (w : List Bool) (j : Nat) : rep w (2*j)=rep (w++w) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega,rep_add,ih,show rep w 2=w++w by simp [rep]]
    exact rep_snoc _ _
theorem rep_double_odd (w : List Bool) (j : Nat) : rep w (2*j+1)=rep (w++w) j++w := by
  rw [rep_add,rep_double]; simp [rep]
theorem F_right (m : Nat) :
    [true]++rep Q (m+1)++[true]++rep W m = (F m).r := by
  have h := rotate true [false] (m+1)
  change [true]++rep Q (m+1)=rep P (m+1)++[true] at h
  simp only [F,h,List.append_assoc,List.cons_append,List.nil_append]
theorem setup (v : Kind) (m : Nat) :
    run0 (p v) (overhead v) (F m) =
      some ⟨0,[false]++Q,rep P m++[true,true]++rep W m⟩ := by
  cases m <;> cases v <;> rfl
theorem right2 (v : Kind) (L R : List Bool) :
    run0 (p v) 2 ⟨0,[false]++L,P++R⟩ =
      some ⟨0,[false]++Q++L,R⟩ := by cases v <;> rfl
theorem enter (v : Kind) (L R : List Bool) :
    run0 (p v) 2 ⟨0,[false]++L,[true,true]++R⟩ =
      some ⟨0,[true,false,true]++L,R⟩ := by cases v <;> rfl
theorem right5 (v : Kind) (L R : List Bool) :
    run0 (p v) 5 ⟨0,[true,false,true]++L,W++R⟩ =
      some ⟨0,[true,false,true]++W++L,R⟩ := by cases v <;> rfl
theorem turn12 (v : Kind) (L : List Bool) :
    run0 (p v) 12 ⟨0,[true,false,true]++L,[]⟩ =
      some ⟨2,[true]++L,t⟩ := by cases v <;> rfl
theorem rightPhase (v : Kind) (m : Nat) :
    run0 (p v) (overhead v+7*m+14) (F m) =
      some ⟨2,[true]++rep W m++rep Q (m+1),t⟩ := by
  have h := sweepR (p v) 0 [false] [] P Q 2 (right2 v) m Q ([true,true]++rep W m)
  have h' : run0 (p v) (2*m) ⟨0,[false]++Q,rep P m++[true,true]++rep W m⟩ =
      some ⟨0,[false]++rep Q (m+1),[true,true]++rep W m⟩ := by
    have eq : [false]++rep Q m++Q = [false]++rep Q (m+1) := by
      rw [List.append_assoc,rep_snoc]
      rfl
    rw [eq] at h
    simpa only [List.nil_append,List.append_assoc] using h
  have h2 := sweepR (p v) 0 [true,false,true] [] W W 5 (right5 v) m (rep Q (m+1)) []
  have h2' : run0 (p v) (5*m) ⟨0,[true,false,true]++rep Q (m+1),rep W m⟩ =
      some ⟨0,[true,false,true]++rep W m++rep Q (m+1),[]⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using h2
  have H := join0 (join0 (join0 (join0 (setup v m) h') (enter v (rep Q (m+1)) (rep W m))) h2') (turn12 v (rep W m++rep Q (m+1)))
  rw [show overhead v+2*m+2+5*m+12=overhead v+7*m+14 by omega] at H
  simpa only [List.append_assoc] using H

theorem left10 (v : Kind) (L R : List Bool) :
    run0 (p v) 10 ⟨2,[true]++(W++W)++L,t++R⟩ =
      some ⟨2,[true]++L,t++(W++W)++R⟩ := by cases v <;> rfl
theorem even3 (v : Kind) (L R : List Bool) :
    run0 (p v) 3 ⟨2,[true]++Q++L,t++R⟩ =
      some ⟨2,Q++L,W++W++R⟩ := by cases v <;> rfl
theorem odd6 (v : Kind) (L R : List Bool) :
    run0 (p v) 6 ⟨2,[true]++W++Q++L,t++R⟩ =
      some ⟨2,Q++Q++L,[true]++W++W++R⟩ := by cases v <;> rfl
theorem left4 (v : Kind) (L R : List Bool) :
    run0 (p v) 4 ⟨2,Q++(Q++Q)++L,R⟩ =
      some ⟨2,Q++L,(Q++Q)++R⟩ := by cases v <;> rfl
theorem finish3 (v : Kind) (R : List Bool) :
    run0 (p v) 3 ⟨2,Q,R⟩ = some ⟨5,[],[true]++Q++R⟩ := by cases v <;> rfl
theorem leftEnd (v : Kind) (j : Nat) (R : List Bool) :
    run0 (p v) (4*j+3) ⟨2,Q++rep (Q++Q) j,R⟩ =
      some ⟨5,[],[true]++rep Q (2*j+1)++R⟩ := by
  have h := sweepL (p v) 2 Q [] (Q++Q) (Q++Q) 4 (left4 v) j [] R
  have h' : run0 (p v) (4*j) ⟨2,Q++rep (Q++Q) j,R⟩ =
      some ⟨2,Q,rep (Q++Q) j++R⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using h
  have H := join0 h' (finish3 v (rep (Q++Q) j++R))
  rw [show 2*j+1=1+2*j by omega,rep_add,rep_double]
  simpa only [rep,List.append_nil,List.append_assoc] using H

theorem advanceEven (v : Kind) (j : Nat) :
    run0 (p v) (overhead v+14*(2*j)+20) (F (2*j)) =
      some (F (2*j+1)) := by
  have h := rightPhase v (2*j)
  rw [rep_double W] at h
  have h2 := sweepL (p v) 2 [true] t (W++W) (W++W) 10 (left10 v) j (rep Q (2*j+1)) []
  have h2' : run0 (p v) (10*j) ⟨2,[true]++rep (W++W) j++rep Q (2*j+1),t⟩ =
      some ⟨2,[true]++rep Q (2*j+1),t++rep (W++W) j⟩ := by
    simpa only [List.append_nil,List.append_assoc] using h2
  have h3 := even3 v (rep Q (2*j)) (rep (W++W) j)
  have h3' : run0 (p v) 3 ⟨2,[true]++rep Q (2*j+1),t++rep (W++W) j⟩ =
      some ⟨2,Q++rep (Q++Q) j,rep (W++W) (j+1)⟩ := by
    rw [← rep_double Q]
    simpa only [rep,List.append_assoc] using h3
  have H := join0 (join0 (join0 h h2') h3') (leftEnd v j (rep (W++W) (j+1)))
  rw [show overhead v+7*(2*j)+14+10*j+3+(4*j+3)=overhead v+14*(2*j)+20 by omega] at H
  have eq : [true]++rep Q (2*j+1)++rep (W++W) (j+1) = (F (2*j+1)).r := by
    rw [← rep_double W,show 2*(j+1)=1+(2*j+1) by omega,rep_add W 1,← F_right]
    have e : rep Q (2*j+1+1)=rep Q (2*j+1)++Q := (rep_snoc Q (2*j+1)).symm
    rw [e]
    rw [show rep W 1 = Q++[true] by rfl]
    simp only [List.append_assoc]
  rw [eq] at H
  exact H

theorem advanceOdd (v : Kind) (j : Nat) :
    run0 (p v) (overhead v+14*(2*j+1)+20) (F (2*j+1)) =
      some (F (2*j+2)) := by
  have h := rightPhase v (2*j+1)
  rw [rep_double_odd W] at h
  have h2 := sweepL (p v) 2 [true] t (W++W) (W++W) 10 (left10 v) j (W++rep Q (2*j+1+1)) []
  have h2' : run0 (p v) (10*j) ⟨2,[true]++(rep (W++W) j++W)++rep Q (2*j+1+1),t⟩ =
      some ⟨2,[true]++W++rep Q (2*j+1+1),t++rep (W++W) j⟩ := by
    simpa only [List.append_nil,List.append_assoc] using h2
  have h3 := odd6 v (rep Q (2*j+1)) (rep (W++W) j)
  have h3' : run0 (p v) 6 ⟨2,[true]++W++rep Q (2*j+1+1),t++rep (W++W) j⟩ =
      some ⟨2,Q++rep (Q++Q) (j+1),[true]++rep (W++W) (j+1)⟩ := by
    have e : rep (Q++Q) (j+1)=Q++rep Q (2*j+1) := by
      rw [← rep_double Q,show 2*(j+1)=2*j+1+1 by omega]
      rfl
    rw [e]
    have eW : rep (W++W) (j+1)=(W++W)++rep (W++W) j := rfl
    rw [eW,show rep Q (2*j+1+1)=Q++rep Q (2*j+1) by rfl]
    simpa only [List.append_assoc] using h3
  have H := join0 (join0 (join0 h h2') h3') (leftEnd v (j+1) ([true]++rep (W++W) (j+1)))
  rw [show overhead v+7*(2*j+1)+14+10*j+6+(4*(j+1)+3)=overhead v+14*(2*j+1)+20 by omega,
      ← rep_double W,show 2*(j+1)=2*j+2 by omega] at H
  have eq : [true]++rep Q (2*j+2+1)++([true]++rep W (2*j+2))=(F (2*j+2)).r := by
    simpa only [List.append_assoc] using F_right (2*j+2)
  rw [eq] at H
  exact H

def family (j : Nat) := F (2*j)
def cost (v : Kind) (j : Nat) := (overhead v+14*(2*j)+20)+(overhead v+14*(2*j+1)+20)
theorem seed (v : Kind) : run0 (p v) 8 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem growth (v : Kind) (j : Nat) :
    run0 (p v) (cost v j) (family j) = some (family (j+1)) := by
  have h := join0 (advanceEven v j) (advanceOdd v j)
  rw [show 2*j+2=2*(j+1) by omega] at h
  exact h
theorem never (v : Kind) (m : Machine) (hm : compatible (p v) m) : NeverHalts m :=
  never_of_pad_growth (p v) family 8 (cost v) (exactRun (seed v))
    (by intro j; unfold cost; omega) (fun j => exactRun (growth v j)) m hm
#print axioms never
end BB6.Agent6OneLFTriple
