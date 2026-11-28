import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent7D100Countdown
open BB6Coverage BB6Coverage.Agent31Pump

/-- 1RB0LE_1RC1LD_0RD0RB_0LD0LA_1LA0RF_1RE--- -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true  => some (some ⟨false,false,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true  => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | _,_ => none

def V : List Bool := [true,false]
def W : List Bool := [false,true]
def U (n : Nat) : List Bool := rep [true] n

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega]
    simp only [rep,ih,List.append_assoc]

theorem U_add (a b : Nat) : U (a+b) = U a ++ U b := rep_add [true] a b

theorem U_block (k n : Nat) : rep (U k) n = U (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ,Nat.add_comm (k*n) k,U_add]
    simp only [rep,ih]

theorem V_rotate (n : Nat) : rep V n ++ [true] = true::rep W n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    rfl

theorem W_rotate (n : Nat) : rep W n ++ [false] = false::rep V n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    rfl

theorem V_tail (n : Nat) (R : List Bool) : rep V n ++ true::R = true::(rep W n++R) := by
  have h := congrArg (fun x : List Bool => x++R) (V_rotate n)
  simpa only [List.cons_append,List.nil_append,List.append_assoc] using h

theorem A_first (R : List Bool) :
    run0 table 5 ⟨0,[],true::R⟩ = some ⟨2,[true,true,true],R⟩ := by rfl

theorem C_pair (L R : List Bool) :
    run0 table 2 ⟨2,[true]++L,W++R⟩ = some ⟨2,[true]++V++L,R⟩ := by rfl

theorem scan (n : Nat) (R : List Bool) :
    run0 table (5+2*n) ⟨0,[],rep V n++true::R⟩ =
    some ⟨2,true::rep V n++[true,true],R⟩ := by
  have h := A_first (rep W n++R)
  have g := sweepR table 2 [true] [] W V 2 C_pair n [true,true] R
  have H := join0 h (by simpa only [List.nil_append,List.cons_append] using g)
  rw [V_tail]
  simpa only [List.cons_append,List.nil_append] using H

theorem double_turn (L R : List Bool) :
    run0 table 4 ⟨2,true::true::false::L,true::R⟩ =
    some ⟨0,false::L,false::false::true::R⟩ := by rfl

theorem scan_double (m : Nat) (R : List Bool) :
    run0 table (9+2*(m+1)) ⟨0,[],rep V (m+1)++true::true::R⟩ =
    some ⟨0,rep W (m+1)++[true],false::false::true::R⟩ := by
  have h := scan (m+1) (true::R)
  have g := double_turn (rep V m++[true,true]) R
  have H := join0 h (by simpa only [rep,V,List.cons_append,List.nil_append] using g)
  change run0 table (5+2*(m+1)+4) _ = some ⟨0,false::(rep V m++true::[true]),false::false::true::R⟩ at H
  rw [V_tail m [true]] at H
  rw [show 9+2*(m+1)=5+2*(m+1)+4 by omega]
  simpa only [rep,W,List.cons_append,List.nil_append,List.append_assoc] using H

theorem A_pair (L R : List Bool) :
    run0 table 4 ⟨0,[false]++L,[false,false]++V++R⟩ =
    some ⟨0,[false]++U 2++L,[false,false]++R⟩ := by rfl

theorem A_scan (q : Nat) (L R : List Bool) :
    run0 table (4*q) ⟨0,false::L,false::false::rep V q++R⟩ =
    some ⟨0,false::(U (2*q)++L),false::false::R⟩ := by
  have h := sweepR table 0 [false] [false,false] V (U 2) 4 A_pair q L R
  simpa only [List.cons_append,List.nil_append,U_block] using h

theorem end_one (L : List Bool) :
    run0 table 10 ⟨0,false::L,[false,false,true]⟩ =
    some ⟨0,U 3++L,[false,false,false]⟩ := by rfl

theorem end_zero (L : List Bool) :
    run0 table 6 ⟨0,false::L,[false,false,false]⟩ =
    some ⟨0,U 1++L,[false,false,false]⟩ := by rfl

/-- The double-one separator is read, and the right alternating word
    is converted to a unary block on the left. -/
theorem gather_one (m q : Nat) :
    run0 table (9+2*(m+1)+4*q+10)
      ⟨0,[],rep V (m+1)++true::rep V q++[true]⟩ =
    some ⟨0,U (2*q+4)++rep W m++[true],[false,false,false]⟩ := by
  have h := scan_double m (rep W q)
  rw [← V_rotate] at h
  have g := A_scan q (true::rep W m++[true]) [true]
  have H := join0 h (by simpa only [rep,W,List.cons_append,List.nil_append] using g)
  have K := join0 H (by simpa only [W,List.append_assoc,List.cons_append] using end_one (U (2*q)++true::rep W m++[true]))
  rw [show 2*q+4=3+(2*q+1) by omega,U_add,U_add,show U 1=[true] by rfl]
  simpa only [W,List.cons_append,List.nil_append,List.append_assoc] using K

/-- Variant for the pure-alternating restart: the final bit is zero. -/
theorem gather_zero (m : Nat) :
    run0 table (9+2*(m+1)+8+6)
      ⟨0,[],rep V (m+1)++true::rep V 2++[false]⟩ =
    some ⟨0,U 6++rep W m++[true],[false,false,false]⟩ := by
  have h := scan_double m [false,true,false,false]
  have g := A_scan 2 (true::rep W m++[true]) [false]
  have H := join0 h (by simpa only [rep,W,V,List.cons_append,List.nil_append,List.append_assoc] using g)
  have K := join0 H (end_zero (U (2*2)++true::rep W m++[true]))
  simpa only [U,rep,Nat.reduceMul,V,List.cons_append,List.nil_append,List.append_assoc] using K

theorem init_four (L : List Bool) :
    run0 table 20 ⟨0,U 4++L,[false,false,false]⟩ =
    some ⟨0,L,rep V 3++[true]⟩ := by rfl

theorem A_to_E (L R : List Bool) :
    run0 table 1 ⟨0,true::true::L,R⟩ = some ⟨4,true::L,false::R⟩ := by rfl

theorem E_pair (L R : List Bool) :
    run0 table 2 ⟨4,[true]++L,[false]++V++R⟩ =
    some ⟨4,[true]++V++L,[false]++R⟩ := by rfl

theorem E_end (L : List Bool) :
    run0 table 5 ⟨4,true::L,[false,true]⟩ =
    some ⟨0,rep V 2++L,[true]⟩ := by rfl

theorem A_left (L R : List Bool) :
    run0 table 2 ⟨0,[]++V++L,[]++R⟩ = some ⟨0,[]++L,[]++V++R⟩ := by rfl

theorem A_left_all (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨0,rep V n++L,R⟩ = some ⟨0,L,rep V n++R⟩ := by
  simpa only [List.nil_append] using sweepL table 0 [] [] V V 2 A_left n L R

theorem E_scan (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨4,true::L,false::rep V n++R⟩ =
    some ⟨4,true::rep V n++L,false::R⟩ := by
  simpa only [List.cons_append,List.nil_append] using sweepR table 4 [true] [false] V V 2 E_pair n L R

/-- Two unary cells are removed and two alternating pairs are added. -/
theorem pump_one (b : Nat) (L : List Bool) :
    run0 table (4*b+10) ⟨0,U 2++L,rep V b++[true]⟩ =
    some ⟨0,L,rep V (b+2)++[true]⟩ := by
  have h := join0 (A_to_E L (rep V b++[true])) (E_scan b L [true])
  have H := join0 h (E_end (rep V b++L))
  have K := A_left_all (b+2) L [true]
  rw [Nat.add_comm b 2,rep_add,List.append_assoc] at K
  have J := join0 H K
  rw [show 4*b+10=1+2*b+5+2*(b+2) by omega]
  simpa only [Nat.add_comm b 2,rep_add,List.append_assoc,List.cons_append,List.nil_append,show U 2=[true,true] by rfl] using J

def pumpCost (b q : Nat) : Nat := 4*b*q+4*q*q+6*q

theorem pumpCost_succ (b q : Nat) : pumpCost b (q+1) = (4*b+10)+pumpCost (b+2) q := by
  simp only [pumpCost,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]
  omega

theorem pump_many (b q : Nat) (L : List Bool) :
    run0 table (pumpCost b q) ⟨0,U (2*q)++L,rep V b++[true]⟩ =
    some ⟨0,L,rep V (b+2*q)++[true]⟩ := by
  induction q generalizing b with
  | zero => simp only [pumpCost,Nat.mul_zero,Nat.add_zero,U,rep,List.nil_append,run0]
  | succ q ih =>
    have h := join0 (pump_one b (U (2*q)++L)) (ih (b+2))
    rw [pumpCost_succ,show 2*(q+1)=2+2*q by omega,U_add,List.append_assoc,
      ← Nat.add_assoc b 2 (2*q)]
    exact h

theorem clean_first (L R : List Bool) :
    run0 table 3 ⟨0,false::true::L,true::R⟩ =
    some ⟨0,true::L,false::true::R⟩ := by rfl

theorem clean_turn (L R : List Bool) :
    run0 table 3 ⟨4,true::L,false::false::true::R⟩ =
    some ⟨0,V++L,true::true::R⟩ := by rfl

theorem clean_single (R : List Bool) :
    run0 table 2 ⟨0,[true],R⟩ = some ⟨0,[],V++R⟩ := by rfl

/-- Removes the remaining left alternating word, retaining the separator. -/
theorem clean_many (s : Nat) (R : List Bool) :
    run0 table (6*s+9) ⟨0,rep W (s+1)++[true],true::R⟩ =
    some ⟨0,[],rep V (s+1)++true::true::R⟩ := by
  have h := clean_first (rep W s++[true]) R
  have h' : run0 table 3 ⟨0,rep W (s+1)++[true],true::R⟩ =
      some ⟨0,rep V s++[true,true],false::true::R⟩ := by
    rw [show [true,true]=true::[true] by rfl,V_tail]
    simpa only [rep,W,List.cons_append,List.nil_append,List.append_assoc] using h
  have H := join0 h' (A_left_all s [true,true] (false::true::R))
  have K := join0 H (A_to_E [] (rep V s++false::true::R))
  have J := join0 K (E_scan s [] (false::true::R))
  have T := join0 J (by simpa only [List.append_nil] using clean_turn (rep V s) R)
  have F := join0 T (by simpa only [rep,List.append_nil] using A_left_all (s+1) [] (true::true::R))
  rw [show 6*s+9=3+2*s+1+2*s+3+2*(s+1) by omega]
  exact F

/-- Pure alternating tape. This intermediate configuration restarts the countdown. -/
def P (n : Nat) : Z0 := ⟨0,[],rep V n++[true]⟩
/-- Double-one separator; countdown p=m+1 is positive. -/
def D (m q : Nat) : Z0 := ⟨0,[],rep V (m+1)++true::rep V q++[true]⟩

theorem gather_pump (m q : Nat) :
    run0 table (9+2*(m+1)+4*q+10+20+pumpCost 3 q) (D m q) =
    some ⟨0,rep W m++[true],rep V (3+2*q)++[true]⟩ := by
  have h := gather_one m q
  have g := init_four (U (2*q)++rep W m++[true])
  rw [show 2*q+4=4+2*q by omega,U_add,List.append_assoc] at h
  have H := join0 h g
  have K := join0 H (by simpa only [List.append_assoc] using pump_many 3 q (rep W m++[true]))
  simpa only [D,List.append_assoc,List.cons_append] using K

def mainCost (m q : Nat) : Nat := 9+2*(m+1)+4*q+10+20+pumpCost 3 q

theorem count (s q : Nat) :
    run0 table (mainCost (s+1) q+(6*s+9)) (D (s+1) q) =
    some (D s (3+2*q)) := by
  have h := gather_pump (s+1) q
  have g := clean_many s (rep W (3+2*q))
  rw [← V_rotate] at g
  have K := join0 h g
  simpa only [D,mainCost,List.append_assoc,List.cons_append] using K

theorem finish (q : Nat) :
    run0 table (mainCost 0 q+2) (D 0 q) = some (P (4+2*q)) := by
  have h := gather_pump 0 q
  have H := join0 h (clean_single (rep V (3+2*q)++[true]))
  unfold P mainCost
  rw [show 4+2*q=3+2*q+1 by omega,rep,List.append_assoc]
  exact H

theorem pure_turn (L : List Bool) :
    run0 table 12 ⟨2,true::true::false::L,[]⟩ =
    some ⟨0,true::true::false::L,[false,false,false]⟩ := by rfl

theorem pure_start (n : Nat) :
    run0 table (5+2*(n+1)+12+6) (P (n+1)) =
    some ⟨0,rep W (n+1)++[true],rep V 2++[false]⟩ := by
  have h := scan (n+1) []
  have g := pure_turn (rep V n++[true,true])
  have H := join0 h (by simpa only [rep,V,List.cons_append,List.nil_append] using g)
  change run0 table (5+2*(n+1)+12) _ = some ⟨0,true::true::false::(rep V n++true::[true]),[false,false,false]⟩ at H
  rw [V_tail n [true]] at H
  have H' : run0 table (5+2*(n+1)+12) (P (n+1)) =
      some ⟨0,U 2++rep W (n+1)++[true],[false,false,false]⟩ := by
    simpa only [P,U,List.append_nil,rep,W,List.cons_append,List.nil_append,List.append_assoc] using H
  have g' : ∀ L : List Bool, run0 table 6 ⟨0,U 2++L,[false,false,false]⟩ =
      some ⟨0,L,rep V 2++[false]⟩ := by intro L; rfl
  exact join0 H' (g' (rep W (n+1)++[true]))

theorem restart (n : Nat) :
    run0 table (5+2*(n+2)+12+6+(6*(n+1)+9)+(9+2*(n+2)+8+6)+20+22+(6*n+9))
      (P (n+2)) = some (D n 5) := by
  have h := pure_start (n+1)
  have H := join0 h (clean_many (n+1) [false,true,false,false])
  have K := join0 H (by simpa only [List.append_assoc,List.cons_append,List.nil_append,show rep V 2 = [true,false,true,false] by rfl] using gather_zero (n+1))
  rw [show U 6=U 4++U 2 by rfl,List.append_assoc] at K
  have g := init_four (U 2++rep W (n+1)++[true])
  have J := join0 K g
  have T := join0 J (pump_one 3 (rep W (n+1)++[true]))
  have F := join0 T (clean_many n (rep W 5))
  rw [← V_rotate] at F
  simpa only [D,List.cons_append,List.append_assoc] using F

def next : Nat × Nat → Nat × Nat
  | (0,q) => (2+2*q,5)
  | (m+1,q) => (m,3+2*q)

def restartCost (n : Nat) : Nat :=
  5+2*(n+2)+12+6+(6*(n+1)+9)+(9+2*(n+2)+8+6)+20+22+(6*n+9)

def macroCost : Nat × Nat → Nat
  | (0,q) => mainCost 0 q+2+restartCost (2+2*q)
  | (m+1,q) => mainCost (m+1) q+(6*m+9)

theorem next_run (x : Nat × Nat) :
    run0 table (macroCost x) (D x.1 x.2) = some (D (next x).1 (next x).2) := by
  rcases x with ⟨m,q⟩
  cases m with
  | zero =>
    have h := finish q
    have g := restart (2+2*q)
    rw [show 2+2*q+2=4+2*q by omega] at g
    have H := join0 h g
    simpa only [macroCost,next,restartCost,show 2+2*q+2=4+2*q by omega] using H
  | succ m => exact count m q

def params : Nat → Nat × Nat
  | 0 => (0,5)
  | k+1 => next (params k)

def family (k : Nat) : Z0 := D (params k).1 (params k).2
def cost (k : Nat) : Nat := macroCost (params k)

theorem entry : run0 table 153 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  exact next_run (params k)

theorem positive (k : Nat) : 0 < cost k := by
  unfold cost
  rcases h : params k with ⟨m,q⟩
  cases m <;> simp only [macroCost,mainCost,restartCost] <;> omega

#print axioms count
#print axioms finish
#print axioms restart
#print axioms entry
#print axioms growth
#print axioms positive
end BB6.Agent7D100Countdown
