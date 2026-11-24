import Std
import Lean.Elab.Tactic.Omega

namespace BB6CountedZipper

@[local simp] theorem val0 : (0:Fin 6).val = 0 := rfl
@[local simp] theorem val1 : (1:Fin 6).val = 1 := rfl
@[local simp] theorem val2 : (2:Fin 6).val = 2 := rfl
@[local simp] theorem val3 : (3:Fin 6).val = 3 := rfl
@[local simp] theorem val4 : (4:Fin 6).val = 4 := rfl
@[local simp] theorem val5 : (5:Fin 6).val = 5 := rfl

structure Z where
  q : Fin 6
  h : Int
  l : List Bool
  r : List Bool
  deriving DecidableEq, Repr

def left (q : Fin 6) (h : Int) (l r : List Bool) : Z := ⟨q,h,l,r⟩
def right (q : Fin 6) (h : Int) (l r : List Bool) : Z :=
  ⟨q,h+1,r.headD false :: l,r.tail⟩
def ml (q : Fin 6) (w : Bool) (z : Z) : Z :=
  ⟨q,z.h-1,z.l.tail,w::z.r⟩
def mr (q : Fin 6) (w : Bool) (z : Z) : Z :=
  ⟨q,z.h+1,z.r.headD false::w::z.l.tail,z.r.tail⟩
def step (z : Z) : Option Z :=
  match z.q.val,z.l.headD false with
  | 0,false => some (mr 1 true z)
  | 0,true => none
  | 1,false => some (ml 2 true z)
  | 1,true => some (mr 5 false z)
  | 2,false => some (mr 4 true z)
  | 2,true => some (ml 3 false z)
  | 3,false => some (ml 2 false z)
  | 3,true => some (mr 1 true z)
  | 4,false => some (mr 0 true z)
  | 4,true => some (mr 4 true z)
  | 5,false => some (mr 4 true z)
  | 5,true => some (mr 3 false z)
  | _,_ => none

def run : Nat → Z → Option Z
  | 0,z => some z
  | n+1,z => (step z).bind (run n)

theorem run_add (n m : Nat) (z : Z) : run (n+m) z = (run n z).bind (run m) := by
  induction n generalizing z with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+m=n+m+1 by omega]
    simp only [run]
    cases step z with
    | none => rfl
    | some z' => exact ih z'

theorem join {n m : Nat} {x y z : Z} (h₁ : run n x = some y) (h₂ : run m y = some z) : run (n+m) x = some z := by
  rw [run_add,h₁]; exact h₂

def shift (t : Int) (z : Z) : Z := { z with h := z.h+t }

theorem step_shift (t : Int) (z : Z) : step (shift t z) = (step z).map (shift t) := by
  unfold step
  change (match z.q.val,z.l.headD false with
    | 0,false => some (mr 1 true (shift t z))
    | 0,true => none
    | 1,false => some (ml 2 true (shift t z))
    | 1,true => some (mr 5 false (shift t z))
    | 2,false => some (mr 4 true (shift t z))
    | 2,true => some (ml 3 false (shift t z))
    | 3,false => some (ml 2 false (shift t z))
    | 3,true => some (mr 1 true (shift t z))
    | 4,false => some (mr 0 true (shift t z))
    | 4,true => some (mr 4 true (shift t z))
    | 5,false => some (mr 4 true (shift t z))
    | 5,true => some (mr 3 false (shift t z))
    | _,_ => none) = _
  split <;> simp [shift,ml,mr] <;> omega

theorem run_shift (t : Int) (n : Nat) (z : Z) :
    run n (shift t z) = (run n z).map (shift t) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [run,step_shift]
    cases step z with
    | none => rfl
    | some z' => exact ih z'

def ones (n : Nat) : List Bool := List.replicate n true
def d0 : List Bool := [false,false,true]
def d1 : List Bool := [true,true,true]
def zeros3 : Nat → List Bool
  | 0 => []
  | n+1 => d0 ++ zeros3 n

def marker (m : Nat) : List Bool :=
  if m%3=0 then [false,true] else if m%3=1 then [true,false,true] else [true,true,false,true]

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega]
    simp only [ones,List.replicate_succ,List.cons_append] at ih ⊢
    exact congrArg (List.cons true) ih

theorem ones_succ (n : Nat) : ones (n+1) = true::ones n := rfl

theorem ones_snoc (n : Nat) : ones n ++ [true] = true :: ones n := by
  change ones n ++ ones 1 = _
  rw [← ones_add n 1, ones_succ]

-- The D/B/C left sweep transfers each one across a moving zero separator.
theorem dSweep_one (h : Int) (l r : List Bool) :
    run 3 (left 3 h (true::l) (false::r)) = some (left 3 (h-1) l (false::true::r)) := by
  simp [run,step,ml,mr,left] <;> omega

theorem dSweep (n : Nat) (h : Int) (l r : List Bool) :
    run (3*n) (left 3 h (ones n ++ l) (false::r)) =
    some (left 3 (h-(n:Int)) l (false::(ones n ++ r))) := by
  induction n generalizing h r with
  | zero => simp [ones,run]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega, ones_succ]
    have hp := dSweep_one h (ones n ++ l) r
    have hh := join hp (ih (h-1) (true::r))
    rw [show h-1-(n:Int)=h-((n+1:Nat):Int) by omega] at hh
    have ha : ones n ++ true::r = true::(ones n ++ r) := by
      rw [← List.singleton_append, ← List.append_assoc, ones_snoc]; rfl
    rw [ha] at hh
    exact hh

-- B/F/D right sweep turns each 111 block into physical 001.
theorem bSweep_one (h : Int) (l r : List Bool) :
    run 3 (right 1 h l (true::true::true::r)) =
    some (right 1 (h+3) (true::false::false::l) r) := by
  simp [run,step,ml,mr,right] <;> omega

def rev0 : Nat → List Bool
  | 0 => []
  | n+1 => [true,false,false] ++ rev0 n

theorem rev0_snoc (n : Nat) : rev0 n ++ [true,false,false] = [true,false,false] ++ rev0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rev0,List.append_assoc]; rw [ih]

theorem bSweep (n : Nat) (h : Int) (l r : List Bool) :
    run (3*n) (right 1 h l (ones (3*n) ++ r)) =
    some (right 1 (h+3*(n:Int)) (rev0 n ++ l) r) := by
  induction n generalizing h l with
  | zero => simp [ones,rev0,run]
  | succ n ih =>
    have ho : ones (3*(n+1)) = [true,true,true] ++ ones (3*n) := by
      rw [show 3*(n+1)=3+3*n by omega,ones_add];rfl
    rw [ho,List.append_assoc,show 3*(n+1)=3+3*n by omega]
    have hh := join (bSweep_one h l (ones (3*n) ++ r)) (ih (h+3) (true::false::false::l))
    rw [show h+3+3*(n:Int)=h+3*((n+1:Nat):Int) by omega] at hh
    have ha : rev0 n ++ [true,false,false] ++ l = rev0 (n+1) ++ l := by
      rw [rev0_snoc]; rfl
    have hh2 : rev0 n ++ true::false::false::l = rev0 (n+1) ++ l := by simpa only [List.append_assoc,List.cons_append,List.nil_append] using ha
    rw [hh2] at hh
    simpa only [List.cons_append,List.nil_append] using hh

theorem rev0_one (n : Nat) : rev0 n ++ [true] = true :: zeros3 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rev0,zeros3,List.append_assoc,ih,d0]
    rfl

-- The four-step center of the outer binary carry.
theorem lc_core (h : Int) (l r : List Bool) :
    run 4 (left 3 h (d0 ++ l) (false::r)) =
    some (right 1 (h+1) (true::(d1 ++ l)) r) := by
  simp [d0,d1,run,step,ml,mr,left,right] <;> omega

-- Generic outer LC decrement, independent of both exterior streams.
theorem lc_carry (v : Nat) (h : Int) (l r : List Bool) :
    run (4+12*v) (left 3 h (ones (3*v) ++ d0 ++ l) (false::r)) =
    some (right 1 (h+1) (true::(zeros3 v ++ d1 ++ l)) r) := by
  have h₁ := dSweep (3*v) h (d0++l) r
  have h₂ := lc_core (h-((3*v:Nat):Int)) l (ones (3*v)++r)
  have h₃ := bSweep v (h-((3*v:Nat):Int)+1) (true::(d1++l)) r
  have hj := join (join h₁ h₂) h₃
  have ht : 3*(3*v)+4+3*v = 4+12*v := by omega
  rw [ht,show h-((3*v:Nat):Int)+1+3*(v:Int)=h+1 by omega] at hj
  have ha : rev0 v ++ true::(d1++l) = true::(zeros3 v ++ d1 ++ l) := by
    rw [← List.singleton_append,← List.append_assoc,rev0_one] <;> simp [List.append_assoc]
  simpa only [List.append_assoc,ha] using hj

-- After the initial unary left sweep, the three marker cases take 17,20,23 steps.
theorem marker_pre (m : Nat) (hm : m<3) (h : Int) (l r : List Bool) :
    run (17+3*m) (left 3 h (marker m ++ d0 ++ l) (false::r)) =
      some (left 3 (h-(5+(m:Int))) l
        ([false,true,true,true,true,false] ++ ones m ++ r)) := by
  have hc : m=0 ∨ m=1 ∨ m=2 := by omega
  have hf : run (17+3*m) (left 3 0 (marker m ++ d0 ++ l) (false::r)) =
      some (left 3 (-(5+(m:Int))) l ([false,true,true,true,true,false] ++ ones m ++ r)) := by
    rcases hc with rfl|rfl|rfl <;> rfl
  have hs := run_shift h (17+3*m) (left 3 0 (marker m ++ d0 ++ l) (false::r))
  rw [hf] at hs
  simpa [shift,left,Int.sub_eq_add_neg,Int.add_comm] using hs

-- Exact Rst prelude: all a and arbitrary outer counter tail.
theorem reset_pre (m a : Nat) (hm : m<3) (h : Int) (l r : List Bool) :
    run (17+9*a+3*m)
      (left 3 h (ones (3*a) ++ marker m ++ d0 ++ l) (false::r)) =
    some (left 3 (h-(3*(a:Int)+5+(m:Int))) l
      ([false,true,true,true,true,false] ++ ones (3*a+m) ++ r)) := by
  have hp := dSweep (3*a) h (marker m ++ d0 ++ l) r
  have hq := marker_pre m hm (h-((3*a:Nat):Int)) l (ones (3*a)++r)
  have hj := join hp hq
  rw [show 3*(3*a)+(17+3*m)=17+9*a+3*m by omega,
      show h-((3*a:Nat):Int)-(5+(m:Int))=h-(3*(a:Int)+5+(m:Int)) by omega] at hj
  have ho : ones m ++ ones (3*a) = ones (3*a+m) := by rw [← ones_add]; congr 1; omega
  simpa only [List.append_assoc, ← ho] using hj

-- E moves right on every one.
theorem eSweep (n : Nat) (h : Int) (l r : List Bool) :
    run n (right 4 h l (ones n ++ r)) =
      some (right 4 (h+(n:Int)) (ones n ++ l) r) := by
  induction n generalizing h l with
  | zero => simp [ones,run]
  | succ n ih =>
    rw [ones_succ]
    have hp : run 1 (right 4 h l (true::(ones n++r))) =
        some (right 4 (h+1) (true::l) (ones n++r)) := by
      simp [run,step,mr,right]
    have hh := join hp (ih (h+1) (true::l))
    rw [show 1+n=n+1 by omega,show h+1+(n:Int)=h+((n+1:Nat):Int) by omega] at hh
    have ha : ones n ++ true::l = true::(ones n ++ l) := by
      rw [← List.singleton_append,← List.append_assoc,ones_snoc];rfl
    simpa only [List.cons_append,ha] using hh

-- Postlude, first five instructions and two-zero crossing around E sweep.
theorem post_five (h : Int) (l r : List Bool) :
    run 5 (right 1 h (true::l) ([true,true,true,true,false]++r)) =
      some (right 4 (h+5) ([true,false,true,false,false,true]++l) r) := by
  simp [run,step,mr,ml,right] <;> omega

theorem post_two (h : Int) (l r : List Bool) :
    run 2 (right 4 h l (false::false::r)) =
      some (right 1 (h+2) (true::true::l) r) := by
  simp [run,step,mr,ml,right] <;> omega

-- Final fixed 29 instructions; arbitrary left exterior.
theorem post_last (h : Int) (l : List Bool) :
    run 29 (right 1 h ([true,false,false,true]++l) []) =
      some (left 3 (h-4) l [false,true,true,true,false,false,true,true,true]) := by
  have hf : run 29 (right 1 0 ([true,false,false,true]++l) []) =
      some (left 3 (-4) l [false,true,true,true,false,false,true,true,true]) := by rfl
  have hs := run_shift h 29 (right 1 0 ([true,false,false,true]++l) [])
  rw [hf] at hs
  simpa [shift,right,left,Int.sub_eq_add_neg,Int.add_comm] using hs


-- General postlude. N counts the ones between the two short bridges.
theorem post_generic (N b : Nat) (h : Int) (l : List Bool) :
    run (39+N+3*b)
      (right 1 h (true::l) ([true,true,true,true,false] ++ ones N ++ [false,false] ++ ones (3*(b+1)))) =
    some (left 3 (h+6+(N:Int)+3*(b:Int))
      (zeros3 b ++ ones (N+2) ++ [false,true,false,false,true] ++ l)
      [false,true,true,true,false,false,true,true,true]) := by
  let L := [true,false,true,false,false,true] ++ l
  let R := [false,false] ++ ones (3*(b+1))
  have h₁ := post_five h l (ones N ++ R)
  have h₂ := eSweep N (h+5) L R
  have h₃ := post_two (h+5+(N:Int)) (ones N ++ L) (ones (3*(b+1)))
  have h₄ := bSweep (b+1) (h+5+(N:Int)+2) (true::true::(ones N ++ L)) []
  simp only [List.append_nil] at h₄
  have hj := join (join (join h₁ h₂) h₃) h₄
  have hl : rev0 (b+1) ++ true::true::(ones N ++ L) =
      [true,false,false,true] ++ (zeros3 b ++ ones (N+2) ++ [false,true,false,false,true] ++ l) := by
    have ho : ones N ++ true::([false,true,false,false,true]++l) =
        true::(ones N ++ ([false,true,false,false,true]++l)) := by
      rw [← List.singleton_append,← List.append_assoc,ones_snoc]; rfl
    have he : true::true::(ones N ++ L) = true::(ones (N+2) ++ [false,true,false,false,true] ++ l) := by
      dsimp [L]
      rw [show N+2=N+1+1 by omega,ones_succ,ones_succ]
      simpa only [List.cons_append,List.nil_append,List.append_assoc] using
        congrArg (fun x => true::true::x) ho
    have hr (X : List Bool) : rev0 b ++ true::X = true::(zeros3 b ++ X) := by
      rw [← List.singleton_append,← List.append_assoc,rev0_one]; rfl
    rw [he,rev0,List.append_assoc,hr]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  rw [hl] at hj
  have h₅ := post_last (h+5+(N:Int)+2+3*((b+1:Nat):Int))
      (zeros3 b ++ ones (N+2) ++ [false,true,false,false,true] ++ l)
  have hf := join hj h₅
  rw [show ((5+N)+2)+3*(b+1)+29=39+N+3*b by omega,
      show h+5+(N:Int)+2+3*((b+1:Nat):Int)-4=h+6+(N:Int)+3*(b:Int) by omega] at hf
  simpa only [R,List.append_assoc] using hf

theorem marker_out (m a : Nat) (hm : m<3) :
    ones (3*a+5+m) ++ [false,true] =
      ones (3*(a+(if m=0 then 1 else 2))) ++ marker ((m+2)%3) := by
  have hc : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hc with rfl|rfl|rfl
  · change ones (3*a+5+0) ++ [false,true] = ones (3*(a+1)) ++ [true,true,false,true]
    rw [show 3*a+5+0=3*(a+1)+2 by omega,ones_add]; simp [ones,List.append_assoc]
  · change ones (3*a+5+1) ++ [false,true] = ones (3*(a+2)) ++ [false,true]
    rw [show 3*a+5+1=3*(a+2) by omega]
  · change ones (3*a+5+2) ++ [false,true] = ones (3*(a+2)) ++ [true,false,true]
    rw [show 3*a+5+2=3*(a+2)+1 by omega,ones_add]; simp [ones,List.append_assoc]


def rc (b : Nat) : List Bool := [false,true,true,true,false,false] ++ ones (3*(b+1))
def nextA (m a b : Nat) := a+b+(if m=0 then 1 else 2)
def nextM (m : Nat) := (m+2)%3

-- One source-faithful reset-prefix theorem covers all three markers, all
-- positive outer counters (expressed by their carry pattern), and all a,b.
theorem reset_prefix (m a v b : Nat) (hm : m<3) (h : Int) (l : List Bool) :
    run (63+4*m+12*(a+v)+3*b)
      (left 3 h (ones (3*a) ++ marker m ++ d0 ++ ones (3*v) ++ d0 ++ l) (rc b)) =
    some (left 3 (h+5+3*(b:Int))
      (zeros3 b ++ ones (3*(a+(if m=0 then 1 else 2))) ++ marker (nextM m) ++ d0 ++ zeros3 v ++ d1 ++ l)
      (rc 0)) := by
  let hc := h-(3*(a:Int)+5+(m:Int))
  let R := [true,true,true] ++ [false,false] ++ ones (3*(b+1))
  let L := ones (3*v) ++ d0 ++ l
  have hp := reset_pre m a hm h L R
  let R' := [true,true,true,true,false] ++ ones (3*a+m+3) ++ [false,false] ++ ones (3*(b+1))
  have hpre : run (17+9*a+3*m)
      (left 3 h (ones (3*a) ++ marker m ++ d0 ++ L) (rc b)) =
      some (left 3 hc L (false::R')) := by
    have he : ones (3*a+m+3) = ones (3*a+m) ++ [true,true,true] := by rw [ones_add]; rfl
    simpa only [rc,R',R,hc,he,List.append_assoc,List.cons_append,List.nil_append] using hp
  have hcarry := lc_carry v hc l R'
  have hpost := post_generic (3*a+m+3) b (hc+1) (zeros3 v ++ d1 ++ l)
  have hh := join (join hpre hcarry) hpost
  have hn : 17+9*a+3*m+(4+12*v)+(39+(3*a+m+3)+3*b) = 63+4*m+12*(a+v)+3*b := by omega
  have hhead : hc+1+6+((3*a+m+3:Nat):Int)+3*(b:Int)=h+5+3*(b:Int) := by dsimp [hc]; omega
  rw [hn,hhead,show 3*a+m+3+2=3*a+5+m by omega] at hh
  have hout := marker_out m a hm
  have he : ones (3*a+5+m) ++ [false,true,false,false,true] =
      ones (3*(a+(if m=0 then 1 else 2))) ++ marker (nextM m) ++ d0 := by
    change ones (3*a+5+m) ++ ([false,true]++d0) = _
    rw [← List.append_assoc,hout]; rfl
  have he' : zeros3 b ++ ones (3*a+5+m) ++ [false,true,false,false,true] ++ (zeros3 v ++ d1 ++ l) =
      zeros3 b ++ (ones (3*a+5+m) ++ [false,true,false,false,true]) ++ (zeros3 v ++ d1 ++ l) := by simp only [List.append_assoc]
  rw [he',he] at hh
  simpa only [List.append_assoc,L,show rc 0 = [false,true,true,true,false,false,true,true,true] by rfl] using hh


-- Inner-counter Inc0 after the generic carry. The same arbitrary-tail
-- sweeps discharge the complete suffix without valuation case splits.
theorem inc_pre (h : Int) (l r : List Bool) :
    run 11 (right 1 h (true::l) ([true,true,true,false,false]++r)) =
    some (right 4 (h+5) ([true,false,true,true,true,true]++l) r) := by
  have hf : run 11 (right 1 0 (true::l) ([true,true,true,false,false]++r)) =
      some (right 4 5 ([true,false,true,true,true,true]++l) r) := by rfl
  have hs := run_shift h 11 (right 1 0 (true::l) ([true,true,true,false,false]++r))
  rw [hf] at hs
  simpa [shift,right,Int.add_comm,Int.add_left_comm,Int.add_assoc] using hs

theorem inc_turn (h : Int) (l : List Bool) :
    run 4 (right 4 h l []) = some (left 3 (h+1) (true::l) [false,true]) := by
  simp [run,step,ml,mr,right,left] <;> omega

theorem inc_bridge (h : Int) (l r : List Bool) :
    run 2 (left 3 h (false::true::l) r) =
      some (left 3 (h-2) l (false::false::r)) := by
  simp [run,step,ml,mr,left] <;> omega

theorem inc_post (b : Nat) (h : Int) (l : List Bool) :
    run (44+12*b) (right 1 h (true::l) ([true,true,true,false,false]++ones (3*(b+1)))) =
    some (left 3 (h-1) l (rc (b+1))) := by
  let N := 3*(b+1)
  let L := [true,false,true,true,true,true]++l
  have h₁ := inc_pre h l (ones N)
  have h₂ := eSweep N (h+5) L []
  simp only [List.append_nil] at h₂
  have h₃ := inc_turn (h+5+(N:Int)) (ones N++L)
  have hj := join (join h₁ h₂) h₃
  have he : true::(ones N++L) = ones (N+2) ++ [false,true,true,true,true] ++ l := by
    dsimp [L]
    rw [show N+2=N+1+1 by omega,ones_succ,ones_succ]
    have hp : ones N ++ true::([false,true,true,true,true]++l) =
        true::(ones N ++ ([false,true,true,true,true]++l)) := by
      rw [← List.singleton_append,← List.append_assoc,ones_snoc];rfl
    simpa only [List.cons_append,List.append_assoc,List.nil_append] using congrArg (List.cons true) hp
  rw [he] at hj
  have h₄ := dSweep (N+2) (h+5+(N:Int)+1) ([false,true,true,true,true]++l) [true]
  have h₄' : run (3*(N+2)) (left 3 (h+5+(N:Int)+1)
      (ones (N+2) ++ [false,true,true,true,true] ++ l) [false,true]) =
      some (left 3 (h+4) ([false,true,true,true,true]++l) (false::ones (N+3))) := by
    rw [show h+5+(N:Int)+1-((N+2:Nat):Int)=h+4 by omega] at h₄
    have ho : ones (N+3) = ones (N+2) ++ [true] := by
      rw [show N+3=N+2+1 by omega,ones_add]; rfl
    simpa only [List.append_assoc,ho] using h₄
  have h₅ := inc_bridge (h+4) ([true,true,true]++l) (false::ones (N+3))
  have h₆ := dSweep 3 (h+4-2) l (false::false::ones (N+3))
  have h₅' : run 2 (left 3 (h+4) ([false,true,true,true,true]++l) (false::ones (N+3))) =
      some (left 3 (h+4-2) (ones 3++l) (false::false::false::ones (N+3))) := h₅
  have hf := join (join (join hj h₄') h₅') h₆
  have hn : 11+N+4+3*(N+2)+2+3*3=44+12*b := by dsimp [N];omega
  have hr : false::(ones 3++false::false::ones (N+3)) = rc (b+1) := by
    have hx : N+3=3*(b+1+1) := by dsimp [N];omega
    rw [hx];rfl
  rw [hn,show h+4-2-((3:Nat):Int)=h-1 by omega,hr] at hf
  exact hf

theorem inc0_carry (v b : Nat) (h : Int) (l : List Bool) :
    run (48+12*v+12*b)
      (left 3 h (ones (3*v) ++ d0 ++ l) (rc b)) =
    some (left 3 h (zeros3 v ++ d1 ++ l) (rc (b+1))) := by
  have h₁ := lc_carry v h l ([true,true,true,false,false]++ones (3*(b+1)))
  have h₂ := inc_post b (h+1) (zeros3 v++d1++l)
  have hf := join h₁ h₂
  rw [show 4+12*v+(44+12*b)=48+12*v+12*b by omega,show h+1-1=h by omega] at hf
  exact hf


def lh : List Bool := [true,true,false,true,true,true]
def lh' : List Bool := [true,true,true,false,true,true,true]

-- Fixed left-history rewrite, including the two genuinely blank cells.
theorem sentinel (h : Int) (r : List Bool) :
    run 18 (left 3 h [false,true,true,true] (false::r)) =
      some (right 1 (h+1) lh' r) := by
  have hf : run 18 (left 3 0 [false,true,true,true] (false::r)) =
      some (right 1 1 lh' r) := by rfl
  have hs := run_shift h 18 (left 3 0 [false,true,true,true] (false::r))
  rw [hf] at hs
  simp [shift,right,left,Int.add_comm,Int.add_left_comm] at hs ⊢
  exact hs

theorem zero_bridge (h : Int) (l r : List Bool) :
    run 6 (right 1 h ([true,false,false]++l) (false::r)) =
      some (right 1 h ([true,true,true]++l) (true::r)) := by
  simp [run,step,ml,mr,right] <;> omega

theorem two_bridge (h : Int) (l r : List Bool) :
    run 6 (right 1 h l ([true,true,false,false]++r)) =
      some (right 1 (h+4) ([true,true,true,false]++l) r) := by
  simp [run,step,ml,mr,right] <;> omega

theorem halt_bridge (h : Int) (l r : List Bool) :
    run 3 (right 1 h l ([true,false,false]++r)) =
      some (right 0 (h+3) ([true,true,false]++l) r) := by
  simp [run,step,ml,mr,right] <;> omega

-- Shared zero-outer-counter prefix, up to the last (m=0/1) fork.
theorem zero_outer (m L a b : Nat) (hm : m<3) (h : Int) :
    run (56+3*m+12*(L+a))
      (left 3 h (ones (3*a) ++ marker m ++ d0 ++ ones (3*L) ++ lh) (rc b)) =
    some (right 1 (h+3-(m:Int))
      (rev0 (a+1) ++ d1 ++ rev0 (L+1) ++ lh')
      (ones (m+1) ++ [false,false] ++ ones (3*(b+1)))) := by
  -- All markers share the prefix through the final B sweep; m+1 ones remain.
  let hc := h-(3*(a:Int)+5+(m:Int))
  let hx := hc-((3*L+2:Nat):Int)
  let R := [false,false] ++ ones (3*(b+1))
  let U := ones (3*a+m+3) ++ R
  let W := ones (3*(L+2)) ++ false::U
  have hp := reset_pre m a hm h (ones (3*L)++lh) ([true,true,true]++R)
  have hp' : run (17+9*a+3*m)
      (left 3 h (ones (3*a) ++ marker m ++ d0 ++ ones (3*L) ++ lh) (rc b)) =
      some (left 3 hc (ones (3*L)++lh) ([false,true,true,true,true,false]++U)) := by
    have he : ones (3*a+m+3)=ones (3*a+m)++[true,true,true] := by rw [ones_add];rfl
    simpa only [hc,rc,R,U,he,List.append_assoc,List.cons_append,List.nil_append] using hp
  have he : ones (3*L) ++ lh = ones (3*L+2) ++ [false,true,true,true] := by
    rw [ones_add,List.append_assoc]; rfl
  rw [he] at hp'
  have hd := dSweep (3*L+2) hc [false,true,true,true] ([true,true,true,true,false]++U)
  have hd' : run (3*(3*L+2)) (left 3 hc (ones (3*L+2)++[false,true,true,true])
        ([false,true,true,true,true,false]++U)) =
      some (left 3 hx [false,true,true,true] (false::W)) := by
    have ho : ones (3*(L+2))=ones (3*L+2)++[true,true,true,true] := by
      rw [show 3*(L+2)=3*L+2+4 by omega,ones_add];rfl
    simpa only [hx,W,ho,List.append_assoc,List.cons_append,List.nil_append] using hd
  have hs := sentinel hx W
  have hb := bSweep (L+2) (hx+1) lh' (false::U)
  have hj := join (join (join hp' hd') hs) hb
  have hz := zero_bridge (hx+1+3*((L+2:Nat):Int)) (rev0 (L+1)++lh') U
  have ha : rev0 (L+2)++lh' = [true,false,false]++(rev0 (L+1)++lh') := by simp [rev0]
  rw [ha] at hj
  have hj' := join hj hz
  have hU : true::U = ones (3*(a+1))++(ones (m+1)++R) := by
    change true::(ones (3*a+m+3)++R) = _
    rw [← List.append_assoc (ones (3*(a+1))) (ones (m+1)) R,← ones_add,show 3*(a+1)+(m+1)=3*a+m+3+1 by omega,ones_succ]
    rfl
  rw [hU] at hj'
  have ha' := bSweep (a+1) (hx+1+3*((L+2:Nat):Int))
      (d1++(rev0 (L+1)++lh')) (ones (m+1)++R)
  have hf := join hj' ha'
  -- The general prefix has 3m extra steps, and the marker remainder is m+1.
  rw [show 17+9*a+3*m+3*(3*L+2)+18+3*(L+2)+6+3*(a+1)=56+3*m+12*(L+a) by omega] at hf
  have hhead : hx+1+3*((L+2:Nat):Int)+3*((a+1:Nat):Int)=h+3-(m:Int) := by dsimp [hx,hc];omega
  rw [hhead] at hf
  simpa only [R,List.append_assoc] using hf


-- The final m=0 zero-counter branch halts after the exact successful count.
theorem terminal (L a b : Nat) (h : Int) :
    ∃ z, run (59+12*(L+a))
      (left 3 h (ones (3*a) ++ marker 0 ++ d0 ++ ones (3*L) ++ lh) (rc b)) = some z ∧ step z = none := by
  let l := rev0 (a+1) ++ d1 ++ rev0 (L+1) ++ lh'
  have h₁ := zero_outer 0 L a b (by decide) h
  have h₂ := halt_bridge (h+3) l (ones (3*(b+1)))
  rw [show h+3-((0:Nat):Int)=h+3 by omega] at h₁
  have hh := join h₁ h₂
  have hn : 56+3*0+12*(L+a)+3=59+12*(L+a) := by omega
  rw [hn] at hh
  refine ⟨_,hh,?_⟩
  have ho : ones (3*(b+1)) = true::ones (3*b+2) := by
    rw [show 3*(b+1)=3*b+2+1 by omega,ones_succ]
  simp [ho,step,right]

-- Rst1' zero-outer reset: the expanded outer counter is represented by
-- d0^a d1 d0^(L+1), and the inner counter by d0^b. The exact left
-- history is restored. This is the same general macro for either cycle.
theorem reset_prime_prefix (L a b : Nat) (h : Int) :
    run (97+12*(L+a)+3*b)
      (left 3 h (ones (3*a) ++ marker 1 ++ d0 ++ ones (3*L) ++ lh) (rc b)) =
    some (left 3 (h+5+3*(b:Int))
      (zeros3 b ++ marker 2 ++ d0 ++ zeros3 a ++ d1 ++ zeros3 (L+1) ++ lh) (rc 0)) := by
  let l := rev0 (a+1) ++ d1 ++ rev0 (L+1) ++ lh'
  have h₁ := zero_outer 1 L a b (by decide) h
  have h₂ := two_bridge (h+2) l (ones (3*(b+1)))
  have h₁' : run (59+12*(L+a))
      (left 3 h (ones (3*a) ++ marker 1 ++ d0 ++ ones (3*L) ++ lh) (rc b)) =
      some (right 1 (h+2) l ([true,true,false,false]++ones (3*(b+1)))) := by
    simpa only [l,show h+3-(1:Nat)=h+2 by omega,show 56+3*1=59 by decide,show ones (1+1)=[true,true] by rfl,List.cons_append,List.nil_append] using h₁
  have h₃ := bSweep (b+1) (h+2+4) ([true,true,true,false]++l) []
  simp only [List.append_nil] at h₃
  have hj := join (join h₁' h₂) h₃
  have hr (n : Nat) (r : List Bool) : rev0 n ++ true::r = true::(zeros3 n++r) := by
    rw [← List.singleton_append,← List.append_assoc,rev0_one]; rfl
  have hl : rev0 (b+1) ++ ([true,true,true,false]++l) =
      [true,false,false,true] ++ (zeros3 b ++ marker 2 ++ d0 ++ zeros3 a ++ d1 ++ zeros3 (L+1) ++ lh) := by
    change ([true,false,false]++rev0 b) ++ true::true::true::false::l = _
    rw [List.append_assoc,hr]
    dsimp [l]
    have hh : d1 ++ rev0 (L+1) ++ lh' = d1 ++ true::(zeros3 (L+1)++lh) := by
      rw [List.append_assoc]
      change d1 ++ (rev0 (L+1) ++ true::lh) = _
      rw [hr]
    simp only [List.append_assoc] at hh ⊢
    rw [hh]
    have hh' : rev0 (a+1) ++ (d1 ++ true::(zeros3 (L+1)++lh)) =
        true::(zeros3 (a+1) ++ d1 ++ zeros3 (L+1) ++ lh) := by
      change rev0 (a+1) ++ true::([true,true,true]++(zeros3 (L+1)++lh)) = _
      rw [hr]; simp [d1,List.append_assoc]
    rw [hh']
    simp [marker,zeros3,List.append_assoc,d0,d1]
  rw [hl] at hj
  have h₄ := post_last (h+2+4+3*((b+1:Nat):Int))
      (zeros3 b ++ marker 2 ++ d0 ++ zeros3 a ++ d1 ++ zeros3 (L+1) ++ lh)
  have hf := join hj h₄
  rw [show 59+12*(L+a)+6+3*(b+1)+29=97+12*(L+a)+3*b by omega,
      show h+2+4+3*((b+1:Nat):Int)-4=h+5+3*(b:Int) by omega] at hf
  simpa only [show rc 0=[false,true,true,true,false,false,true,true,true] by rfl] using hf

#print axioms lc_carry
#print axioms reset_prefix
#print axioms inc0_carry
#print axioms terminal
#print axioms reset_prime_prefix
end BB6CountedZipper
