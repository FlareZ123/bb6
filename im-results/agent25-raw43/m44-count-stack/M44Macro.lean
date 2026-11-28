import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25M44
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def bitsEq (a b : List Bool) : Prop := ∀ i, a.getD i false = b.getD i false

theorem bitsEq_refl (a : List Bool) : bitsEq a a := fun _ => rfl

theorem bitsEq_symm {a b : List Bool} (h : bitsEq a b) : bitsEq b a := fun i => (h i).symm

theorem bitsEq_trans {a b c : List Bool} (h : bitsEq a b) (g : bitsEq b c) : bitsEq a c := fun i => (h i).trans (g i)

theorem bitsEq_cons {a b : List Bool} (h : bitsEq a b) (v : Bool) : bitsEq (v::a) (v::b) := by
  intro i; cases i with
  | zero => rfl
  | succ i => exact h i

theorem bitsEq_append (p : List Bool) {a b : List Bool} (h : bitsEq a b) : bitsEq (p++a) (p++b) := by
  induction p with
  | nil => exact h
  | cons v p ih => exact bitsEq_cons ih v

theorem bitsEq_head {a b : List Bool} (h : bitsEq a b) : a.headD false = b.headD false := by
  have H := h 0
  cases a <;> cases b <;> exact H

theorem bitsEq_tail {a b : List Bool} (h : bitsEq a b) : bitsEq a.tail b.tail := by
  intro i
  have H := h (i+1)
  cases a <;> cases b <;> exact H

def zEq (a b : Z0) : Prop := a.q=b.q ∧ bitsEq a.l b.l ∧ bitsEq a.r b.r

theorem zEq_refl (a : Z0) : zEq a a := ⟨rfl,bitsEq_refl _,bitsEq_refl _⟩
theorem zEq_symm {a b : Z0} (h : zEq a b) : zEq b a := ⟨h.1.symm,bitsEq_symm h.2.1,bitsEq_symm h.2.2⟩
theorem zEq_trans {a b c : Z0} (h : zEq a b) (g : zEq b c) : zEq a c := ⟨h.1.trans g.1,bitsEq_trans h.2.1 g.2.1,bitsEq_trans h.2.2 g.2.2⟩

theorem move_equiv (mv : Move) {a b : Z0} (h : zEq a b) : zEq (move0 mv a) (move0 mv b) := by
  cases hr : mv.right
  · simp only [move0,hr,Bool.false_eq_true,ite_false]
    exact ⟨rfl,bitsEq_tail h.2.1,bitsEq_cons h.2.2 _⟩
  · simp only [move0,hr,ite_true]
    refine ⟨rfl,?_,bitsEq_tail h.2.2⟩
    rw [bitsEq_head h.2.2]
    exact bitsEq_cons (bitsEq_cons (bitsEq_tail h.2.1) _) _

theorem step_equiv (p : PartialMachine) {a b c : Z0} (h : zEq a b)
    (hr : step0 p a = some c) : ∃ d, step0 p b = some d ∧ zEq c d := by
  unfold step0 at hr ⊢
  rw [← h.1,← bitsEq_head h.2.1]
  cases hm : (p (a.q,a.l.headD false)).bind id with
  | none => rw [hm] at hr; contradiction
  | some mv =>
    simp only [hm,Option.map_some,Option.some.injEq] at hr
    subst c
    exact ⟨move0 mv b,rfl,move_equiv mv h⟩

theorem run_equiv (p : PartialMachine) (n : Nat) {a b c : Z0} (h : zEq a b)
    (hr : run0 p n a = some c) : ∃ d, run0 p n b = some d ∧ zEq c d := by
  induction n generalizing a b c with
  | zero =>
    have he : a = c := Option.some.inj hr
    subst c
    exact ⟨b,rfl,h⟩
  | succ n ih =>
    simp only [run0] at hr ⊢
    cases hs : step0 p a with
    | none => simp [hs] at hr
    | some u =>
      have hu : run0 p n u = some c := by simpa [hs] using hr
      obtain ⟨v,hv,he⟩ := step_equiv p h hs
      obtain ⟨d,hd,he'⟩ := ih he hu
      exact ⟨d,by simp [hv,hd],he'⟩

def runs (n : Nat) (a b : Z0) : Prop := ∃ c, run0 table n a = some c ∧ zEq c b

theorem runs_exact {n : Nat} {a b : Z0} (h : run0 table n a = some b) : runs n a b := ⟨b,h,zEq_refl _⟩

theorem runs_transport {n : Nat} {a b a' b' : Z0} (h : runs n a b) (ha : zEq a a') (hb : zEq b b') : runs n a' b' := by
  obtain ⟨c,hc,he⟩ := h
  obtain ⟨d,hd,he'⟩ := run_equiv table n ha hc
  exact ⟨d,hd,zEq_trans (zEq_symm he') (zEq_trans he hb)⟩

theorem runs_join {n k : Nat} {a b c : Z0} (h : runs n a b) (g : runs k b c) : runs (n+k) a c := by
  obtain ⟨a',ha',he⟩ := h
  obtain ⟨b',hb',he'⟩ := runs_transport g (zEq_symm he) (zEq_refl c)
  exact ⟨b',join0 ha' hb',he'⟩

def ones (n : Nat) := List.replicate n true
def zeros (n : Nat) := List.replicate n false

theorem zeros_eq_nil (n : Nat) : bitsEq (zeros n) [] := by
  induction n with
  | zero => exact bitsEq_refl _
  | succ n ih =>
    intro i; cases i with
    | zero => rfl
    | succ i => exact ih i

theorem ones_add (a b : Nat) : ones (a+b)=ones a++ones b := by unfold ones; rw [List.replicate_append_replicate]
theorem zeros_add (a b : Nat) : zeros (a+b)=zeros a++zeros b := by unfold zeros; rw [List.replicate_append_replicate]

def leftBits : List Nat → List Bool
  | [] => []
  | a::l => ones a ++ false::leftBits l

def rightBits : List Nat → List Bool
  | [] => []
  | g::r => zeros g ++ true::rightBits r

def sec (l r : List Nat) : Z0 := ⟨0,false::leftBits l,(rightBits r).tail⟩

-- Canonical representation is needed only for dropping the bottom virtual zero.
def pushL (a : Nat) (l : List Nat) : List Nat := if a=0 ∧ l=[] then [] else a::l

theorem pushL_equiv (a : Nat) (l : List Nat) : bitsEq (leftBits (a::l)) (leftBits (pushL a l)) := by
  unfold pushL
  split
  · obtain ⟨ha,hl⟩ := ‹a=0 ∧ l=[]›
    subst a; subst l
    intro i; cases i <;> rfl
  · exact bitsEq_refl _

theorem left_decomp (l : List Nat) : bitsEq (leftBits l) (ones (l.headD 0) ++ false::leftBits l.tail) := by
  cases l with
  | nil => intro i; cases i <;> rfl
  | cons a l => exact bitsEq_refl _

-- A1 clears its current scanned one and all consecutive left ones.
theorem clear_ones (n : Nat) (L R : List Bool) :
    run0 table n ⟨0,ones n++L,R⟩ = some ⟨0,L,zeros n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 ⟨0,ones (n+1)++L,R⟩ = some ⟨0,ones n++L,false::R⟩ := by rfl
    have H := join0 h (ih (false::R))
    have hz : zeros (n+1) = zeros n++[false] := by rw [zeros_add]; rfl
    simpa only [show 1+n=n+1 by omega,hz,List.append_assoc,List.cons_append,List.nil_append] using H

def frame (a : Nat) (t : List Nat) (R : List Bool) : Z0 :=
  ⟨0,false::(ones a++false::leftBits t),R⟩

theorem sec_frame (l r : List Nat) :
    zEq (sec l r) (frame (l.headD 0) l.tail (rightBits r).tail) :=
  ⟨rfl,bitsEq_cons (left_decomp l) _,bitsEq_refl _⟩

def incR (d : Nat) (r : List Nat) : List Nat :=
  match r with
  | [] => []
  | g::t => (d+g)::t

theorem right_inc (d : Nat) (r : List Nat) : bitsEq (zeros d ++ rightBits r) (rightBits (incR d r)) := by
  cases r with
  | nil => simpa [rightBits,incR] using zeros_eq_nil d
  | cons g r =>
    simp only [incR,rightBits,zeros_add,List.append_assoc]
    exact bitsEq_refl _

theorem right_inc_tail (d : Nat) (r : List Nat) :
    bitsEq (zeros d ++ rightBits r) (rightBits (incR (d+1) r)).tail := by
  have h := bitsEq_tail (right_inc (d+1) r)
  exact h

theorem rightBits_head {r : List Nat} (h : r=[] ∨ r.headD 0≠0) : (rightBits r).headD false=false := by
  cases r with
  | nil => rfl
  | cons g r =>
    cases g with
    | zero => simp at h
    | succ g => rfl

theorem rightBits_pos (g : Nat) (r : List Nat) : (rightBits ((g+1)::r)).tail = zeros g ++ true::rightBits r := rfl

theorem long_prefix (a : Nat) (L R : List Bool) :
    run0 table 8 ⟨0,false::(ones a++false::L),[false,false,false]++R⟩ =
      some ⟨0,ones (a+1)++false::L,[true,false,true]++R⟩ := by rfl

theorem long_raw (a : Nat) (L R : List Bool) :
    run0 table (a+9) ⟨0,false::(ones a++false::L),[false,false,false]++R⟩ =
      some ⟨0,false::L,zeros (a+1)++[true,false,true]++R⟩ := by
  have H := join0 (long_prefix a L R) (clear_ones (a+1) (false::L) ([true,false,true]++R))
  simpa only [show 8+(a+1)=a+9 by omega,List.append_assoc] using H

theorem prefix2 (a : Nat) (L R : List Bool) :
    run0 table 3 ⟨0,false::(ones a++false::L),[false,true]++R⟩ =
      some ⟨0,R.headD false::(ones (a+3)++false::L),R.tail⟩ := by rfl

theorem prefix3 (a : Nat) (L R : List Bool) :
    run0 table 6 ⟨0,false::(ones a++false::L),[false,false,true,false,true]++R⟩ =
      some ⟨0,R.headD false::[true,true,false,false]++ones (a+2)++false::L,R.tail⟩ := by rfl

theorem prefix1 (b : Nat) (L R : List Bool) :
    run0 table 7 ⟨0,false::(ones (b+2)++false::L),true::R⟩ =
      some ⟨0,[false,true,true,false]++ones b++false::L,R⟩ := by rfl

theorem macro_empty (l : List Nat) : runs (l.headD 0+9) (sec l []) (sec l.tail [l.headD 0+2,1]) := by
  let a := l.headD 0
  let L := leftBits l.tail
  have H := runs_exact (long_raw a L [])
  apply runs_transport H
  · apply zEq_symm
    exact zEq_trans (sec_frame l []) ⟨rfl,bitsEq_refl _,bitsEq_symm (zeros_eq_nil 3)⟩
  · refine ⟨rfl,bitsEq_refl _,?_⟩
    simp only [a, L, sec, rightBits, rightBits_pos,List.append_nil]
    exact bitsEq_refl _

theorem macro_long (l r : List Nat) (g : Nat) :
    runs (l.headD 0+9) (sec l ((g+4)::r)) (sec l.tail ([l.headD 0+2,1,g]++r)) := by
  let a := l.headD 0
  let L := leftBits l.tail
  have H := runs_exact (long_raw a L (zeros g++true::rightBits r))
  apply runs_transport H
  · apply zEq_symm
    exact sec_frame l ((g+4)::r)
  · refine ⟨rfl,bitsEq_refl _,?_⟩
    simp only [a, L, sec, rightBits,rightBits_pos,List.cons_append,List.nil_append,List.append_assoc]
    exact bitsEq_refl _

theorem macro_one (l r : List Nat) (ha : 2≤l.headD 0) :
    runs 7 (sec l (1::r)) (sec (pushL 2 (pushL (l.headD 0-2) l.tail)) (incR 1 r)) := by
  let b := l.headD 0-2
  have ha' : b+2=l.headD 0 := by dsimp [b]; omega
  have H := runs_exact (prefix1 b (leftBits l.tail) (rightBits r))
  apply runs_transport H
  · apply zEq_symm
    have F := sec_frame l (1::r)
    rw [← ha'] at F
    exact F
  · refine ⟨rfl,?_,right_inc_tail 0 r⟩
    exact bitsEq_cons (bitsEq_append [true,true,false] (pushL_equiv b l.tail)) false

theorem macro_two_short (l r : List Nat) (h : r=[] ∨ r.headD 0≠0) :
    runs 3 (sec l (2::r)) (sec ((l.headD 0+3)::l.tail) r) := by
  have H := prefix2 (l.headD 0) (leftBits l.tail) (rightBits r)
  rw [rightBits_head h] at H
  exact runs_transport (runs_exact H) (zEq_symm (sec_frame l (2::r))) (zEq_refl _)

theorem macro_two_long (l r : List Nat) :
    runs (l.headD 0+7) (sec l (2::0::r)) (sec l.tail (incR (l.headD 0+5) r)) := by
  let a := l.headD 0
  have H := prefix2 a (leftBits l.tail) (true::rightBits r)
  have G := clear_ones (a+4) (false::leftBits l.tail) (rightBits r)
  have J := join0 H G
  have K : runs (a+7) (frame a l.tail ([false,true,true]++rightBits r))
      ⟨0,false::leftBits l.tail,zeros (a+4)++rightBits r⟩ := by
    rw [show a+7=3+(a+4) by omega]
    exact runs_exact J
  exact runs_transport K (zEq_symm (sec_frame l (2::0::r)))
    ⟨rfl,bitsEq_refl _,right_inc_tail (a+4) r⟩

theorem macro_three_short (l r : List Nat) (h : r=[] ∨ r.headD 0≠0) :
    runs 6 (sec l (3::1::r)) (sec ([2,0,l.headD 0+2]++l.tail) r) := by
  have H := prefix3 (l.headD 0) (leftBits l.tail) (rightBits r)
  rw [rightBits_head h] at H
  exact runs_transport (runs_exact H) (zEq_symm (sec_frame l (3::1::r))) (zEq_refl _)

theorem macro_three_long (l r : List Nat) :
    runs 9 (sec l (3::1::0::r)) (sec ([0,l.headD 0+2]++l.tail) (incR 4 r)) := by
  let a := l.headD 0
  have H := prefix3 a (leftBits l.tail) (true::rightBits r)
  have G := clear_ones 3 (false::false::(ones (a+2)++false::leftBits l.tail)) (rightBits r)
  have J := join0 H G
  have K : runs 9 (frame a l.tail ([false,false,true,false,true,true]++rightBits r))
      ⟨0,false::false::(ones (a+2)++false::leftBits l.tail),zeros 3++rightBits r⟩ := runs_exact J
  exact runs_transport K (zEq_symm (sec_frame l (3::1::0::r)))
    ⟨rfl,bitsEq_refl _,right_inc_tail 3 r⟩

#print axioms macro_empty
#print axioms macro_long
#print axioms macro_one
#print axioms macro_two_short
#print axioms macro_two_long
#print axioms macro_three_short
#print axioms macro_three_long
end BB6.Agent25M44
