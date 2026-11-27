import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF47
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def zeros (n : Nat) : List Bool := rep [false] n
def ones (n : Nat) : List Bool := rep [true] n

def padded (a b : List Bool) : Prop := ∀ i : Nat, a[i]?.getD false = b[i]?.getD false

theorem padded_refl (a : List Bool) : padded a a := fun _ => rfl
theorem padded_symm {a b : List Bool} (h : padded a b) : padded b a := fun i => (h i).symm
theorem padded_trans {a b c : List Bool} (h : padded a b) (g : padded b c) : padded a c := fun i => (h i).trans (g i)
theorem padded_cons {a b : List Bool} (h : padded a b) (v : Bool) : padded (v::a) (v::b) := by
  intro i; cases i with
  | zero => rfl
  | succ i => exact h i

theorem padded_append (pre : List Bool) {a b : List Bool} (h : padded a b) : padded (pre++a) (pre++b) := by
  induction pre with
  | nil => exact h
  | cons v pre ih => exact padded_cons ih v

theorem padded_zero : padded [] [false] := by intro i; cases i <;> rfl

theorem padded_zeros (n : Nat) : padded [] (zeros n) := by
  induction n with
  | zero => exact padded_refl []
  | succ n ih => exact padded_trans padded_zero (padded_cons ih false)

theorem padded_head {a b : List Bool} (h : padded a b) : a.headD false = b.headD false := by
  cases a <;> cases b <;> exact h 0

theorem padded_tail {a b : List Bool} (h : padded a b) : padded a.tail b.tail := by
  intro i
  cases a <;> cases b <;> exact h (i+1)

def zrel (a b : Z0) : Prop := a.q = b.q ∧ padded a.l b.l ∧ padded a.r b.r

theorem zrel_refl (a : Z0) : zrel a a := ⟨rfl,padded_refl _,padded_refl _⟩
theorem zrel_symm {a b : Z0} (h : zrel a b) : zrel b a := ⟨h.1.symm,padded_symm h.2.1,padded_symm h.2.2⟩
theorem zrel_trans {a b c : Z0} (h : zrel a b) (g : zrel b c) : zrel a c := ⟨h.1.trans g.1,padded_trans h.2.1 g.2.1,padded_trans h.2.2 g.2.2⟩

theorem move_rel (mv : Move) {a b : Z0} (h : zrel a b) : zrel (move0 mv a) (move0 mv b) := by
  unfold move0
  cases hv : mv.right
  · exact ⟨rfl,padded_tail h.2.1,padded_cons h.2.2 _⟩
  · refine ⟨rfl,?_,padded_tail h.2.2⟩
    rw [padded_head h.2.2]
    exact padded_cons (padded_cons (padded_tail h.2.1) _) _

theorem run_rel (p : PartialMachine) (n : Nat) {a b c : Z0} (h : zrel a b)
    (hr : run0 p n a = some c) : ∃ d, run0 p n b = some d ∧ zrel c d := by
  induction n generalizing a b c with
  | zero => simp [run0] at hr; subst c; exact ⟨b,rfl,h⟩
  | succ n ih =>
    change (((p (a.q,a.l.headD false)).bind id).map (fun mv => move0 mv a)).bind (run0 p n) = some c at hr
    change ∃ d, (((p (b.q,b.l.headD false)).bind id).map (fun mv => move0 mv b)).bind (run0 p n) = some d ∧ zrel c d
    rw [← h.1,← padded_head h.2.1]
    cases he : (p (a.q,a.l.headD false)).bind id with
    | none => rw [he] at hr; contradiction
    | some mv =>
      simp only [he,Option.map_some,Option.bind_some] at hr ⊢
      exact ih (move_rel mv h) hr

def sec (l r : List Bool) : Z0 := ⟨0,l,[true,false]++r⟩

def goes (a b : Z0) : Prop := ∃ t d, 0 < t ∧ run0 table t a = some d ∧ zrel d b

theorem goes_of_eq {a b : Z0} {t : Nat} (ht : 0 < t) (h : run0 table t a = some b) : goes a b := ⟨t,b,ht,h,zrel_refl b⟩
theorem goes_congr {a b c d : Z0} (ha : zrel a b) (hb : zrel c d) (h : goes a c) : goes b d := by
  obtain ⟨t,e,ht,he,hr⟩ := h
  obtain ⟨f,hf,hrel⟩ := run_rel table t ha he
  exact ⟨t,f,ht,hf,zrel_trans (zrel_symm hrel) (zrel_trans hr hb)⟩

theorem goes_join {a b c : Z0} (h : goes a b) (g : goes b c) : goes a c := by
  obtain ⟨t,d,ht,hd,hr⟩ := h
  obtain ⟨u,e,hu,he,hs⟩ := goes_congr (zrel_symm hr) (zrel_refl c) g
  exact ⟨t+u,e,by omega,join0 hd he,hs⟩

def atR (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,R.headD false::L,R.tail⟩

theorem scanC (n : Nat) (L R : List Bool) :
    run0 table n (atR 2 L (ones n++R)) = some (atR 2 (zeros n++L) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    change run0 table (n+1) (atR 2 L (true::(ones n++R))) = some (atR 2 (false::(zeros n++L)) R)
    have a (X Y : List Bool) : run0 table 1 (atR 2 X (true::Y)) = some (atR 2 (false::X) Y) := by rfl
    have h := join0 (a L (ones n++R)) (ih (false::L))
    rw [show 1+n=n+1 by omega] at h
    have rot : zeros n++false::L = false::(zeros n++L) := by
      change rep [false] n ++ ([false] ++ L) = _
      rw [← List.append_assoc, rep_snoc]; rfl
    rwa [rot] at h

theorem a0_one (b : Nat) (L R : List Bool) :
    run0 table (b+6) (sec (false::L) (ones b++false::true::R)) =
      some (sec (zeros b++[true,false,true]++L) R) := by
  have a (X Y : List Bool) : run0 table 3 (sec (false::X) Y) = some (atR 2 ([true,false,true]++X) Y) := by rfl
  have c (X Y : List Bool) : run0 table 3 (atR 2 X (false::true::Y)) = some (sec X Y) := by rfl
  have h := join0 (join0 (a L (ones b++false::true::R)) (scanC b ([true,false,true]++L) (false::true::R)))
    (c (zeros b++([true,false,true]++L)) R)
  rw [show 3+b+3=b+6 by omega] at h
  simpa only [List.append_assoc] using h

theorem a0_zero (b : Nat) (L R : List Bool) :
    run0 table (2*b+8) (sec (false::L) (ones b++false::false::R)) =
      some (sec (true::L) (ones (b+2)++R)) := by
  have a (X Y : List Bool) : run0 table 3 (sec (false::X) Y) = some (atR 2 ([true,false,true]++X) Y) := by rfl
  have c (X Y : List Bool) : run0 table 1 (atR 2 X (false::false::Y)) = some ⟨3,false::false::X,Y⟩ := by rfl
  have d := sweepL table 3 [] [] [false] [true] 1 (fun _ _ => rfl) (b+2) ([true,false,true]++L) R
  have e (X Y : List Bool) : run0 table 2 ⟨3,[true,false,true]++X,Y⟩ = some (sec (true::X) Y) := by rfl
  have h1 := join0 (join0 (a L (ones b++false::false::R)) (scanC b ([true,false,true]++L) (false::false::R)))
    (c (zeros b++([true,false,true]++L)) R)
  have h2 := join0 h1 (by simpa only [rep,zeros,ones,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,Nat.one_mul] using d)
  have h3 := join0 h2 (e L (ones (b+2)++R))
  rw [show 3+b+1+(b+2)+2=2*b+8 by omega] at h3
  exact h3

theorem a1_one (L R : List Bool) :
    run0 table 7 (sec (true::false::true::L) R) = some (sec (true::false::L) (false::R)) := by rfl

theorem a1_two (L R : List Bool) :
    run0 table 13 (sec (true::false::false::true::false::L) R) = some (sec (true::false::L) ([true,true,false]++R)) := by rfl

theorem a1_three (L R : List Bool) :
    run0 table 8 (sec (true::false::false::false::L) R) = some (sec L ([true,true,true,false]++R)) := by rfl

#print axioms a0_one
#print axioms a0_zero
#print axioms run_rel
end BB6.Agent8Raw54.RF47
