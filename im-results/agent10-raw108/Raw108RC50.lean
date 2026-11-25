import SweepPumping
namespace BB6.Agent10Raw108RC50
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Raw108/0RC leaf 50: a finite abstraction of the exact run-length return
    system. The certificate allows arbitrary run lengths and stack depth. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

abbrev LS := Fin 7
abbrev C := Fin 3
abbrev K := Fin 2
abbrev RS := Fin 6
abbrev Q := Fin 56

def cap (n : Nat) : C := ⟨min n 2,by omega⟩
def bump (j : C) : C := cap (j.val+1)
def pos (n : Nat) : K := ⟨min n 1,by omega⟩
def liftK (k : K) : C := ⟨k.val+1,by omega⟩
def push (s : LS) (k : K) : LS := ⟨if s.val=0 then k.val+1 else 3+2*((s.val-1)%2)+k.val,by split <;> omega⟩
def sc (j : C) (l : LS) : Q := ⟨7*j.val+l.val,by omega⟩
def rt (j : C) (l : LS) : Q := ⟨7*(3+j.val)+l.val,by omega⟩
def ev (l : LS) : Q := ⟨42+l.val,by omega⟩
def bl (l : LS) : Q := ⟨49+l.val,by omega⟩

def rpush (b : Bool) (j : C) (s : RS) : RS :=
  match s.val with
  | 0 | 4 => if b then 4 else if j.val=0 then 1 else if j.val=1 then 2 else 3
  | 1 => if !b && j.val=0 then 0 else 5
  | 2 | 3 => if b then 4 else if j.val=0 then 2 else 3
  | _ => 5

-- Determinized six-class right suffix safety relation, extracted from
-- backwards saturation of the 56-control-state abstract stack machine.
def forbidden (s : RS) : Nat :=
  match s.val with
  | 0 => 125533467065712641
  | 1 => 95323236927012863
  | 2 => 72237914142015489
  | 3 => 72237914142015488
  | 4 => 125533467065712640
  | _ => 144115188075855871

def safe (p : Q) (s : RS) : Bool := !(forbidden s).testBit p.val

theorem cap_succ (n : Nat) : cap (n+1) = bump (cap n) := by
  apply Fin.ext; simp [cap,bump]; omega

theorem cap_pos (n : Nat) : cap (n+1) = liftK (pos n) := by
  apply Fin.ext; simp [cap,liftK,pos]; omega

theorem pos_succ (n : Nat) : pos (n+1) = 1 := by
  apply Fin.ext; simp [pos]

theorem sc_inc0 (j : C) (s : RS) : safe (sc (bump j) 0) s = true → safe (sc j (push 0 0)) s = true := by revert j s; decide
theorem sc_inc1 (j : C) (l : LS) (k : K) (s : RS) :
    safe (sc (bump j) (push l k)) s = true → safe (sc j (push l 1)) s = true := by revert j l k s; decide
theorem sc_end0 : safe (sc 0 0) 0 = true → safe (bl (push (push 0 0) 0)) 0 = true := by decide
theorem sc_end1 (l : LS) (k : K) : safe (sc 0 (push l k)) 0 = true → safe (bl (push (push l 1) 0)) 0 = true := by revert l k; decide
theorem sc_pop0 (b : Bool) (j : C) (s : RS) :
    safe (sc 0 0) (rpush b j s) = true → safe (if b then sc j (push (push 0 0) 0) else rt j (push (push 0 0) 0)) s = true := by revert b j s; decide
theorem sc_pop1 (b : Bool) (j : C) (l : LS) (k : K) (s : RS) :
    safe (sc 0 (push l k)) (rpush b j s) = true → safe (if b then sc j (push (push l 1) 0) else rt j (push (push l 1) 0)) s = true := by revert b j l k s; decide
theorem rt_pop0 (j : C) (s : RS) : safe (rt (bump j) 0) s = true → safe (rt 0 0) (rpush false j s) = true := by revert j s; decide
theorem rt_pop1 (j : C) (l : LS) (k : K) (s : RS) :
    safe (rt (bump j) (push l k)) s = true → safe (rt (liftK k) l) (rpush false j s) = true := by revert j l k s; decide
theorem rt_single0 (j : C) (s : RS) : safe (rt 0 0) (rpush false j s) = true → safe (sc (bump j) 0) s = true := by revert j s; decide
theorem rt_single1 (j : C) (l : LS) (s : RS) : safe (rt 0 (push l 0)) (rpush false j s) = true → safe (ev l) (rpush false (bump j) s) = true := by revert j l s; decide
theorem rt_bad0 (l : LS) : safe (rt 0 l) 0 = false := by revert l; decide
theorem rt_bad4 (l : LS) (j : C) (s : RS) : safe (rt 0 l) (rpush true j s) = false := by revert l j s; decide
theorem rt_badk (l : LS) (j : C) (s : RS) : safe (rt 0 (push l 1)) (rpush false j s) = false := by revert l j s; decide
theorem ev_pop0 (j : C) (s : RS) : safe (ev 0) (rpush false j s) = true → safe (rt 0 0) (rpush true j s) = true := by revert j s; decide
theorem ev_pop1 (j : C) (l : LS) (k : K) (s : RS) : safe (ev (push l k)) (rpush false j s) = true → safe (rt (liftK k) l) (rpush true j s) = true := by revert j l k s; decide
theorem ev_bad0 (l : LS) : safe (ev l) 0 = false := by revert l; decide
theorem ev_bad4 (l : LS) (j : C) (s : RS) : safe (ev l) (rpush true j s) = false := by revert l j s; decide
theorem bl_pop0 : safe (bl 0) 0 = true → safe (rt 0 0) (rpush false 0 0) = true := by decide
theorem bl_pop1 (l : LS) (k : K) : safe (bl (push l k)) 0 = true → safe (rt (liftK k) l) (rpush false 0 0) = true := by revert l k; decide
theorem init_safe : safe (bl 0) 0 = true := by decide

abbrev P : List Bool := [true,true]
abbrev Z : List Bool := [false,false]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
def pair (n : Nat) : List Bool := rep P n
def odd (n : Nat) : List Bool := true::pair n
def left : List Nat → List Bool
  | [] => []
  | n::ls => false::(pair (n+1)++left ls)
def right : List (Bool × Nat) → List Bool
  | [] => []
  | (b,n)::rs => (if b then Z++Z else Z)++odd n++right rs

def lcode : List Nat → LS
  | [] => 0
  | n::ls => push (lcode ls) (pos n)
def rcode : List (Bool × Nat) → RS
  | [] => 0
  | (b,n)::rs => rpush b (cap n) (rcode rs)

def increment : List Nat → List Nat
  | [] => [0]
  | n::ls => (n+1)::ls

def extend (ls : List Nat) : List Nat := 0::increment ls

def top : List Nat → Nat
  | [] => 0
  | n::_ => n+1

inductive Section where
  | scan (j : Nat) (ls : List Nat) (rs : List (Bool × Nat))
  | ret (j : Nat) (ls : List Nat) (rs : List (Bool × Nat))
  | even (ls : List Nat) (rs : List (Bool × Nat))
  | blank (ls : List Nat)

def cfg : Section → Z0
  | .scan j ls rs => A (left ls) (Z++odd j++right rs)
  | .ret j ls rs => A (left ls) (odd j++right rs)
  | .even ls rs => A (left ls) (P++right rs)
  | .blank ls => A (left ls) []

def good : Section → Prop
  | .scan j ls rs => safe (sc (cap j) (lcode ls)) (rcode rs) = true
  | .ret j ls rs => safe (rt (cap j) (lcode ls)) (rcode rs) = true
  | .even ls rs => safe (ev (lcode ls)) (rcode rs) = true
  | .blank ls => safe (bl (lcode ls)) 0 = true

theorem odd_succ (n : Nat) : odd (n+1) = P++odd n := by rfl

theorem pair_scan (k : Nat) (L R : List Bool) :
    run0 table (2*k) (A (pair k++L) R) = some (A L (pair k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 2 (A (P++pair k++L) R) = some (A (pair k++L) (P++R)) := by rfl
    have H := join0 h (ih (P++R))
    change run0 table (2*(k+1)) (A ((P++pair k)++L) R) = some (A L ((P++pair k)++R))
    rw [show 2*(k+1)=2+2*k by omega]
    simpa only [List.append_assoc,←List.append_assoc (pair k) P R,show pair k++P=P++pair k from rep_snoc P k] using H

theorem pair_commute_true (k : Nat) (R : List Bool) : pair k++true::R = true::(pair k++R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (P++pair k)++true::R = true::((P++pair k)++R)
    simp only [List.append_assoc,ih];rfl

theorem odd_scan (k : Nat) (L R : List Bool) :
    run0 table (2*k+1) (A (odd k++L) R) = some (A L (odd k++R)) := by
  have h : run0 table 1 (A (true::(pair k++L)) R) = some (A (pair k++L) (true::R)) := by rfl
  have H := join0 h (pair_scan k L (true::R))
  rw [pair_commute_true,show 1+2*k=2*k+1 by omega] at H
  exact H

theorem inc_macro (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    run0 table 8 (cfg (.scan (j+1) ls rs)) = some (cfg (.scan j (increment ls) rs)) := by
  cases ls <;> rfl

theorem sc_to_ret (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    run0 table 5 (cfg (.scan 0 ls ((false,j)::rs))) = some (cfg (.ret j (extend ls) rs)) := by
  cases ls <;> rfl

theorem sc_to_sc (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    run0 table 5 (cfg (.scan 0 ls ((true,j)::rs))) = some (cfg (.scan j (extend ls) rs)) := by
  cases ls <;> rfl

theorem sc_to_bl (ls : List Nat) :
    run0 table 5 (cfg (.scan 0 ls [])) = some (cfg (.blank (extend ls))) := by
  cases ls <;> rfl

theorem rt_pop_macro (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    run0 table (4+(2*top ls+1)) (cfg (.ret (j+1) ls rs)) =
      some (cfg (.ret (top ls) ls.tail ((false,j)::rs))) := by
  cases ls with
  | nil => rfl
  | cons n ls =>
    have h : run0 table 4 (cfg (.ret (j+1) (n::ls) rs)) =
      some (A (odd (n+1)++left ls) (Z++odd j++right rs)) := by rfl
    exact join0 h (odd_scan (n+1) (left ls) (Z++odd j++right rs))

theorem rt_to_sc (j : Nat) (rs : List (Bool × Nat)) :
    run0 table 11 (cfg (.ret 0 [] ((false,j)::rs))) = some (cfg (.scan (j+1) [] rs)) := by rfl

theorem rt_to_ev (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    run0 table 13 (cfg (.ret 0 (0::ls) ((false,j)::rs))) = some (cfg (.even ls ((false,j+1)::rs))) := by
  have h : run0 table 11 (cfg (.ret 0 (0::ls) ((false,j)::rs))) =
      some (A (P++left ls) (Z++odd (j+1)++right rs)) := by rfl
  have H := join0 h (pair_scan 1 (left ls) (Z++odd (j+1)++right rs))
  exact H

theorem ev_to_rt (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    run0 table (4+(2*top ls+1)) (cfg (.even ls ((false,j)::rs))) =
      some (cfg (.ret (top ls) ls.tail ((true,j)::rs))) := by
  cases ls with
  | nil => rfl
  | cons n ls =>
    have h : run0 table 4 (cfg (.even (n::ls) ((false,j)::rs))) =
      some (A (odd (n+1)++left ls) ((Z++Z)++odd j++right rs)) := by rfl
    exact join0 h (odd_scan (n+1) (left ls) ((Z++Z)++odd j++right rs))

theorem bl_to_rt (ls : List Nat) :
    run0 table (10+(2*top ls+1)) (cfg (.blank ls)) =
      some (cfg (.ret (top ls) ls.tail [(false,0)])) := by
  cases ls with
  | nil => rfl
  | cons n ls =>
    have h : run0 table 10 (cfg (.blank (n::ls))) = some (A (odd (n+1)++left ls) (Z++odd 0)) := by rfl
    exact join0 h (odd_scan (n+1) (left ls) (Z++odd 0))

theorem cap_zero : cap 0 = 0 := by decide
theorem pos_zero : pos 0 = 0 := by decide

theorem good_inc (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    good (.scan (j+1) ls rs) → good (.scan j (increment ls) rs) := by
  cases ls with
  | nil => simpa only [good,lcode,increment,cap_succ,pos_zero,cap_zero] using sc_inc0 (cap j) (rcode rs)
  | cons n ls => simpa only [good,lcode,increment,cap_succ,pos_succ] using sc_inc1 (cap j) (lcode ls) (pos n) (rcode rs)

theorem good_sc_blank (ls : List Nat) : good (.scan 0 ls []) → good (.blank (extend ls)) := by
  cases ls with
  | nil => exact sc_end0
  | cons n ls => simpa only [good,lcode,rcode,extend,increment,pos_succ,pos_zero,cap_zero] using sc_end1 (lcode ls) (pos n)

theorem good_sc_pop (b : Bool) (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    good (.scan 0 ls ((b,j)::rs)) → good (if b then .scan j (extend ls) rs else .ret j (extend ls) rs) := by
  cases b <;> cases ls with
  | nil => exact sc_pop0 _ (cap j) (rcode rs)
  | cons n ls =>
    first
    | exact (by
        change safe (sc 0 (push (lcode ls) (pos n))) (rpush false (cap j) (rcode rs)) = true →
          safe (rt (cap j) (push (push (lcode ls) (pos (n+1))) 0)) (rcode rs) = true
        rw [pos_succ]
        exact sc_pop1 false (cap j) (lcode ls) (pos n) (rcode rs))
    | exact (by
        change safe (sc 0 (push (lcode ls) (pos n))) (rpush true (cap j) (rcode rs)) = true →
          safe (sc (cap j) (push (push (lcode ls) (pos (n+1))) 0)) (rcode rs) = true
        rw [pos_succ]
        exact sc_pop1 true (cap j) (lcode ls) (pos n) (rcode rs))

theorem good_rt_pop (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    good (.ret (j+1) ls rs) → good (.ret (top ls) ls.tail ((false,j)::rs)) := by
  cases ls with
  | nil => simpa only [good,lcode,rcode,top,List.tail_nil,cap_succ,cap_zero] using rt_pop0 (cap j) (rcode rs)
  | cons n ls =>
    change safe (rt (cap (j+1)) (push (lcode ls) (pos n))) (rcode rs) = true →
      safe (rt (cap (n+1)) (lcode ls)) (rpush false (cap j) (rcode rs)) = true
    rw [cap_pos n,cap_succ j]
    exact rt_pop1 (cap j) (lcode ls) (pos n) (rcode rs)

theorem good_rt_sc (j : Nat) (rs : List (Bool × Nat)) : good (.ret 0 [] ((false,j)::rs)) → good (.scan (j+1) [] rs) := by
  simpa only [good,lcode,rcode,cap_succ,pos_zero,cap_zero] using rt_single0 (cap j) (rcode rs)

theorem good_rt_ev (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    good (.ret 0 (0::ls) ((false,j)::rs)) → good (.even ls ((false,j+1)::rs)) := by
  simpa only [good,lcode,rcode,cap_succ,pos_zero,cap_zero] using rt_single1 (cap j) (lcode ls) (rcode rs)

theorem good_ev_pop (j : Nat) (ls : List Nat) (rs : List (Bool × Nat)) :
    good (.even ls ((false,j)::rs)) → good (.ret (top ls) ls.tail ((true,j)::rs)) := by
  cases ls with
  | nil => exact ev_pop0 (cap j) (rcode rs)
  | cons n ls => simpa only [good,lcode,rcode,top,List.tail_cons,cap_pos,cap_zero] using ev_pop1 (cap j) (lcode ls) (pos n) (rcode rs)

theorem good_bl_pop (ls : List Nat) : good (.blank ls) → good (.ret (top ls) ls.tail [(false,0)]) := by
  cases ls with
  | nil => exact bl_pop0
  | cons n ls => simpa only [good,lcode,rcode,top,List.tail_cons,cap_pos,cap_zero] using bl_pop1 (lcode ls) (pos n)

theorem next (c : Section) (hc : good c) : ∃ t d, 0 < t ∧ run0 table t (cfg c) = some (cfg d) ∧ good d := by
  cases c with
  | scan j ls rs =>
    cases j with
    | succ j => exact ⟨8,.scan j (increment ls) rs,by decide,inc_macro j ls rs,good_inc j ls rs hc⟩
    | zero =>
      cases rs with
      | nil => exact ⟨5,.blank (extend ls),by decide,sc_to_bl ls,good_sc_blank ls hc⟩
      | cons r rs =>
        rcases r with ⟨b,j⟩
        cases b with
        | false => exact ⟨5,.ret j (extend ls) rs,by decide,sc_to_ret j ls rs,good_sc_pop false j ls rs hc⟩
        | true => exact ⟨5,.scan j (extend ls) rs,by decide,sc_to_sc j ls rs,good_sc_pop true j ls rs hc⟩
  | ret j ls rs =>
    cases j with
    | succ j => exact ⟨4+(2*top ls+1),.ret (top ls) ls.tail ((false,j)::rs),by omega,rt_pop_macro j ls rs,good_rt_pop j ls rs hc⟩
    | zero =>
      cases rs with
      | nil =>
        have hh := rt_bad0 (lcode ls)
        change safe (rt 0 (lcode ls)) 0 = true at hc
        rw [hh] at hc; contradiction
      | cons r rs =>
        rcases r with ⟨b,j⟩
        cases b with
        | true =>
          have hh := rt_bad4 (lcode ls) (cap j) (rcode rs)
          change safe (rt 0 (lcode ls)) (rpush true (cap j) (rcode rs)) = true at hc
          rw [hh] at hc; contradiction
        | false =>
          cases ls with
          | nil => exact ⟨11,.scan (j+1) [] rs,by decide,rt_to_sc j rs,good_rt_sc j rs hc⟩
          | cons n ls =>
            cases n with
            | zero => exact ⟨13,.even ls ((false,j+1)::rs),by decide,rt_to_ev j ls rs,good_rt_ev j ls rs hc⟩
            | succ n =>
              have hh := rt_badk (lcode ls) (cap j) (rcode rs)
              change safe (rt 0 (push (lcode ls) (pos (n+1)))) (rpush false (cap j) (rcode rs)) = true at hc
              rw [pos_succ,hh] at hc; contradiction
  | even ls rs =>
    cases rs with
    | nil =>
      have hh := ev_bad0 (lcode ls)
      change safe (ev (lcode ls)) 0 = true at hc
      rw [hh] at hc; contradiction
    | cons r rs =>
      rcases r with ⟨b,j⟩
      cases b with
      | true =>
        have hh := ev_bad4 (lcode ls) (cap j) (rcode rs)
        change safe (ev (lcode ls)) (rpush true (cap j) (rcode rs)) = true at hc
        rw [hh] at hc; contradiction
      | false => exact ⟨4+(2*top ls+1),.ret (top ls) ls.tail ((true,j)::rs),by omega,ev_to_rt j ls rs,good_ev_pop j ls rs hc⟩
  | blank ls => exact ⟨10+(2*top ls+1),.ret (top ls) ls.tail [(false,0)],by omega,bl_to_rt ls,good_bl_pop ls hc⟩

noncomputable def advance (c : {c : Section // good c}) : Nat × {c : Section // good c} :=
  let h := next c.val c.property
  (h.choose,⟨h.choose_spec.choose,h.choose_spec.choose_spec.2.2⟩)
noncomputable def seq : Nat → {c : Section // good c}
  | 0 => ⟨.blank [],init_safe⟩
  | n+1 => (advance (seq n)).2
noncomputable def family (n : Nat) : Z0 := cfg (seq n).val
noncomputable def cost (n : Nat) : Nat := (advance (seq n)).1

theorem entry : run0 table 0 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (n : Nat) : 0 < cost n := (next (seq n).val (seq n).property).choose_spec.choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (next (seq n).val (seq n).property).choose_spec.choose_spec.2.1

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 0 cost entry positive growth m hm

#print axioms next
#print axioms growth
#print axioms never
end BB6.Agent10Raw108RC50
