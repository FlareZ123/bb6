import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw118BinaryCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Row 655 when false; row 657 when true. -/
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨v,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_ => none
abbrev z : Bool := false
abbrev o : Bool := true
def d (v : Bool) : Nat := if v then 3 else 2
def extra (v : Bool) : Nat := if v then 1 else 0
def oneBlock (v : Bool) : List Bool := if v then [z,o] else [o]
def zeroBlock (v : Bool) : List Bool := if v then [z,z,z] else [z,z]
def pref (v b : Bool) : List Bool := if v then [o,z,b] else [z,b]
abbrev A (n : Nat) (L R : List Bool) : Z0 := ⟨0,rep [o] (n+1)++L,R⟩
abbrev C (n : Nat) (b : Bool) (L R : List Bool) : Z0 := ⟨2,b::(rep [o] (n+1)++L),R⟩

theorem aLeft (v : Bool) (L R : List Bool) :
    run0 (table v) 1 ⟨0,[o]++L,R⟩ = some ⟨0,L,[o]++R⟩ := by rfl

theorem bRight (v : Bool) (L R : List Bool) :
    run0 (table v) 1 ⟨1,[o]++L,[o]++R⟩ = some ⟨1,[o]++[o]++L,R⟩ := by rfl

theorem prepB (v : Bool) (n : Nat) (L R : List Bool) (b : Bool) :
    run0 (table v) (n+3) ⟨0,z::L,rep [o] (n+1)++z::b::R⟩ = some (C (n+2) b L R) := by
  have h1 : run0 (table v) 1 ⟨0,z::L,rep [o] (n+1)++z::b::R⟩ = some ⟨1,[o,o]++L,rep [o] n++z::b::R⟩ := by cases v <;> rfl
  have h2 := sweepR (table v) 1 [o] [] [o] [o] 1
    (fun L R => by simpa only [List.nil_append] using bRight v L R) n (o::L) (z::b::R)
  have h3 : run0 (table v) 2 ⟨1,[o]++rep [o] n++o::L,z::b::R⟩ = some ⟨2,b::o::o::(rep [o] n++o::L),R⟩ := by cases v <;> rfl
  have h2' : run0 (table v) n ⟨1,[o,o]++L,rep [o] n++z::b::R⟩ = some ⟨1,[o]++rep [o] n++o::L,z::b::R⟩ := by
    simpa only [Nat.one_mul,List.nil_append,List.cons_append] using h2
  have h4 := join0 (join0 h1 h2') h3
  rw [show 1+n+2 = n+3 by omega] at h4
  have hr : rep [o] n++o::L = o::(rep [o] n++L) := by
    have hs := congrArg (· ++ L) (rep_snoc [o] n)
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using hs
  rw [hr] at h4
  exact h4

theorem prepare (v : Bool) (n : Nat) (L R : List Bool) (b : Bool) :
    run0 (table v) (n+1+(n+extra v+3)) (A n (z::L) (pref v b++R)) = some (C (n+d v) b L R) := by
  have h := sweepL (table v) 0 [] [] [o] [o] 1
    (fun L R => by simpa only [List.nil_append] using aLeft v L R) (n+1) (z::L) (pref v b++R)
  have h1 : run0 (table v) (n+1) (A n (z::L) (pref v b++R)) = some ⟨0,z::L,rep [o] (n+1)++pref v b++R⟩ := by
    simpa only [Nat.one_mul,List.nil_append,List.append_assoc] using h
  have h2 : run0 (table v) (n+extra v+3) ⟨0,z::L,rep [o] (n+1)++pref v b++R⟩ = some (C (n+d v) b L R) := by
    cases v with
    | false => simpa [extra,d,pref,List.append_assoc] using prepB false n L R b
    | true =>
      have he : rep [o] (n+1)++[o,z,b]++R = rep [o] (n+1+1)++z::b::R := by
        have hs := congrArg (· ++ z::b::R) (rep_snoc [o] (n+1))
        simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using hs
      change run0 (table true) (n+1+3) ⟨0,z::L,rep [o] (n+1)++[o,z,b]++R⟩ = some (C (n+3) b L R)
      rw [he]
      simpa only [show n+1+2=n+3 by omega] using prepB true (n+1) L R b
  exact join0 h1 h2

theorem carry (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (n+1+(n+extra v+3)+1) (A n (z::L) (v::(oneBlock v++R))) = some (A (n+d v) L (v::R)) := by
  have h := prepare v n L R true
  have he : v::(oneBlock v++R) = pref v true++R := by cases v <;> rfl
  rw [← he] at h
  exact join0 h (by cases v <;> rfl)

theorem cToE (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) 4 (C (n+d v) false L (z::R)) = some ⟨4,rep [o] (n+d v+2)++L,o::R⟩ := by
  cases v <;> rfl

theorem eLeft (v : Bool) (L R : List Bool) :
    run0 (table v) 1 ⟨4,[o]++L,R⟩ = some ⟨4,L,[z]++R⟩ := by rfl

theorem clear (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (n+d v+2) ⟨4,rep [o] (n+d v+2)++L,o::R⟩ =
      some ⟨4,L,rep [z] (n+d v+2)++o::R⟩ := by
  simpa only [Nat.one_mul,List.nil_append] using sweepL (table v) 4 [] [] [o] [z] 1
    (fun L R => by simpa only [List.nil_append] using eLeft v L R) (n+d v+2) L (o::R)

theorem finish (v : Bool) (L R : List Bool) :
    run0 (table v) 13 ⟨4,z::L,z::z::z::z::R⟩ = some (A 0 (z::z::z::L) (v::R)) := by cases v <;> rfl

theorem zeroPrefix (v : Bool) (n : Nat) (R : List Bool) :
    rep [z] (n+d v+2)++o::R = z::z::z::z::(rep [z] n++oneBlock v++R) := by
  cases v with
  | false => simp [d,oneBlock,rep,List.append_assoc]
  | true =>
    simp only [d,oneBlock,ite_true,rep,List.cons_append,List.nil_append,List.append_assoc]
    have h := congrArg (· ++ o::R) (rep_snoc [z] n)
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun t => z::z::z::z::t) h.symm

theorem zero (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (n+1+(n+extra v+3)+4+(n+d v+2)+13) (A n (z::z::L) (v::(zeroBlock v++R))) =
      some (A 0 (z::z::z::L) (v::(rep [z] n++oneBlock v++R))) := by
  have h := prepare v n (z::L) (z::R) false
  have he : v::(zeroBlock v++R) = pref v false++z::R := by cases v <;> rfl
  rw [← he] at h
  have h2 := join0 (join0 h (cToE v n (z::L) R)) (clear v n (z::L) R)
  rw [zeroPrefix] at h2
  exact join0 h2 (finish v L (rep [z] n++oneBlock v++R))

/-- Binary digits have unequal physical widths; the separator is v. -/
def encode (v : Bool) : List Bool → List Bool
  | [] => []
  | b::w => (if b then oneBlock v else zeroBlock v)++encode v w

def ones : List Bool → Nat
  | [] => 0
  | b::w => ones w + (if b then 1 else 0)

theorem encode_append (v : Bool) (a b : List Bool) : encode v (a++b) = encode v a++encode v b := by
  induction a with
  | nil => rfl
  | cons d a ih => simp only [List.cons_append,encode,ih,List.append_assoc]

theorem ones_append (a b : List Bool) : ones (a++b) = ones a+ones b := by
  induction a with
  | nil => simp [ones]
  | cons d a ih => simp only [List.cons_append,ones,ih]; omega

theorem ones_rep (k : Nat) : ones (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ,ones] using ih

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a++rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem zeros_encode (v : Bool) (k : Nat) : encode v (List.replicate k false) = rep [z] (d v*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,Nat.mul_succ, Nat.add_comm (d v*k) (d v),rep_add]
    simp only [encode,Bool.false_eq_true,ite_false,ih]
    cases v <;> rfl

abbrev marker : List Bool := [o,z,o,z,z]
def buffer (w : List Bool) : List Bool := rep [z] (ones w+3)++marker
abbrev family (v : Bool) (k : Nat) (w : List Bool) : Z0 := A (d v*k) (buffer w) (v::encode v w)

theorem carry_digit (v : Bool) (k : Nat) (w : List Bool) :
    run0 (table v) (d v*k+1+(d v*k+extra v+3)+1) (family v k (true::w)) = some (family v (k+1) w) := by
  have h := carry v (d v*k) (buffer w) (encode v w)
  simpa only [family,buffer,ones,ite_true,show ones w+1+3=(ones w+3)+1 by omega,rep,List.cons_append,List.nil_append,encode,Nat.mul_succ] using h

theorem reset_digit (v : Bool) (k : Nat) (w : List Bool) :
    run0 (table v) (d v*k+1+(d v*k+extra v+3)+4+(d v*k+d v+2)+13)
      (family v k (false::w)) = some (family v 0 (List.replicate k false++true::w)) := by
  have h := zero v (d v*k) (rep [z] (ones w+1)++marker) (encode v w)
  simpa only [family,buffer,ones_append,ones_rep,ones,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero,Nat.zero_add,Nat.mul_zero,encode_append,zeros_encode,encode,rep,List.cons_append,List.nil_append,List.append_assoc,show ones w+1+3=(ones w+1)+3 by rfl] using h

theorem word_step (v : Bool) (k : Nat) (w : List Bool) :
    ∃ n k' out, 0 < n ∧ run0 (table v) n (family v k (w++[false])) = some (family v k' out) := by
  cases he : w++[false] with
  | nil => simp at he
  | cons b t =>
    cases b with
    | false => exact ⟨_,0,List.replicate k false++true::t,by omega,reset_digit v k t⟩
    | true => exact ⟨_,k+1,t,by omega,carry_digit v k t⟩

theorem getD_pad (xs : List Bool) (n k : Nat) :
    (xs++List.replicate k false).getD n false = xs.getD n false := by
  induction xs generalizing n with
  | nil =>
    simp only [List.nil_append,List.getD_nil]
    induction k generalizing n with
    | zero => rfl
    | succ k ih => cases n <;> simp only [List.replicate_succ,List.getD_cons_zero,List.getD_cons_succ,ih]
  | cons b xs ih => cases n <;> simp only [List.cons_append,List.getD_cons_zero,List.getD_cons_succ,ih]

def reprZ (v : Bool) (h : Int) (k : Nat) (w : List Bool) : Z := ⟨0,h,(family v k w).l,(family v k w).r⟩

theorem pad_embed (v : Bool) (h : Int) (k : Nat) (w : List Bool) :
    embed (reprZ v h k (w++[false])) = embed (reprZ v h k w) := by
  unfold embed
  congr 1
  funext x
  unfold atCell reprZ
  simp only [family,A,buffer,ones_append,ones,Nat.add_zero,Bool.false_eq_true,ite_false,encode_append,encode,List.append_nil]
  have he : zeroBlock v = List.replicate (d v) false := by cases v <;> rfl
  rw [he]
  change (if x ≤ h then _ else ((v::encode v w)++List.replicate (d v) false).getD (x-h-1).toNat false) = _
  rw [getD_pad]

def Inv (v : Bool) (c : Config) : Prop := ∃ h k w, c = embed (reprZ v h k w)

theorem initial (v : Bool) : run0 (table v) 27 ⟨0,[],[]⟩ = some (family v 0 []) := by cases v <;> rfl

theorem inv_initial (v : Bool) (m : Machine) (hm : compatible (table v) m) :
    ∃ t, run m 27 blank = some t ∧ Inv v t := by
  have hz : (zrun (table v) 27 start).map project = some (family v 0 []) :=
    (run_project (table v) 27 start).trans (initial v)
  cases h : zrun (table v) 27 start with
  | none => simp [h] at hz
  | some t =>
    have ht : project t = family v 0 [] := by simpa only [h,Option.map_some,Option.some.injEq] using hz
    have H := zrun_sound (table v) m hm 27 start t h
    rw [start_embed] at H
    refine ⟨embed t,H,t.h,0,[],?_⟩
    cases t with
    | mk q h' l r =>
      simp only [project,family,A,Z0.mk.injEq] at ht
      obtain ⟨rfl,rfl,rfl⟩ := ht
      rfl

theorem inv_grow (v : Bool) (m : Machine) (hm : compatible (table v) m) {c : Config} (hc : Inv v c) :
    ∃ n t, 0 < n ∧ run m n c = some t ∧ Inv v t := by
  obtain ⟨h,k,w,rfl⟩ := hc
  obtain ⟨n,k',out,hn,hr⟩ := word_step v k w
  let u := reprZ v h k (w++[false])
  have hp : (zrun (table v) n u).map project = some (family v k' out) := (run_project (table v) n u).trans hr
  cases hz : zrun (table v) n u with
  | none => simp [hz] at hp
  | some t =>
    have ht : project t = family v k' out := by simpa only [hz,Option.map_some,Option.some.injEq] using hp
    have H := zrun_sound (table v) m hm n u t hz
    rw [show embed u = embed (reprZ v h k w) from pad_embed v h k w] at H
    refine ⟨n,embed t,hn,H,t.h,k',out,?_⟩
    cases t with
    | mk q h' l r =>
      simp only [project,family,A,Z0.mk.injEq] at ht
      obtain ⟨rfl,rfl,rfl⟩ := ht
      rfl

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ n t, k ≤ n ∧ run m n blank = some t ∧ Inv v t := by
    intro k
    induction k with
    | zero => obtain ⟨t,ht,hi⟩ := inv_initial v m hm; exact ⟨27,t,by omega,ht,hi⟩
    | succ k ih =>
      obtain ⟨n,t,hn,hr,hi⟩ := ih
      obtain ⟨j,u,hj,hs,hu⟩ := inv_grow v m hm hi
      exact ⟨n+j,u,by omega,by rw [run_append,hr]; exact hs,hu⟩
  intro n
  obtain ⟨k,t,hk,hr,_⟩ := arbitrary n
  rw [show k = n+(k-n) by omega,run_append] at hr
  cases h : run m n blank with
  | none => simp [h] at hr
  | some _ => rfl

#print axioms never
end BB6Coverage.Agent1Raw118BinaryCounter
