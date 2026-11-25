import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw118Radix4
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Row 4188 when false, row 4197 when true. -/
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => if v then some (some ⟨true,false,3⟩) else some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none
abbrev z : Bool := false
abbrev o : Bool := true
abbrev A (R : List Bool) : Z0 := ⟨0,[z,z,z],R⟩
abbrev U (k : Nat) (R : List Bool) : Z0 := ⟨0,z::(rep [o,o,o] k++[z,z]),R⟩

theorem carryOne (v : Bool) (L R : List Bool) :
    run0 (table v) 3 ⟨0,[z]++L,[z,o,z]++R⟩ = some ⟨0,[z]++[o,o,o]++L,R⟩ := by cases v <;> rfl

theorem carry (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k) (A (z::(rep [o,z,z] k++R))) = some (U k (z::R)) := by
  have hr : z::(rep [o,z,z] k++R) = rep [z,o,z] k++z::R := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [rep,List.cons_append,List.nil_append]
      exact congrArg (fun t => z::o::z::t) ih
  have h := sweepR (table v) 0 [z] [] [z,o,z] [o,o,o] 3
    (fun L R => by simpa only [List.nil_append] using carryOne v L R) k [z,z] (z::R)
  rw [hr]
  exact h

def turnCost (v : Bool) : Nat := if v then 10 else 12

def highCost (v : Bool) : Nat := if v then 11 else 13

theorem turn0 (v : Bool) (L R : List Bool) :
    run0 (table v) 6 ⟨0,z::L,z::z::z::z::R⟩ = some ⟨4,o::o::o::L,o::z::R⟩ := by cases v <;> rfl

theorem turn1 (v : Bool) (L R : List Bool) :
    run0 (table v) (turnCost v) ⟨0,z::L,z::z::o::z::R⟩ = some ⟨4,o::o::o::L,o::o::R⟩ := by cases v <;> rfl

theorem turn2 (v : Bool) (L R : List Bool) :
    run0 (table v) (highCost v) ⟨0,z::L,z::z::o::o::R⟩ = some ⟨4,o::o::L,o::z::z::R⟩ := by cases v <;> rfl

theorem clear3 (v : Bool) (L R : List Bool) :
    run0 (table v) 3 ⟨4,[o,o,o]++[o,o,o]++L,R⟩ = some ⟨4,[o,o,o]++L,[z,z,z]++R⟩ := by cases v <;> rfl

theorem clear2 (v : Bool) (L R : List Bool) :
    run0 (table v) 3 ⟨4,[o,o]++[o,o,o]++L,R⟩ = some ⟨4,[o,o]++L,[z,z,z]++R⟩ := by cases v <;> rfl

theorem back3 (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k) ⟨4,[o,o,o]++rep [o,o,o] k++[z,z],R⟩ =
      some ⟨4,[o,o,o,z,z],rep [z,z,z] k++R⟩ := by
  exact sweepL (table v) 4 [o,o,o] [] [o,o,o] [z,z,z] 3
    (fun L R => by simpa only [List.nil_append] using clear3 v L R) k [z,z] R

theorem back2 (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k) ⟨4,[o,o]++rep [o,o,o] k++[z,z],R⟩ =
      some ⟨4,[o,o,z,z],rep [z,z,z] k++R⟩ := by
  exact sweepL (table v) 4 [o,o] [] [o,o,o] [z,z,z] 3
    (fun L R => by simpa only [List.nil_append] using clear2 v L R) k [z,z] R

theorem finish3 (v : Bool) (R : List Bool) : run0 (table v) 6 ⟨4,[o,o,o,z,z],R⟩ = some (A (z::z::R)) := by cases v <;> rfl

theorem finish2 (v : Bool) (R : List Bool) : run0 (table v) 5 ⟨4,[o,o,z,z],R⟩ = some (A (z::R)) := by cases v <;> rfl

theorem zeros_commute (k : Nat) (R : List Bool) :
    z::(rep [z,z,z] k++R) = rep [z,z,z] k++z::R := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.cons_append,List.nil_append]
    exact congrArg (fun t => z::z::z::t) ih

theorem digit0 (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k+6+3*k+6) (A (z::(rep [o,z,z] k++[z,z,z]++R))) =
      some (A (z::(rep [z,z,z] k++[z,o,z]++R))) := by
  have h := join0 (join0 (join0 (carry v k ([z,z,z]++R)) (turn0 v (rep [o,o,o] k++[z,z]) R)) (back3 v k (o::z::R))) (finish3 v (rep [z,z,z] k++o::z::R))
  have hh := zeros_commute k (o::z::R)
  rw [hh] at h
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h

theorem digit1 (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k+turnCost v+3*k+6) (A (z::(rep [o,z,z] k++[z,o,z]++R))) =
      some (A (z::(rep [z,z,z] k++[z,o,o]++R))) := by
  have h := join0 (join0 (join0 (carry v k ([z,o,z]++R)) (turn1 v (rep [o,o,o] k++[z,z]) R)) (back3 v k (o::o::R))) (finish3 v (rep [z,z,z] k++o::o::R))
  have hh := zeros_commute k (o::o::R)
  rw [hh] at h
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h

theorem digit2 (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k+highCost v+3*k+5) (A (z::(rep [o,z,z] k++[z,o,o]++R))) =
      some (A (z::(rep [z,z,z] k++[o,z,z]++R))) := by
  have h := join0 (join0 (join0 (carry v k ([z,o,o]++R)) (turn2 v (rep [o,o,o] k++[z,z]) R)) (back2 v k (o::z::z::R))) (finish2 v (rep [z,z,z] k++o::z::z::R))
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h

inductive Digit where | d0 | d1 | d2 | d3 deriving DecidableEq
open Digit
def bits : Digit → List Bool
  | d0 => [z,z,z]
  | d1 => [z,o,z]
  | d2 => [z,o,o]
  | d3 => [o,z,z]
def encode : List Digit → List Bool
  | [] => []
  | d::w => bits d++encode w

theorem encode_append (a b : List Digit) : encode (a++b) = encode a++encode b := by
  induction a with
  | nil => rfl
  | cons d a ih => simp only [List.cons_append,encode,ih,List.append_assoc]

theorem encode_rep (d : Digit) (k : Nat) : encode (List.replicate k d) = rep (bits d) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,encode,rep,ih]

theorem decompose (w : List Digit) : ∃ k d t, w++[d0] = List.replicate k d3++d::t ∧ d ≠ d3 := by
  induction w with
  | nil => exact ⟨0,d0,[],rfl,by decide⟩
  | cons d w ih =>
    by_cases hd : d = d3
    · subst d
      obtain ⟨k,d,t,he,hn⟩ := ih
      exact ⟨k+1,d,t,by simp only [List.cons_append,List.replicate_succ]; rw [he],hn⟩
    · exact ⟨0,d,w++[d0],rfl,hd⟩

theorem word_step (v : Bool) (w : List Digit) :
    ∃ n out, 0 < n ∧ run0 (table v) n (A (z::encode (w++[d0]))) = some (A (z::encode out)) := by
  obtain ⟨k,d,t,he,hd⟩ := decompose w
  rw [he]
  cases d with
  | d0 =>
    refine ⟨3*k+6+3*k+6,List.replicate k d0++d1::t,by omega,?_⟩
    simpa only [encode_append,encode_rep,encode,bits,List.append_assoc] using digit0 v k (encode t)
  | d1 =>
    refine ⟨3*k+turnCost v+3*k+6,List.replicate k d0++d2::t,by omega,?_⟩
    simpa only [encode_append,encode_rep,encode,bits,List.append_assoc] using digit1 v k (encode t)
  | d2 =>
    refine ⟨3*k+highCost v+3*k+5,List.replicate k d0++d3::t,by omega,?_⟩
    simpa only [encode_append,encode_rep,encode,bits,List.append_assoc] using digit2 v k (encode t)
  | d3 => exact False.elim (hd rfl)

theorem getD_pad (xs : List Bool) (n k : Nat) :
    (xs++List.replicate k false).getD n false = xs.getD n false := by
  induction xs generalizing n with
  | nil =>
    simp only [List.nil_append,List.getD_nil]
    induction k generalizing n with
    | zero => rfl
    | succ k ih => cases n <;> simp only [List.replicate_succ,List.getD_cons_zero,List.getD_cons_succ,ih]
  | cons b xs ih => cases n <;> simp only [List.cons_append,List.getD_cons_zero,List.getD_cons_succ,ih]

def reprZ (h : Int) (w : List Digit) : Z := ⟨0,h,[z,z,z],z::encode w⟩
theorem pad_embed (h : Int) (w : List Digit) : embed (reprZ h (w++[d0])) = embed (reprZ h w) := by
  unfold embed
  congr 1
  funext x
  unfold atCell reprZ
  simp only
  rw [encode_append]
  change (if x ≤ h then [z,z,z].getD (h-x).toNat false
    else ((z::encode w)++List.replicate 3 false).getD (x-h-1).toNat false) = _
  rw [getD_pad]

theorem blank_repr : embed (reprZ 0 []) = blank := by
  unfold embed reprZ blank
  congr 1
  funext x
  unfold atCell
  simp only
  split
  · exact getD_pad [] _ 3
  · exact getD_pad [] _ 1

def Inv (c : Config) : Prop := ∃ h w, c = embed (reprZ h w)

theorem inv_grow (v : Bool) (m : Machine) (hm : compatible (table v) m) {c : Config} (hc : Inv c) :
    ∃ n t, 0 < n ∧ run m n c = some t ∧ Inv t := by
  obtain ⟨h,w,rfl⟩ := hc
  obtain ⟨n,out,hn,hr⟩ := word_step v w
  let u := reprZ h (w++[d0])
  have hp : (zrun (table v) n u).map project = some (A (z::encode out)) :=
    (run_project (table v) n u).trans hr
  cases hz : zrun (table v) n u with
  | none => simp [hz] at hp
  | some t =>
    have hv : project t = A (z::encode out) := by simpa only [hz,Option.map_some,Option.some.injEq] using hp
    have H := zrun_sound (table v) m hm n u t hz
    rw [show embed u = embed (reprZ h w) from pad_embed h w] at H
    refine ⟨n,embed t,hn,H,t.h,out,?_⟩
    cases t with
    | mk q h' l r =>
      simp only [project,A,Z0.mk.injEq] at hv
      obtain ⟨rfl,rfl,rfl⟩ := hv
      rfl

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ n t, k ≤ n ∧ run m n blank = some t ∧ Inv t := by
    intro k
    induction k with
    | zero => exact ⟨0,blank,by omega,rfl,0,[],blank_repr.symm⟩
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
end BB6Coverage.Agent1Raw118Radix4
