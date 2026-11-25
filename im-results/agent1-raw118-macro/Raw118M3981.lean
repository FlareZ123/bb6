import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw118M3981
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,3⟩)
  | _,_ => none

abbrev z : Bool := false
abbrev o : Bool := true
abbrev A (R : List Bool) : Z0 := ⟨0,[z,z,z],R⟩
abbrev B (k : Nat) (R : List Bool) : Z0 := ⟨1,z::(rep [z,o,o] k ++ [o,z,z]),R⟩
abbrev E (k : Nat) (R : List Bool) : Z0 := ⟨4,o::o::(rep [z,o,o] k ++ [o,z,z]),R⟩

theorem forwardOne (L R : List Bool) :
    run0 table 3 ⟨1,[z]++L,[o,z,z]++R⟩ = some ⟨1,[z]++[z,o,o]++L,R⟩ := by rfl

theorem forward (k : Nat) (R : List Bool) :
    run0 table (1+3*k) (A (rep [z,o,z] k ++ z::R)) = some (B k R) := by
  have hr : z::(rep [o,z,z] k ++ R) = rep [z,o,z] k ++ z::R := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [rep,List.cons_append,List.nil_append]
      exact congrArg (fun t => z::o::z::t) ih
  have h1 : run0 table 1 (A (z::(rep [o,z,z] k ++ R))) = some ⟨1,[z,o,z,z],rep [o,z,z] k++R⟩ := by rfl
  have h2 := sweepR table 1 [z] [] [o,z,z] [z,o,o] 3
    (fun L R => by simpa only [List.nil_append] using forwardOne L R) k [o,z,z] R
  have h := join0 h1 h2
  rw [hr] at h
  simpa only [B,List.singleton_append,List.nil_append,List.cons_append] using h

theorem backwardOne (L R : List Bool) :
    run0 table 5 ⟨4,[o,o]++[z,o,o]++L,R⟩ = some ⟨4,[o,o]++L,[o,z,z]++R⟩ := by rfl

theorem backward (k : Nat) (R : List Bool) :
    run0 table (5*k) (E k R) = some (E 0 (rep [o,z,z] k++R)) := by
  have h := sweepL table 4 [o,o] [] [z,o,o] [o,z,z] 5
    (fun L R => by simpa only [List.nil_append] using backwardOne L R) k [o,z,z] R
  simpa only [E,rep,List.nil_append,List.cons_append] using h

theorem finish (R : List Bool) : run0 table 6 (E 0 R) = some (A (z::z::R)) := by rfl

theorem turnZero (k : Nat) (R : List Bool) :
    run0 table 5 (B k (z::z::R)) = some (E k (o::R)) := by rfl

theorem turnLow (k : Nat) (R : List Bool) :
    run0 table 7 (B k (z::o::z::R)) = some (E k (o::o::R)) := by rfl

theorem turnHighBase (R : List Bool) :
    run0 table 13 (B 0 (z::o::o::R)) = some (A (z::o::z::z::R)) := by rfl

theorem turnHigh (k : Nat) (R : List Bool) :
    run0 table 10 (B (k+1) (z::o::o::R)) = some (E k (z::o::o::z::z::R)) := by rfl

/-- Carry the two fixed low bits through the backward sweep. -/
theorem rotateTwo (k : Nat) (R : List Bool) :
    z::z::(rep [o,z,z] k ++ R) = rep [z,z,o] k ++ z::z::R := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.cons_append,List.nil_append]
    exact congrArg (fun t => z::z::o::t) ih

theorem macroZero (k : Nat) (R : List Bool) :
    run0 table (1+3*k+5+5*k+6) (A (rep [z,o,z] k ++ z::z::z::R)) =
      some (A (rep [z,z,o] (k+1) ++ R)) := by
  have h := join0 (join0 (join0 (forward k (z::z::R)) (turnZero k R)) (backward k (o::R))) (finish (rep [o,z,z] k ++ o::R))
  rw [rotateTwo] at h
  have he : rep [z,z,o] k ++ z::z::o::R = rep [z,z,o] (k+1) ++ R := by
    have hs := congrArg (· ++ R) (rep_snoc [z,z,o] k)
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using hs
  rw [he] at h
  exact h

theorem macroLow (k : Nat) (R : List Bool) :
    run0 table (1+3*k+7+5*k+6) (A (rep [z,o,z] k ++ z::z::o::z::R)) =
      some (A (rep [z,z,o] (k+1) ++ o::R)) := by
  have h := join0 (join0 (join0 (forward k (z::o::z::R)) (turnLow k R)) (backward k (o::o::R))) (finish (rep [o,z,z] k ++ o::o::R))
  rw [rotateTwo] at h
  have he : rep [z,z,o] k ++ z::z::o::o::R = rep [z,z,o] (k+1) ++ o::R := by
    have hs := congrArg (· ++ o::R) (rep_snoc [z,z,o] k)
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using hs
  rw [he] at h
  exact h

theorem macroHighBase (R : List Bool) :
    run0 table 14 (A (z::z::o::o::R)) = some (A (z::o::z::z::R)) :=
  join0 (forward 0 (z::o::o::R)) (turnHighBase R)

theorem macroHigh (k : Nat) (R : List Bool) :
    run0 table (1+3*(k+1)+10+5*k+6) (A (rep [z,o,z] (k+1) ++ z::z::o::o::R)) =
      some (A (rep [z,z,o] k ++ z::z::z::o::o::z::z::R)) := by
  have h := join0 (join0 (join0 (forward (k+1) (z::o::o::R)) (turnHigh k R)) (backward k (z::o::o::z::z::R))) (finish (rep [o,z,z] k ++ z::o::o::z::z::R))
  rw [rotateTwo] at h
  exact h

#print axioms macroZero
#print axioms macroLow
#print axioms macroHighBase
#print axioms macroHigh

/-- The six three-bit blocks occurring in the invariant language. The first
    bit is an overlap/carry flag, while the last two specify a local digit. -/
inductive Digit where
  | g000 | g001 | g010 | g100 | g101 | g110
  deriving DecidableEq, Repr
open Digit

def digitBits : Digit → List Bool
  | g000 => [z,z,z]
  | g001 => [z,z,o]
  | g010 => [z,o,z]
  | g100 => [o,z,z]
  | g101 => [o,z,o]
  | g110 => [o,o,z]

def encode : List Digit → List Bool
  | [] => []
  | d::t => digitBits d ++ encode t

/-- The predecessor groups 000/100 have the same successors, as do
    001/101 and 010/110. The initial virtual predecessor is 010. -/
def allowed : Digit → Digit → Prop
  | g000, d | g100, d => d = g000 ∨ d = g110
  | g001, d | g101, d => d ≠ g010
  | g010, d | g110, d => d = g000 ∨ d = g001 ∨ d = g010

instance (a b : Digit) : Decidable (allowed a b) := by
  cases a <;> unfold allowed <;> infer_instance

def chain : Digit → List Digit → Prop
  | _, [] => True
  | d, e::t => allowed d e ∧ chain e t

abbrev Safe (w : List Digit) : Prop := chain g010 w

theorem encode_append (w t : List Digit) : encode (w++t) = encode w ++ encode t := by
  induction w with
  | nil => rfl
  | cons d w ih => simp only [List.cons_append,encode,ih,List.append_assoc]

theorem encode_rep (d : Digit) (k : Nat) :
    encode (List.replicate k d) = rep (digitBits d) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,encode,ih,rep]

theorem safe_carry (k : Nat) (w : List Digit) :
    Safe (List.replicate k g010 ++ w) ↔ Safe w := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ,List.cons_append,Safe,chain,allowed,or_true,true_and] using ih

theorem safe_ones (k : Nat) (w : List Digit) (h : chain g001 w) :
    Safe (List.replicate (k+1) g001 ++ w) := by
  have aux : ∀ j, chain g001 (List.replicate j g001 ++ w) := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih => exact ⟨by decide,ih⟩
  exact ⟨by decide,aux k⟩

theorem safe_zero (k : Nat) (w : List Digit) (h : Safe (g000::w)) :
    Safe (List.replicate (k+1) g001 ++ w) := by
  apply safe_ones
  cases w with
  | nil => trivial
  | cons d w =>
    obtain ⟨_,hh,ht⟩ := h
    exact ⟨by rcases hh with rfl|rfl <;> decide,ht⟩

theorem chain_flag0 (w : List Digit) : chain g000 w ↔ chain g100 w := by cases w <;> rfl
theorem chain_flag1 (w : List Digit) : chain g001 w ↔ chain g101 w := by cases w <;> rfl
theorem chain_flag2 (w : List Digit) : chain g010 w ↔ chain g110 w := by cases w <;> rfl

theorem safe_high (k : Nat) (e : Digit) (w : List Digit) (he : allowed g110 e) (ht : chain e w) :
    Safe (List.replicate k g001 ++ g000::g110::e::w) := by
  cases k with
  | zero => exact ⟨by decide,by decide,he,ht⟩
  | succ k => apply safe_ones; exact ⟨by decide,by decide,he,ht⟩

/-- Every non-carry digit and its next digit admit a positive-cost macro
    that preserves the block language. The grammar, rather than a finite
    trajectory, closes every carry length and every valid suffix. -/
theorem word_step (k : Nat) (d e : Digit) (w : List Digit)
    (hd : d ≠ g010) (hs : Safe (d::e::w)) :
    ∃ n out, 0 < n ∧ Safe out ∧
      run0 table n (A (encode (List.replicate k g010 ++ d::e::w))) = some (A (encode out)) := by
  cases d with
  | g000 =>
    refine ⟨1+3*k+5+5*k+6,List.replicate (k+1) g001 ++ e::w,by omega,safe_zero k _ hs,?_⟩
    simpa only [encode_append,encode_rep,encode,digitBits,List.cons_append,List.nil_append] using macroZero k (encode (e::w))
  | g001 =>
    obtain ⟨_,he,ht⟩ := hs
    cases e with
    | g000 =>
      refine ⟨1+3*k+7+5*k+6,List.replicate (k+1) g001 ++ g100::w,by omega,safe_ones k _ ⟨by decide,(chain_flag0 w).mp ht⟩,?_⟩
      simpa only [encode_append,encode_rep,encode,digitBits,List.cons_append,List.nil_append] using macroLow k (z::z::encode w)
    | g001 =>
      refine ⟨1+3*k+7+5*k+6,List.replicate (k+1) g001 ++ g101::w,by omega,safe_ones k _ ⟨by decide,(chain_flag1 w).mp ht⟩,?_⟩
      simpa only [encode_append,encode_rep,encode,digitBits,List.cons_append,List.nil_append] using macroLow k (z::o::encode w)
    | g010 => exact False.elim (he rfl)
    | g100 =>
      have ht' := (chain_flag0 w).mpr ht
      cases k with
      | zero =>
        refine ⟨14,g010::g000::w,by decide,⟨by decide,by decide,ht'⟩,?_⟩
        simpa only [List.replicate_zero,List.nil_append,encode,digitBits,List.cons_append] using macroHighBase (z::z::encode w)
      | succ k =>
        refine ⟨1+3*(k+1)+10+5*k+6,List.replicate k g001 ++ g000::g110::g000::w,by omega,safe_high k _ _ (by decide) ht',?_⟩
        simpa only [encode_append,encode_rep,encode,digitBits,List.cons_append,List.nil_append] using macroHigh k (z::z::encode w)
    | g101 =>
      have ht' := (chain_flag1 w).mpr ht
      cases k with
      | zero =>
        refine ⟨14,g010::g001::w,by decide,⟨by decide,by decide,ht'⟩,?_⟩
        simpa only [List.replicate_zero,List.nil_append,encode,digitBits,List.cons_append] using macroHighBase (z::o::encode w)
      | succ k =>
        refine ⟨1+3*(k+1)+10+5*k+6,List.replicate k g001 ++ g000::g110::g001::w,by omega,safe_high k _ _ (by decide) ht',?_⟩
        simpa only [encode_append,encode_rep,encode,digitBits,List.cons_append,List.nil_append] using macroHigh k (z::o::encode w)
    | g110 =>
      have ht' := (chain_flag2 w).mpr ht
      cases k with
      | zero =>
        refine ⟨14,g010::g010::w,by decide,⟨by decide,by decide,ht'⟩,?_⟩
        simpa only [List.replicate_zero,List.nil_append,encode,digitBits,List.cons_append] using macroHighBase (o::z::encode w)
      | succ k =>
        refine ⟨1+3*(k+1)+10+5*k+6,List.replicate k g001 ++ g000::g110::g010::w,by omega,safe_high k _ _ (by decide) ht',?_⟩
        simpa only [encode_append,encode_rep,encode,digitBits,List.cons_append,List.nil_append] using macroHigh k (o::z::encode w)
  | g010 => exact False.elim (hd rfl)
  | g100 => exact False.elim ((by decide : ¬ allowed g010 g100) hs.1)
  | g101 => exact False.elim ((by decide : ¬ allowed g010 g101) hs.1)
  | g110 => exact False.elim ((by decide : ¬ allowed g010 g110) hs.1)

#print axioms word_step

theorem chain_pad (d : Digit) (w : List Digit) (hw : chain d w) :
    chain d (w++[g000,g000]) := by
  induction w generalizing d with
  | nil => cases d <;> exact ⟨by decide,by decide,trivial⟩
  | cons e w ih => exact ⟨hw.1,ih e hw.2⟩

theorem carry_decompose (w : List Digit) :
    ∃ k d e t, w++[g000,g000] = List.replicate k g010 ++ d::e::t ∧ d ≠ g010 := by
  induction w with
  | nil => exact ⟨0,g000,g000,[],rfl,by decide⟩
  | cons d w ih =>
    by_cases hd : d = g010
    · subst d
      obtain ⟨k,d,e,t,he,hn⟩ := ih
      exact ⟨k+1,d,e,t,by simp only [List.cons_append,List.replicate_succ]; rw [he],hn⟩
    · cases w with
      | nil => exact ⟨0,d,g000,[g000],rfl,hd⟩
      | cons e w => exact ⟨0,d,e,w++[g000,g000],rfl,hd⟩

theorem padded_word_step (w : List Digit) (hw : Safe w) :
    ∃ n out, 0 < n ∧ Safe out ∧
      run0 table n (A (encode (w++[g000,g000]))) = some (A (encode out)) := by
  obtain ⟨k,d,e,t,he,hd⟩ := carry_decompose w
  have hs : Safe (w++[g000,g000]) := chain_pad g010 w hw
  rw [he] at hs ⊢
  exact word_step k d e t hd ((safe_carry k _).mp hs)

/-- Padding the finite right stack by six blank bits changes no tape cell. -/
theorem getD_pad (xs : List Bool) (n k : Nat) :
    (xs++List.replicate k false).getD n false = xs.getD n false := by
  induction xs generalizing n with
  | nil =>
    simp only [List.nil_append,List.getD_nil]
    induction k generalizing n with
    | zero => rfl
    | succ k ih => cases n <;> simp only [List.replicate_succ,List.getD_cons_zero,List.getD_cons_succ,ih]
  | cons b xs ih => cases n <;> simp only [List.cons_append,List.getD_cons_zero,List.getD_cons_succ,ih]

def reprZ (h : Int) (w : List Digit) : Z := ⟨0,h,[z,z,z],encode w⟩

theorem pad_embed (h : Int) (w : List Digit) :
    embed (reprZ h (w++[g000,g000])) = embed (reprZ h w) := by
  unfold embed
  congr 1
  funext x
  unfold atCell reprZ
  simp only
  rw [encode_append]
  change (if x ≤ h then [z,z,z].getD (h-x).toNat false
    else (encode w++List.replicate 6 false).getD (x-h-1).toNat false) = _
  rw [getD_pad]

theorem blank_repr : embed (reprZ 0 []) = blank := by
  unfold embed reprZ blank
  congr 1
  funext x
  unfold atCell
  simp only
  split
  · exact getD_pad [] _ 3
  · rfl

def Inv (c : Config) : Prop := ∃ h w, Safe w ∧ c = embed (reprZ h w)

theorem inv_blank : Inv blank := ⟨0,[],trivial,blank_repr.symm⟩

theorem inv_grow (m : Machine) (hm : compatible table m) {c : Config} (hc : Inv c) :
    ∃ n t, 0 < n ∧ run m n c = some t ∧ Inv t := by
  obtain ⟨h,w,hw,rfl⟩ := hc
  obtain ⟨n,out,hn,ho,hr⟩ := padded_word_step w hw
  let u := reprZ h (w++[g000,g000])
  have hp : (zrun table n u).map project = some (A (encode out)) :=
    (run_project table n u).trans hr
  cases hz : zrun table n u with
  | none => simp [hz] at hp
  | some v =>
    have hv : project v = A (encode out) := by simpa only [hz,Option.map_some,Option.some.injEq] using hp
    have H := zrun_sound table m hm n u v hz
    rw [show embed u = embed (reprZ h w) from pad_embed h w] at H
    refine ⟨n,embed v,hn,H,v.h,out,ho,?_⟩
    cases v with
    | mk q h' l r =>
      simp only [project,A,Z0.mk.injEq] at hv
      obtain ⟨rfl,rfl,rfl⟩ := hv
      rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ n t, k ≤ n ∧ run m n blank = some t ∧ Inv t := by
    intro k
    induction k with
    | zero => exact ⟨0,blank,by omega,rfl,inv_blank⟩
    | succ k ih =>
      obtain ⟨n,t,hn,hr,hi⟩ := ih
      obtain ⟨j,u,hj,hs,hu⟩ := inv_grow m hm hi
      exact ⟨n+j,u,by omega,by rw [run_append,hr]; exact hs,hu⟩
  intro n
  obtain ⟨k,t,hk,hr,_⟩ := arbitrary n
  rw [show k = n+(k-n) by omega,run_append] at hr
  cases h : run m n blank with
  | none => simp [h] at hr
  | some _ => rfl

#print axioms padded_word_step
#print axioms inv_grow
#print axioms never
end BB6Coverage.Agent1Raw118M3981
