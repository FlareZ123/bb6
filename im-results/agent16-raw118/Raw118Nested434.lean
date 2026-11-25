import RecursiveCounterCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent16Raw118Nested.M434
open BB6Coverage Agent31Pump Agent40Recursive Agent50Zipper

-- 1RB0RB_1RC---_0RD1RA_1LD1RE_0LF0LE_1RF0RC
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev z : Bool := false
abbrev o : Bool := true
def O (n : Nat) := List.replicate n true
def ZerosBits (n : Nat) := List.replicate n false
def blocks (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ blocks w n
abbrev lo : List Bool := [z,o,o]
abbrev hi : List Bool := [o,o,z]

theorem blocks_snoc (w : List Bool) (k : Nat) : blocks w k ++ w = blocks w (k+1) := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => simp only [blocks,List.append_assoc,ih]

theorem rotate (k : Nat) (R : List Bool) : z::(blocks hi k ++ R) = blocks lo k ++ z::R := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [blocks,List.cons_append,List.nil_append] using congrArg (fun x => z::o::o::x) ih

theorem O_snoc (k : Nat) (L : List Bool) : O k ++ o::L = O (k+1) ++ L := by
  unfold O; rw [←List.replicate_append_replicate (n:=k) (m:=1)]; simp

theorem Z_snoc (k : Nat) (L : List Bool) : ZerosBits k ++ z::L = ZerosBits (k+1) ++ L := by
  unfold ZerosBits; rw [←List.replicate_append_replicate (n:=k) (m:=1)]; simp

def B (n k : Nat) (R : List Bool) : Z0 := ⟨1,z::(blocks lo k ++ [o,o,z] ++ O (n+2)),R⟩
def F (n k : Nat) (R : List Bool) : Z0 := ⟨5,o::o::(blocks lo k ++ [o,o,z] ++ O (n+2)),z::z::z::R⟩
def Tail (n : Nat) (R : List Bool) : Z0 := ⟨5,O (n+2),z::z::z::z::R⟩

theorem carryOne (n k : Nat) (R : List Bool) : run0 table 3 (B n k (o::o::z::R)) = some (B n (k+1) R) := by rfl

theorem carry (n k j : Nat) (R : List Bool) : run0 table (3*k) (B n j (blocks hi k ++ R)) = some (B n (k+j) R) := by
  induction k generalizing j with
  | zero => simp [blocks,run0]
  | succ k ih =>
    have h := join0 (carryOne n j (blocks hi k ++ R)) (ih (j+1))
    simpa only [blocks,List.append_assoc,List.cons_append,List.nil_append,Nat.mul_succ,show 3+3*k=3*k+3 by omega,show k+(j+1)=k+1+j by omega] using h

theorem backOne (n k : Nat) (R : List Bool) : run0 table 9 (F n (k+1) R) = some (F n k (o::o::z::R)) := by rfl

theorem back (n k : Nat) (R : List Bool) : run0 table (9*k) (F n k R) = some (F n 0 (blocks hi k ++ R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (backOne n k R) (ih (o::o::z::R))
    have eq : blocks hi k ++ o::o::z::R = blocks hi (k+1) ++ R := by
      rw [←blocks_snoc hi k]; simp [List.append_assoc]
    rw [eq] at h
    simpa only [Nat.mul_succ,show 9+9*k=9*k+9 by omega] using h

theorem backBase (n : Nat) (R : List Bool) : run0 table 11 (F n 0 R) = some (Tail n (z::o::o::z::R)) := by rfl

theorem ewalk (k : Nat) (R : List Bool) : run0 table k ⟨4,O k,R⟩ = some ⟨4,[],ZerosBits k ++ R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 ⟨4,O (k+1),R⟩ = some ⟨4,O k,z::R⟩ := by rfl
    have hh := join0 h (ih (z::R))
    rw [Z_snoc] at hh
    simpa only [Nat.add_comm 1 k] using hh

theorem fwalk (k : Nat) (L R : List Bool) : run0 table (k+1) ⟨5,z::L,ZerosBits k ++ o::R⟩ = some ⟨5,o::(O (k+1) ++ L),R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 ⟨5,z::L,ZerosBits (k+1) ++ o::R⟩ = some ⟨5,z::o::L,ZerosBits k ++ o::R⟩ := by rfl
    have hh := join0 h (ih (o::L))
    rw [O_snoc] at hh
    simpa only [Nat.add_comm 1 (k+1)] using hh

theorem tailFinish (n : Nat) (R : List Bool) : PositiveRun table (Tail n R) (B (n+2) 0 R) := by
  have h1 : run0 table 6 (Tail n R) = some ⟨4,O (n+2),o::o::z::z::R⟩ := by rfl
  have h2 := ewalk (n+2) (o::o::z::z::R)
  have h3 : run0 table 2 ⟨4,[],ZerosBits (n+2) ++ o::o::z::z::R⟩ = some ⟨5,z::[o],ZerosBits (n+2) ++ o::o::z::z::R⟩ := by rfl
  have h4 := fwalk (n+2) [o] (o::z::z::R)
  rw [O_snoc,List.append_nil,show n+2+1+1=n+4 by omega] at h4
  have h5 : run0 table 3 ⟨5,o::O (n+4),o::z::z::R⟩ = some (B (n+2) 0 R) := by rfl
  exact ⟨6+(n+2)+2+(n+2+1)+3,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩

theorem backFinish (n k : Nat) (R : List Bool) : PositiveRun table (F n k R) (B (n+2) 0 (blocks lo (k+1) ++ z::R)) := by
  have h := join0 (back n k R) (backBase n (blocks hi k ++ R))
  obtain ⟨j,hj,hr⟩ := tailFinish n (z::o::o::z::(blocks hi k ++ R))
  have eq : z::o::o::z::(blocks hi k ++ R) = blocks lo (k+1) ++ z::R := by
    simpa only [blocks,List.cons_append,List.nil_append] using congrArg (fun x => z::o::o::x) (rotate k R)
  rw [eq] at h
  rw [eq] at hr
  exact ⟨9*k+11+j,by omega,join0 h hr⟩

theorem zeroBase (n : Nat) (x : Bool) (R : List Bool) : run0 table 10 (B n 0 (z::z::x::R)) = some (Tail n (z::o::x::R)) := by rfl
theorem zeroMore (n k : Nat) (x : Bool) (R : List Bool) : run0 table 8 (B n (k+1) (z::z::x::R)) = some (F n k (o::x::R)) := by rfl
theorem lowBase (n : Nat) (R : List Bool) : run0 table 16 (B n 0 (z::o::z::z::R)) = some (Tail n (z::o::o::o::R)) := by rfl
theorem lowMore (n k : Nat) (R : List Bool) : run0 table 14 (B n (k+1) (z::o::z::z::R)) = some (F n k (o::o::o::R)) := by rfl
theorem highBase (n : Nat) (R : List Bool) : run0 table 16 (B n 0 (z::o::o::R)) = some (Tail n (o::o::z::R)) := by rfl
theorem highOne (n : Nat) (R : List Bool) : run0 table 19 (B n 1 (z::o::o::R)) = some (Tail n (z::z::o::o::o::z::R)) := by rfl
theorem highMore (n k : Nat) (R : List Bool) : run0 table 17 (B n (k+2) (z::o::o::R)) = some (F n k (z::o::o::o::z::R)) := by rfl
theorem spillBase (n : Nat) (R : List Bool) : run0 table 16 (B n 0 (o::z::z::z::z::z::R)) = some (Tail n (z::z::z::z::o::z::R)) := by rfl
theorem spillMore (n k : Nat) (R : List Bool) : run0 table 14 (B n (k+1) (o::z::z::z::z::z::R)) = some (F n k (z::z::z::o::z::R)) := by rfl

theorem zeroAfter (n k : Nat) (x : Bool) (R : List Bool) : PositiveRun table (B n k (z::z::x::R)) (B (n+2) 0 (blocks lo k ++ z::o::x::R)) := by
  cases k with
  | zero => exact (show PositiveRun table _ _ from ⟨10,by decide,zeroBase n x R⟩).trans (tailFinish n _)
  | succ k => exact (show PositiveRun table _ _ from ⟨8,by decide,zeroMore n k x R⟩).trans (backFinish n k _)

theorem lowAfter (n k : Nat) (R : List Bool) : PositiveRun table (B n k (z::o::z::z::R)) (B (n+2) 0 (blocks lo k ++ z::o::o::o::R)) := by
  cases k with
  | zero => exact (show PositiveRun table _ _ from ⟨16,by decide,lowBase n R⟩).trans (tailFinish n _)
  | succ k => exact (show PositiveRun table _ _ from ⟨14,by decide,lowMore n k R⟩).trans (backFinish n k _)

theorem highAfter0 (n : Nat) (R : List Bool) : PositiveRun table (B n 0 (z::o::o::R)) (B (n+2) 0 (o::o::z::R)) :=
  (show PositiveRun table _ _ from ⟨16,by decide,highBase n R⟩).trans (tailFinish n _)
theorem highAfter (n k : Nat) (R : List Bool) : PositiveRun table (B n (k+1) (z::o::o::R)) (B (n+2) 0 (blocks lo k ++ z::z::o::o::o::z::R)) := by
  cases k with
  | zero => exact (show PositiveRun table _ _ from ⟨19,by decide,highOne n R⟩).trans (tailFinish n _)
  | succ k => exact (show PositiveRun table _ _ from ⟨17,by decide,highMore n k R⟩).trans (backFinish n k _)

theorem spillAfter (n k : Nat) (R : List Bool) : PositiveRun table (B n k (o::z::z::z::z::z::R)) (B (n+2) 0 (blocks lo k ++ z::z::z::z::o::z::R)) := by
  cases k with
  | zero => exact (show PositiveRun table _ _ from ⟨16,by decide,spillBase n R⟩).trans (tailFinish n _)
  | succ k => exact (show PositiveRun table _ _ from ⟨14,by decide,spillMore n k R⟩).trans (backFinish n k _)

theorem macroRun (n k : Nat) (R S : List Bool) (h : PositiveRun table (B n k R) (B (n+2) 0 S)) : PositiveRun table (B n 0 (blocks hi k ++ R)) (B (n+2) 0 S) := by
  obtain ⟨j,hj,hr⟩ := h
  have hc := carry n k 0 R
  rw [Nat.add_zero] at hc
  exact ⟨3*k+j,by omega,join0 hc hr⟩

inductive Digit where
  | g000 | g001 | g010 | g011 | g100 | g110
  deriving DecidableEq, Repr
open Digit

def bits : Digit → List Bool
  | g000 => [z,z,z]
  | g001 => [z,z,o]
  | g010 => [z,o,z]
  | g011 => [z,o,o]
  | g100 => [o,z,z]
  | g110 => [o,o,z]
def encode : List Digit → List Bool
  | [] => []
  | d::w => bits d ++ encode w

inductive Zeros : List Digit → Prop where
  | nil : Zeros []
  | cons : Zeros w → Zeros (g000::w)
inductive Tens : List Digit → Prop where
  | zero : Zeros w → Tens w
  | ten : Tens w → Tens (g010::w)
inductive Safe : List Digit → Prop where
  | nil : Safe []
  | low0 : Tens w → Safe (g000::w)
  | low2 : Tens w → Safe (g010::w)
  | spill : Zeros w → Safe (g100::w)
  | high : Safe w → Safe (g011::w)
  | carry : Safe w → Safe (g110::w)
  | pair : Safe w → Safe (g001::g110::w)

theorem zerosSafe {w} (h : Zeros w) : Safe w := by
  cases h with
  | nil => exact .nil
  | cons h => exact .low0 (.zero h)
theorem tensSafe {w} (h : Tens w) : Safe w := by
  cases h with
  | zero h => exact zerosSafe h
  | ten h => exact .low2 h

theorem zerosPad {w} (h : Zeros w) : Zeros (w++[g000,g000]) := by
  induction h with
  | nil => exact .cons (.cons .nil)
  | cons h ih => exact .cons ih
theorem tensPad {w} (h : Tens w) : Tens (w++[g000,g000]) := by
  induction h with
  | zero h => exact .zero (zerosPad h)
  | ten h ih => exact .ten ih
theorem safePad {w} (h : Safe w) : Safe (w++[g000,g000]) := by
  induction h with
  | nil => exact .low0 (.zero (.cons .nil))
  | low0 h => exact .low0 (tensPad h)
  | low2 h => exact .low2 (tensPad h)
  | spill h => exact .spill (zerosPad h)
  | high h ih => exact .high ih
  | carry h ih => exact .carry ih
  | pair h ih => exact .pair ih

theorem safeCarry (k : Nat) (w : List Digit) : Safe (List.replicate k g110 ++ w) → Safe w := by
  induction k with
  | zero => exact id
  | succ k ih => intro h; cases h with | carry h => exact ih h
theorem safePrefix (k : Nat) (w : List Digit) (h : Safe w) : Safe (List.replicate k g011 ++ w) := by
  induction k with
  | zero => exact h
  | succ k ih => exact .high ih

theorem encode_append (w v : List Digit) : encode (w++v) = encode w ++ encode v := by
  induction w with
  | nil => rfl
  | cons d w ih => simp only [List.cons_append,encode,ih,List.append_assoc]
theorem encode_rep (d : Digit) (k : Nat) : encode (List.replicate k d) = blocks (bits d) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,encode,ih,blocks]

/-- Complete digit rewrite, including every carry length and every allowed suffix. -/
theorem wordStep (n k : Nat) (d e : Digit) (w : List Digit) (hd : d ≠ g110) (hs : Safe (d::e::w)) :
    ∃ out, Safe out ∧ PositiveRun table (B n 0 (encode (List.replicate k g110 ++ d::e::w))) (B (n+2) 0 (encode out)) := by
  cases d with
  | g000 =>
    have ht : Tens (e::w) := by cases hs with | low0 h => exact h
    refine ⟨List.replicate k g011 ++ g010::e::w,safePrefix k _ (.low2 ht),?_⟩
    simpa only [encode_append,encode_rep,encode,bits,List.cons_append,List.nil_append] using macroRun n k _ _ (zeroAfter n k z (encode (e::w)))
  | g001 =>
    have ht : Safe (e::w) := by cases hs with | pair h => exact .carry h
    refine ⟨List.replicate k g011 ++ g011::e::w,safePrefix k _ (.high ht),?_⟩
    simpa only [encode_append,encode_rep,encode,bits,List.cons_append,List.nil_append] using macroRun n k _ _ (zeroAfter n k o (encode (e::w)))
  | g010 =>
    have ht : Tens (e::w) := by cases hs with | low2 h => exact h
    cases ht with
    | zero hz =>
      cases hz with
      | cons hz =>
        refine ⟨List.replicate k g011 ++ g011::g100::w,safePrefix k _ (.high (.spill hz)),?_⟩
        simpa only [encode_append,encode_rep,encode,bits,List.cons_append,List.nil_append] using macroRun n k _ _ (lowAfter n k (z::z::encode w))
    | ten ht =>
      refine ⟨List.replicate k g011 ++ g011::g110::w,safePrefix k _ (.high (.carry (tensSafe ht))),?_⟩
      simpa only [encode_append,encode_rep,encode,bits,List.cons_append,List.nil_append] using macroRun n k _ _ (lowAfter n k (o::z::encode w))
  | g011 =>
    have ht : Safe (e::w) := by cases hs with | high h => exact h
    cases k with
    | zero =>
      refine ⟨g110::e::w,.carry ht,?_⟩
      simpa only [List.replicate_zero,List.nil_append,encode,bits,List.cons_append,List.nil_append] using highAfter0 n (encode (e::w))
    | succ k =>
      refine ⟨List.replicate k g011 ++ g001::g110::e::w,safePrefix k _ (.pair ht),?_⟩
      simpa only [encode_append,encode_rep,encode,bits,List.cons_append,List.nil_append] using macroRun n (k+1) _ _ (highAfter n k (encode (e::w)))
  | g100 =>
    have hz : Zeros (e::w) := by cases hs with | spill h => exact h
    cases hz with
    | cons hz =>
      refine ⟨List.replicate k g011 ++ g000::g010::w,safePrefix k _ (.low0 (.ten (.zero hz))),?_⟩
      simpa only [encode_append,encode_rep,encode,bits,List.cons_append,List.nil_append] using macroRun n k _ _ (spillAfter n k (encode w))
  | g110 => exact False.elim (hd rfl)

theorem carryDecompose (w : List Digit) : ∃ k d e t, w++[g000,g000] = List.replicate k g110 ++ d::e::t ∧ d ≠ g110 := by
  induction w with
  | nil => exact ⟨0,g000,g000,[],rfl,by decide⟩
  | cons d w ih =>
    by_cases hd : d = g110
    · subst d
      obtain ⟨k,d,e,t,he,hn⟩ := ih
      exact ⟨k+1,d,e,t,by simp only [List.cons_append,List.replicate_succ]; rw [he],hn⟩
    · cases w with
      | nil => exact ⟨0,d,g000,[g000],rfl,hd⟩
      | cons e w => exact ⟨0,d,e,w++[g000,g000],rfl,hd⟩

theorem paddedWordStep (n : Nat) (w : List Digit) (h : Safe w) : ∃ out, Safe out ∧ PositiveRun table (B n 0 (encode (w++[g000,g000]))) (B (n+2) 0 (encode out)) := by
  obtain ⟨k,d,e,t,he,hd⟩ := carryDecompose w
  have hs := safePad h
  rw [he] at hs ⊢
  exact wordStep n k d e t hd (safeCarry k _ hs)

theorem blankEntry : run0 table 39 ⟨0,[],[]⟩ = some (B 6 0 []) := by rfl

theorem getD_pad (xs : List Bool) (n k : Nat) :
    (xs++List.replicate k false).getD n false = xs.getD n false := by
  induction xs generalizing n with
  | nil =>
    simp only [List.nil_append,List.getD_nil]
    induction k generalizing n with
    | zero => rfl
    | succ k ih => cases n <;> simp only [List.replicate_succ,List.getD_cons_zero,List.getD_cons_succ,ih]
  | cons b xs ih => cases n <;> simp only [List.cons_append,List.getD_cons_zero,List.getD_cons_succ,ih]

def reprZ (h : Int) (n : Nat) (w : List Digit) : Agent50Zipper.Z :=
  ⟨1,h,(B n 0 []).l,encode w⟩

theorem pad_embed (h : Int) (n : Nat) (w : List Digit) :
    embed (reprZ h n (w++[g000,g000])) = embed (reprZ h n w) := by
  unfold embed
  congr 1
  funext x
  unfold atCell reprZ
  simp only
  rw [encode_append]
  change (if x ≤ h then (B n 0 []).l.getD (h-x).toNat false
    else (encode w++List.replicate 6 false).getD (x-h-1).toNat false) = _
  rw [getD_pad]

def Inv (c : Config) : Prop := ∃ h n w, Safe w ∧ c = embed (reprZ h n w)

theorem inv_grow (m : Machine) (hm : compatible table m) {c : Config} (hc : Inv c) :
    ∃ k t, 0 < k ∧ run m k c = some t ∧ Inv t := by
  obtain ⟨h,n,w,hw,rfl⟩ := hc
  obtain ⟨out,ho,k,hk,hr⟩ := paddedWordStep n w hw
  let u := reprZ h n (w++[g000,g000])
  have hp : (zrun table k u).map project = some (B (n+2) 0 (encode out)) :=
    (run_project table k u).trans hr
  cases hz : zrun table k u with
  | none => simp [hz] at hp
  | some v =>
    have hv : project v = B (n+2) 0 (encode out) := by simpa only [hz,Option.map_some,Option.some.injEq] using hp
    have H := zrun_sound table m hm k u v hz
    rw [show embed u = embed (reprZ h n w) from pad_embed h n w] at H
    refine ⟨k,embed v,hk,H,v.h,n+2,out,ho,?_⟩
    cases v with
    | mk q h' l r =>
      simp only [project,B,Z0.mk.injEq] at hv
      obtain ⟨rfl,rfl,rfl⟩ := hv
      rfl

theorem inv_entry (m : Machine) (hm : compatible table m) :
    ∃ t, run m 39 blank = some t ∧ Inv t := by
  let u : Agent50Zipper.Z := ⟨0,0,[],[]⟩
  have hb : embed u = blank := by
    unfold u embed blank
    congr 1
    funext x
    simp [atCell]
  have hp : (zrun table 39 u).map project = some (B 6 0 []) :=
    (run_project table 39 u).trans blankEntry
  cases hz : zrun table 39 u with
  | none => simp [hz] at hp
  | some v =>
    have hv : project v = B 6 0 [] := by simpa only [hz,Option.map_some,Option.some.injEq] using hp
    have H := zrun_sound table m hm 39 u v hz
    rw [hb] at H
    refine ⟨embed v,H,v.h,6,[],.nil,?_⟩
    cases v with
    | mk q h' l r =>
      simp only [project,B,Z0.mk.injEq] at hv
      obtain ⟨rfl,rfl,rfl⟩ := hv
      rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ j t, k ≤ j ∧ run m j blank = some t ∧ Inv t := by
    intro k
    induction k with
    | zero =>
      obtain ⟨t,ht,hi⟩ := inv_entry m hm
      exact ⟨39,t,by omega,ht,hi⟩
    | succ k ih =>
      obtain ⟨j,t,hj,hr,hi⟩ := ih
      obtain ⟨a,v,ha,hs,hv⟩ := inv_grow m hm hi
      exact ⟨j+a,v,by omega,by rw [run_append,hr]; exact hs,hv⟩
  intro k
  obtain ⟨j,t,hj,hr,_⟩ := arbitrary k
  rw [show j = k+(j-k) by omega,run_append] at hr
  cases h : run m k blank with
  | none => simp [h] at hr
  | some _ => rfl

#print axioms wordStep
#print axioms paddedWordStep
#print axioms inv_entry
#print axioms inv_grow
#print axioms never
end BB6Coverage.Agent16Raw118Nested.M434
