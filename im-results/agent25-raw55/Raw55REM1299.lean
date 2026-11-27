import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31Raw55REM1299
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def o (n : Nat) := rep [true] n
def z (n : Nat) := rep [false] n
def Z : List Bool := [false,false,false,false]
def O : List Bool := [true,true,true,true]
def sec (r : List Bool) : Z0 := ⟨0,[false,false],r⟩
inductive Tail where | endWord | zero (r : List Bool)
def suffix : Tail → List Bool
  | .endWord => []
  | .zero r => Z++r
def result : Tail → List Bool
  | .endWord => O
  | .zero r => O++r

theorem carry (n : Nat) (t : Tail) :
    run0 table (2*n+20) (sec (o n ++ suffix t)) = some (sec (z n ++ result t)) := by
  cases n with
  | zero => cases t <;> rfl
  | succ n =>
    have a : run0 table 1 (sec (o (n+1)++suffix t)) = some ⟨1,[true,true,false],o n++suffix t⟩ := by rfl
    have b := sweepR table 1 [true] [] [true] [true] 1 (fun _ _ => rfl) n [true,false] (suffix t)
    simp only [Nat.one_mul,List.nil_append] at b
    have c : run0 table 18 ⟨1,[true]++o n++[true,false],suffix t⟩ = some ⟨5,[true]++o n++[true,false],result t⟩ := by
      cases t <;> rfl
    have hL : [true]++o n++[true,false] = o (n+2)++[false] := by
      change ([true]++rep [true] n)++[true,false] = ([true]++[true]++rep [true] n)++[false]
      simp only [List.append_assoc]
      change [true] ++ (rep [true] n ++ ([true] ++ [false])) = [true] ++ ([true] ++ (rep [true] n ++ [false]))
      rw [← List.append_assoc (rep [true] n) [true] [false],rep_snoc]
      simp only [List.append_assoc]
    have d := sweepL table 5 [] [] [true] [false] 1 (fun _ _ => rfl) (n+2) [false] (result t)
    simp only [Nat.one_mul,List.nil_append] at d
    have e : run0 table 1 ⟨5,[false],z (n+2)++result t⟩ = some (sec (z (n+1)++result t)) := by rfl
    have b' : run0 table n ⟨1,[true,true,false],o n++suffix t⟩ = some ⟨1,[true]++o n++[true,false],suffix t⟩ := by
      exact b
    rw [hL] at c
    rw [hL] at b'
    have h := join0 (join0 (join0 (join0 a b') c) d) e
    rw [show 1+n+18+(n+2)+1=2*(n+1)+20 by omega] at h
    exact h

def encode : List Bool → List Bool
  | [] => []
  | b::bs => rep [b] 4 ++ encode bs

def cut : List Bool → Nat × Tail
  | [] => (0,.endWord)
  | false::bs => (0,.zero (encode bs))
  | true::bs => let c := cut bs; (c.1+1,c.2)
def next : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::next bs

theorem rep_add (P : List Bool) (n m : Nat) : rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem enc_cut (bs : List Bool) : encode bs = o (4*(cut bs).1) ++ suffix (cut bs).2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => rfl
    | true =>
      simp only [encode,cut]
      rw [ih,show 4*((cut bs).1+1)=4+4*(cut bs).1 by omega]
      simp only [o,rep_add,List.append_assoc]

theorem enc_next (bs : List Bool) : encode (next bs) = z (4*(cut bs).1) ++ result (cut bs).2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => rfl
    | true =>
      simp only [encode,next,cut]
      rw [ih,show 4*((cut bs).1+1)=4+4*(cut bs).1 by omega]
      simp only [z,rep_add,List.append_assoc]

def orbit : Nat → List Bool
  | 0 => [true]
  | k+1 => next (orbit k)
def family (k : Nat) : Z0 := sec (encode (orbit k))
def cost (k : Nat) := 2*(4*(cut (orbit k)).1)+20
theorem first : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  unfold cost family
  rw [show orbit (k+1)=next (orbit k) by rfl,enc_cut (orbit k),enc_next (orbit k)]
  exact carry (4*(cut (orbit k)).1) (cut (orbit k)).2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 cost first (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent31Raw55REM1299
