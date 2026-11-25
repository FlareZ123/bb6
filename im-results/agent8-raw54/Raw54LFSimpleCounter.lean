import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFSimpleCounter
open BB6Coverage BB6Coverage.Agent31Pump

def table (long v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,long,if v then 4 else 3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def word : List Bool → List Bool
  | [] => []
  | b::bs => false::b::word bs

def cfg (bs : List Bool) (r : Bool) : Z0 := ⟨0,false::word bs,[false,r,r]⟩
def carryCfg (k : Nat) (bs : List Bool) (r : Bool) : Z0 :=
  ⟨4,word bs,rep [true,true] k ++ [false,false,r,r]⟩
def inc : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::inc bs

def out (long r : Bool) : Bool := !(long && r)
def cost (long r : Bool) : Nat := if !long && r then 5 else 7

theorem first (long v : Bool) : run0 (table long v) 10 ⟨0,[],[]⟩ = some (cfg [true] true) := by
  cases long <;> cases v <;> rfl

theorem prefixStep (long v r : Bool) (bs : List Bool) :
    run0 (table long v) (cost long r) (cfg bs r) = some (carryCfg 0 bs (out long r)) := by
  cases long <;> cases v <;> cases r <;> cases bs <;> rfl

theorem carryOne (long v r : Bool) (k : Nat) (bs : List Bool) :
    run0 (table long v) 2 (carryCfg k (true::bs) r) = some (carryCfg (k+1) bs r) := by
  cases long <;> cases v <;> rfl

theorem word_zeros (k : Nat) (bs : List Bool) :
    word (List.replicate k false ++ bs) = rep [false,false] k ++ word bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,word,ih,rep,List.append_assoc]; rfl

theorem zz_rotate (k : Nat) (r : List Bool) :
    false :: (rep [false,false] k ++ r) = rep [false,false] k ++ (false::r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      _ = [false,false] ++ (false::(rep [false,false] k ++ r)) := rfl
      _ = [false,false] ++ (rep [false,false] k ++ (false::r)) := congrArg (fun xs => [false,false] ++ xs) ih
      _ = _ := by simp only [rep,List.append_assoc]

theorem restore (long v r : Bool) (k : Nat) (bs : List Bool) :
    run0 (table long v) (2*k+1) ⟨0,true::true::word bs,rep [true,true] k ++ [false,false,r,r]⟩ =
      some (cfg (List.replicate k false ++ true::bs) r) := by
  have a := sweepR (table long v) 0 [true] [] [true,true] [false,false] 2 (by intro L R; cases long <;> cases v <;> rfl)
    k (true::word bs) [false,false,r,r]
  have b : run0 (table long v) 1 ⟨0,true::(rep [false,false] k ++ (true::word bs)),[false,false,r,r]⟩ =
      some ⟨0,false::false::(rep [false,false] k ++ true::word bs),[false,r,r]⟩ := by cases long <;> cases v <;> rfl
  have H := join0 a b
  rw [zz_rotate k (true::word bs)] at H
  simpa only [cfg,word_zeros,word,List.nil_append,List.cons_append,List.append_assoc] using H

theorem carryZero (long v r : Bool) (k : Nat) (bs : List Bool) :
    run0 (table long v) 2 (carryCfg k (false::bs) r) =
      some ⟨0,true::true::word bs,rep [true,true] k ++ [false,false,r,r]⟩ := by cases long <;> cases v <;> rfl

theorem carryEmpty (long v r : Bool) (k : Nat) :
    run0 (table long v) 2 (carryCfg k [] r) =
      some ⟨0,[true,true],rep [true,true] k ++ [false,false,r,r]⟩ := by cases long <;> cases v <;> rfl

theorem carry (long v r : Bool) (bs : List Bool) (k : Nat) :
    ∃ t, 0<t ∧ run0 (table long v) t (carryCfg k bs r) = some (cfg (List.replicate k false ++ inc bs) r) := by
  induction bs generalizing k with
  | nil => exact ⟨2+(2*k+1),by omega,join0 (carryEmpty long v r k) (restore long v r k [])⟩
  | cons b bs ih =>
    cases b
    · exact ⟨2+(2*k+1),by omega,join0 (carryZero long v r k bs) (restore long v r k bs)⟩
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      refine ⟨2+t,by omega,?_⟩
      have H := join0 (carryOne long v r k bs) hr
      rw [List.replicate_succ', List.append_assoc] at H
      exact H

def orbit : Nat → List Bool
  | 0 => [true]
  | n+1 => inc (orbit n)
def rightOrbit (long : Bool) : Nat → Bool
  | 0 => true
  | n+1 => out long (rightOrbit long n)
def family (long : Bool) (n : Nat) : Z0 := cfg (orbit n) (rightOrbit long n)

theorem family_next (long v : Bool) (n : Nat) :
    ∃ t, 0<t ∧ run0 (table long v) t (family long n) = some (family long (n+1)) := by
  obtain ⟨t,ht,hr⟩ := carry long v (out long (rightOrbit long n)) (orbit n) 0
  exact ⟨cost long (rightOrbit long n)+t,by omega,join0 (prefixStep long v (rightOrbit long n) (orbit n)) hr⟩
theorem never (long v : Bool) (m : Machine) (hm : compatible (table long v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table long v) (family long) 10 (first long v) (family_next long v) m hm
#print axioms never
end BB6.Agent8Raw54.LFSimpleCounter
