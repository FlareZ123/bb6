import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LeftPair
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some (if v then ⟨false,true,5⟩ else ⟨false,true,2⟩))
  | _,_ => none

def oo : List Bool := [true,true]
def zz : List Bool := [false,false]
def word : List Bool → List Bool
  | [] => []
  | b::bs => false::b::word bs

def cfg (bs : List Bool) : Z0 := ⟨0,false::true::word bs,[true,true]⟩
def carryCfg (k : Nat) (bs : List Bool) : Z0 :=
  ⟨1,(word bs).tail,rep oo k ++ [true,false,false,true,true]⟩
def inc : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::inc bs

theorem word_zeros (k : Nat) (bs : List Bool) :
    word (List.replicate k false ++ bs) = rep zz k ++ word bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,word,ih,rep,List.append_assoc]; rfl

theorem first (v : Bool) : run0 (table v) 11 ⟨0,[],[]⟩ = some (cfg [true]) := by
  cases v <;> rfl

theorem prefixStep (v : Bool) (bs : List Bool) : run0 (table v) 5 (cfg bs) = some (carryCfg 0 bs) := by
  cases v <;> cases bs <;> rfl

theorem carryOne (v : Bool) (k : Nat) (bs : List Bool) :
    run0 (table v) 2 (carryCfg k (true::bs)) = some (carryCfg (k+1) bs) := by
  cases v <;> cases bs <;> rfl

theorem oo_rotate (k : Nat) (r : List Bool) :
    rep oo k ++ (true::r) = true :: (rep oo k ++ r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      _ = oo ++ (rep oo k ++ (true::r)) := by simp only [rep,List.append_assoc]
      _ = oo ++ (true :: (rep oo k ++ r)) := congrArg (fun xs => oo ++ xs) ih
      _ = _ := by simp only [rep,List.append_assoc]; rfl

theorem carryZero (v : Bool) (k : Nat) (bs : List Bool) :
    run0 (table v) 1 (carryCfg k (false::bs)) =
      some ⟨2,true::true::word bs,rep oo k ++ [false,false,true,true]⟩ := by
  unfold carryCfg
  change run0 (table v) 1 ⟨1,false::word bs,rep oo k ++ (true::[false,false,true,true])⟩ = _
  rw [oo_rotate]
  cases v <;> rfl

theorem carryEmpty (v : Bool) (k : Nat) :
    run0 (table v) 1 (carryCfg k []) =
      some ⟨2,[true,true],rep oo k ++ [false,false,true,true]⟩ := by
  unfold carryCfg
  change run0 (table v) 1 ⟨1,[],rep oo k ++ (true::[false,false,true,true])⟩ = _
  rw [oo_rotate]
  cases v <;> rfl

theorem zz_rotate (k : Nat) (r : List Bool) :
    false :: (rep zz k ++ r) = rep zz k ++ (false::r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      _ = zz ++ (false::(rep zz k ++ r)) := rfl
      _ = zz ++ (rep zz k ++ (false::r)) := congrArg (fun xs => zz ++ xs) ih
      _ = _ := by simp only [rep,List.append_assoc]

theorem return0 (k : Nat) (bs : List Bool) :
    run0 (table false) (2*k+2) ⟨2,true::true::word bs,rep oo k ++ [false,false,true,true]⟩ =
      some (cfg (List.replicate k false ++ true::bs)) := by
  have a := sweepR (table false) 2 [true] [] oo zz 2 (by intro L R; rfl)
    k (true::word bs) [false,false,true,true]
  have b : run0 (table false) 2 ⟨2,true::(rep zz k ++ (true::word bs)),[false,false,true,true]⟩ =
      some ⟨0,false::true::false::(rep zz k ++ true::word bs),[true,true]⟩ := by rfl
  have H := join0 a b
  rw [zz_rotate k (true::word bs)] at H
  simpa only [cfg,word_zeros,word,List.nil_append,List.cons_append,List.append_assoc] using H

theorem return1 (k : Nat) (bs : List Bool) :
    run0 (table true) (2*k+2) ⟨2,true::true::word bs,rep oo k ++ [false,false,true,true]⟩ =
      some (cfg (List.replicate k false ++ true::bs)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have a : run0 (table true) 2 ⟨2,true::true::word bs,rep oo (k+1) ++ [false,false,true,true]⟩ =
        some ⟨5,true::false::false::true::word bs,rep oo k ++ [false,false,true,true]⟩ := by rfl
    have b := sweepR (table true) 5 [true] [] oo zz 2 (by intro L R; rfl)
      k (false::false::true::word bs) [false,false,true,true]
    have c : run0 (table true) 2 ⟨5,true::(rep zz k ++ (false::false::true::word bs)),[false,false,true,true]⟩ =
        some ⟨0,false::true::false::(rep zz k ++ false::false::true::word bs),[true,true]⟩ := by rfl
    have H := join0 (join0 a b) c
    rw [zz_rotate k (false::false::true::word bs)] at H
    have h2 : rep zz k ++ (false::false::false::true::word bs) =
        false::false::(rep zz k ++ false::true::word bs) := by
      rw [← zz_rotate k (false::false::true::word bs), ← zz_rotate k (false::true::word bs)]
    rw [h2] at H
    rw [show 2*(k+1)+2=2+2*k+2 by omega]
    simpa only [cfg,List.replicate_succ,List.cons_append,word,word_zeros,List.nil_append,List.append_assoc] using H

theorem returnAny (v : Bool) (k : Nat) (bs : List Bool) :
    run0 (table v) (2*k+2) ⟨2,true::true::word bs,rep oo k ++ [false,false,true,true]⟩ =
      some (cfg (List.replicate k false ++ true::bs)) := by
  cases v
  · exact return0 k bs
  · exact return1 k bs

theorem carry (v : Bool) (bs : List Bool) (k : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (carryCfg k bs) = some (cfg (List.replicate k false ++ inc bs)) := by
  induction bs generalizing k with
  | nil =>
    exact ⟨1+(2*k+2),by omega,join0 (carryEmpty v k) (returnAny v k [])⟩
  | cons b bs ih =>
    cases b
    · exact ⟨1+(2*k+2),by omega,join0 (carryZero v k bs) (returnAny v k bs)⟩
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      refine ⟨2+t,by omega,?_⟩
      have H := join0 (carryOne v k bs) hr
      rw [List.replicate_succ', List.append_assoc] at H
      exact H

def orbit : Nat → List Bool
  | 0 => [true]
  | n+1 => inc (orbit n)
def family (n : Nat) : Z0 := cfg (orbit n)
theorem family_next (v : Bool) (n : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (family n) = some (family (n+1)) := by
  obtain ⟨t,ht,hr⟩ := carry v (orbit n) 0
  exact ⟨5+t,by omega,join0 (prefixStep v (orbit n)) hr⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table v) family 11 (first v) (family_next v) m hm
#print axioms never
end BB6.Agent8Raw54.LeftPair
