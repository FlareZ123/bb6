import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFDualCounter
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨v,true,2⟩)
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

def pair : List Bool → List Bool
  | [] => []
  | b::bs => b::b::pair bs

def cfg (bs rs : List Bool) : Z0 := ⟨0,false::word bs,false::pair rs⟩
def carryCfg (k : Nat) (bs rs : List Bool) : Z0 :=
  ⟨4,word bs,rep [true,true] k ++ false::false::pair rs⟩
def scanCfg (v : Bool) (k : Nat) (bs rs : List Bool) : Z0 :=
  ⟨2,rs.headD false::(rep [v,v] k ++ true::true::word bs),(pair rs).tail⟩
def inc (v : Bool) : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => (!v)::inc v bs

theorem first (v : Bool) : run0 (table v) 10 ⟨0,[],[]⟩ = some (cfg [true] [true]) := by cases v <;> rfl

theorem pair_rep (b : Bool) (k : Nat) (bs : List Bool) :
    pair (List.replicate k b ++ bs) = rep [b,b] k ++ pair bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,pair,ih,rep,List.append_assoc]; rfl

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

theorem prefixStep (v : Bool) (bs rs : List Bool) :
    run0 (table v) 2 (cfg bs rs) = some (scanCfg v 0 bs rs) := by
  cases v <;> cases rs <;> rfl

theorem scanOne (v : Bool) (k : Nat) (bs rs : List Bool) :
    run0 (table v) 2 (scanCfg v k bs (true::rs)) = some (scanCfg v (k+1) bs rs) := by
  cases v <;> cases rs <;> rfl

theorem scanZero (v : Bool) (k : Nat) (bs rs : List Bool) :
    run0 (table v) 1 (scanCfg v k bs (false::rs)) =
      some ⟨3,[false,false] ++ (rep [v,v] k ++ true::true::word bs),pair rs⟩ := by cases v <;> rfl

theorem scanEmpty (v : Bool) (k : Nat) (bs : List Bool) :
    run0 (table v) 1 (scanCfg v k bs []) =
      some ⟨3,[false,false] ++ (rep [v,v] k ++ true::true::word bs),[]⟩ := by cases v <;> rfl

theorem returnZero (k : Nat) (bs rs : List Bool) :
    run0 (table false) (2*(k+1)+2) ⟨3,[false,false] ++ (rep [false,false] k ++ true::true::word bs),pair rs⟩ =
      some (carryCfg 0 bs (List.replicate k true ++ true::rs)) := by
  have a := sweepL (table false) 3 [] [] [false,false] [true,true] 2 (by intro L R; rfl) (k+1) (true::true::word bs) (pair rs)
  have b : run0 (table false) 2 ⟨3,true::true::word bs,rep [true,true] (k+1) ++ pair rs⟩ =
      some ⟨4,word bs,false::false::(rep [true,true] (k+1) ++ pair rs)⟩ := by rfl
  have H := join0 a b
  unfold carryCfg
  rw [pair_rep]
  simp only [rep,List.nil_append,List.append_assoc,pair] at H ⊢
  have e := congrArg (fun z => z ++ pair rs) (rep_snoc [true,true] k)
  simp only [List.append_assoc] at e
  change rep [true,true] k ++ true::true::pair rs = [true,true] ++ (rep [true,true] k ++ pair rs) at e
  rw [e]
  exact H

theorem returnOne (k : Nat) (bs rs : List Bool) :
    run0 (table true) (2*(k+1)+2) ⟨3,[false,false] ++ (rep [true,true] k ++ true::true::word bs),pair rs⟩ =
      some (carryCfg 0 bs (List.replicate k false ++ true::rs)) := by
  have a : run0 (table true) 2 ⟨3,[false,false] ++ (rep [true,true] k ++ true::true::word bs),pair rs⟩ =
      some ⟨3,rep [true,true] k ++ true::true::word bs,true::true::pair rs⟩ := by rfl
  have eq : rep [true,true] k ++ true::true::word bs = true::(rep [true,true] k ++ true::word bs) := by
    clear a
    induction k with
    | zero => rfl
    | succ k ih => simp only [rep,List.append_assoc]; change true::true::(rep [true,true] k ++ true::true::word bs) = _; rw [ih]; rfl
  have b : run0 (table true) 1 ⟨3,rep [true,true] k ++ true::true::word bs,true::true::pair rs⟩ =
      some ⟨4,rep [true,true] k ++ true::word bs,false::true::true::pair rs⟩ := by rw [eq]; rfl
  have c := sweepL (table true) 4 [] [] [true,true] [false,false] 2 (by intro L R; rfl) k (true::word bs) (false::true::true::pair rs)
  have d : run0 (table true) 1 ⟨4,true::word bs,rep [false,false] k ++ false::true::true::pair rs⟩ =
      some ⟨4,word bs,false::(rep [false,false] k ++ false::true::true::pair rs)⟩ := by rfl
  have H := join0 (join0 (join0 a b) c) d
  rw [show 2+1+2*k+1=2*(k+1)+2 by omega] at H
  unfold carryCfg
  rw [pair_rep]
  simp only [rep,List.nil_append,pair] at H ⊢
  rw [← zz_rotate k (true::true::pair rs)] at H
  exact H

theorem returnAny (v : Bool) (k : Nat) (bs rs : List Bool) :
    run0 (table v) (2*(k+1)+2) ⟨3,[false,false] ++ (rep [v,v] k ++ true::true::word bs),pair rs⟩ =
      some (carryCfg 0 bs (List.replicate k (!v) ++ true::rs)) := by
  cases v
  · exact returnZero k bs rs
  · exact returnOne k bs rs

theorem scan (v : Bool) (bs rs : List Bool) (k : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (scanCfg v k bs rs) = some (carryCfg 0 bs (List.replicate k (!v) ++ inc v rs)) := by
  induction rs generalizing k with
  | nil => exact ⟨1+(2*(k+1)+2),by omega,join0 (scanEmpty v k bs) (returnAny v k bs [])⟩
  | cons b rs ih =>
    cases b
    · exact ⟨1+(2*(k+1)+2),by omega,join0 (scanZero v k bs rs) (returnAny v k bs rs)⟩
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      refine ⟨2+t,by omega,?_⟩
      have H := join0 (scanOne v k bs rs) hr
      rw [List.replicate_succ',List.append_assoc] at H
      exact H

theorem carryOne (v : Bool) (k : Nat) (bs rs : List Bool) :
    run0 (table v) 2 (carryCfg k (true::bs) rs) = some (carryCfg (k+1) bs rs) := by cases v <;> rfl

theorem restore (v : Bool) (k : Nat) (bs rs : List Bool) :
    run0 (table v) (2*k+1) ⟨0,true::true::word bs,rep [true,true] k ++ false::false::pair rs⟩ =
      some (cfg (List.replicate k false ++ true::bs) rs) := by
  have a := sweepR (table v) 0 [true] [] [true,true] [false,false] 2 (by intro L R; cases v <;> rfl)
    k (true::word bs) (false::false::pair rs)
  have b : run0 (table v) 1 ⟨0,true::(rep [false,false] k ++ (true::word bs)),false::false::pair rs⟩ =
      some ⟨0,false::false::(rep [false,false] k ++ true::word bs),false::pair rs⟩ := by cases v <;> rfl
  have H := join0 a b
  rw [zz_rotate k (true::word bs)] at H
  simpa only [cfg,word_zeros,word,List.nil_append,List.cons_append,List.append_assoc] using H

theorem carryZero (v : Bool) (k : Nat) (bs rs : List Bool) :
    run0 (table v) 2 (carryCfg k (false::bs) rs) =
      some ⟨0,true::true::word bs,rep [true,true] k ++ false::false::pair rs⟩ := by cases v <;> rfl

theorem carryEmpty (v : Bool) (k : Nat) (rs : List Bool) :
    run0 (table v) 2 (carryCfg k [] rs) =
      some ⟨0,[true,true],rep [true,true] k ++ false::false::pair rs⟩ := by cases v <;> rfl

theorem carry (v : Bool) (bs rs : List Bool) (k : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (carryCfg k bs rs) = some (cfg (List.replicate k false ++ inc true bs) rs) := by
  induction bs generalizing k with
  | nil => exact ⟨2+(2*k+1),by omega,join0 (carryEmpty v k rs) (restore v k [] rs)⟩
  | cons b bs ih =>
    cases b
    · exact ⟨2+(2*k+1),by omega,join0 (carryZero v k bs rs) (restore v k bs rs)⟩
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      refine ⟨2+t,by omega,?_⟩
      have H := join0 (carryOne v k bs rs) hr
      rw [List.replicate_succ',List.append_assoc] at H
      exact H

def orbit (v : Bool) : Nat → List Bool
  | 0 => [true]
  | n+1 => inc v (orbit v n)
def family (v : Bool) (n : Nat) : Z0 := cfg (orbit true n) (orbit v n)

theorem family_next (v : Bool) (n : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (family v n) = some (family v (n+1)) := by
  obtain ⟨t,ht,hr⟩ := scan v (orbit true n) (orbit v n) 0
  obtain ⟨u,hu,hs⟩ := carry v (orbit true n) (inc v (orbit v n)) 0
  exact ⟨2+t+u,by omega,join0 (join0 (prefixStep v (orbit true n) (orbit v n)) hr) hs⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table v) (family v) 10 (first v) (family_next v) m hm
#print axioms never
end BB6.Agent8Raw54.LFDualCounter
