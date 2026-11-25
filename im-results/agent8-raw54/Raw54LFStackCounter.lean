import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFStackCounter
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
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

def right (n : Nat) : List Bool := rep [false,true,true,false] n ++ [false,true,true]
def cfg (bs : List Bool) (n : Nat) : Z0 := ⟨0,false::word bs,right n⟩
def carryCfg (k : Nat) (bs : List Bool) (n : Nat) : Z0 :=
  ⟨4,word bs,rep [true,true] k ++ false::right n⟩
def inc : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::inc bs

theorem first : run0 table 10 ⟨0,[],[]⟩ = some (cfg [true] 0) := by rfl

theorem right_eq (n : Nat) : false::right n = rep [false,false,true,true] (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [false,false,true,true] ++ (false::right n) = [false,false,true,true] ++ rep [false,false,true,true] (n+1)
    rw [ih]

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

theorem transfer (n : Nat) (L : List Bool) :
    run0 table (4*(n+1)) ⟨0,false::L,right n⟩ =
      some ⟨0,false::(rep [false,true,true,true] (n+1) ++ L),[]⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 4 ⟨0,false::L,right (n+1)⟩ = some ⟨0,false::([false,true,true,true] ++ L),right n⟩ := by rfl
    have H := join0 h (ih ([false,true,true,true] ++ L))
    rw [show 4*(n+1+1)=4+4*(n+1) by omega]
    simp only [← List.append_assoc,rep_snoc] at H
    exact H

theorem prefixStep (bs : List Bool) (n : Nat) :
    ∃ t, 0<t ∧ run0 table t (cfg bs n) = some (carryCfg 0 bs (n+1)) := by
  have a := transfer n (word bs)
  have b : run0 table 7 ⟨0,false::(rep [false,true,true,true] (n+1) ++ word bs),[]⟩ =
      some ⟨4,rep [false,true,true,true] (n+1) ++ word bs,[false,false,true,true]⟩ := by rfl
  have c := sweepL table 4 [] [] [false,true,true,true] [false,false,true,true] 4 (by intro L R; rfl) (n+1) (word bs) [false,false,true,true]
  have H := join0 (join0 a b) c
  refine ⟨4*(n+1)+7+4*(n+1),by omega,?_⟩
  unfold cfg carryCfg
  simp only [rep,List.nil_append] at H ⊢
  rw [right_eq]
  have eq := rep_snoc [false,false,true,true] n
  have eq2 := rep_snoc [false,false,true,true] (n+1)
  simp only [rep] at eq2
  simpa only [rep,List.append_assoc,← eq2] using H

theorem carryOne (k : Nat) (bs : List Bool) (n : Nat) :
    run0 table 2 (carryCfg k (true::bs) n) = some (carryCfg (k+1) bs n) := by rfl

theorem restore (k : Nat) (bs : List Bool) (n : Nat) :
    run0 table (2*k+1) ⟨0,true::true::word bs,rep [true,true] k ++ false::right n⟩ =
      some (cfg (List.replicate k false ++ true::bs) n) := by
  have a := sweepR table 0 [true] [] [true,true] [false,false] 2 (by intro L R; rfl)
    k (true::word bs) (false::right n)
  have b : run0 table 1 ⟨0,true::(rep [false,false] k ++ (true::word bs)),false::right n⟩ =
      some ⟨0,false::false::(rep [false,false] k ++ true::word bs),right n⟩ := by rfl
  have H := join0 a b
  rw [zz_rotate k (true::word bs)] at H
  simpa only [cfg,word_zeros,word,List.nil_append,List.cons_append,List.append_assoc] using H

theorem carryZero (k : Nat) (bs : List Bool) (n : Nat) :
    run0 table 2 (carryCfg k (false::bs) n) =
      some ⟨0,true::true::word bs,rep [true,true] k ++ false::right n⟩ := by rfl

theorem carryEmpty (k : Nat) (n : Nat) :
    run0 table 2 (carryCfg k [] n) =
      some ⟨0,[true,true],rep [true,true] k ++ false::right n⟩ := by rfl

theorem carry (bs : List Bool) (n : Nat) (k : Nat) :
    ∃ t, 0<t ∧ run0 table t (carryCfg k bs n) = some (cfg (List.replicate k false ++ inc bs) n) := by
  induction bs generalizing k with
  | nil => exact ⟨2+(2*k+1),by omega,join0 (carryEmpty k n) (restore k [] n)⟩
  | cons b bs ih =>
    cases b
    · exact ⟨2+(2*k+1),by omega,join0 (carryZero k bs n) (restore k bs n)⟩
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      refine ⟨2+t,by omega,?_⟩
      have H := join0 (carryOne k bs n) hr
      rw [List.replicate_succ',List.append_assoc] at H
      exact H

def orbit : Nat → List Bool
  | 0 => [true]
  | n+1 => inc (orbit n)
def family (n : Nat) : Z0 := cfg (orbit n) n

theorem family_next (n : Nat) :
    ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨t,ht,hr⟩ := prefixStep (orbit n) n
  obtain ⟨u,hu,hs⟩ := carry (orbit n) (n+1) 0
  exact ⟨t+u,by omega,join0 hr hs⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 10 first family_next m hm
#print axioms never
end BB6.Agent8Raw54.LFStackCounter
