import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.Rec39
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => none
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def ones (n : Nat) := [true,true,true] ++ rep [true,true] n ++ [false,true,true,true,true,true]
def cfg (n : Nat) (b : Bool) (r : List Bool) : Z0 := ⟨2,b::ones n,r⟩
def Return (n : Nat) : Prop := ∀ r : List Bool, r.headD false = false →
    ∃ t, 0<t ∧ run0 table t (cfg n false r) = some (cfg (n+1) (r.tail.headD false) r.tail.tail)

theorem base : Return 0 := by
  intro r h
  refine ⟨34,by decide,?_⟩
  cases r with
  | nil => rfl
  | cons b r =>
    cases b
    · rfl
    · simp at h

theorem prefixStep (n : Nat) (r : List Bool) (h : r.headD false = false) :
    run0 table (8+2*n+24) (cfg (n+1) false r) =
      some (cfg 0 false (false :: (rep [false,false] n ++ ([true,true] ++ r.tail)))) := by
  have a : run0 table 8 (cfg (n+1) false r) =
      some ⟨4,rep [true,true] n ++ [false,true,true,true,true,true],
        [false,false,false,false,false] ++ ([true,true] ++ r.tail)⟩ := by
    cases r with
    | nil => rfl
    | cons b r =>
      cases b
      · rfl
      · simp at h
  have b := sweepL table 4 [] [false,false,false,false,false] [true,true] [false,false] 2
    (by intro L R; rfl) n [false,true,true,true,true,true] ([true,true] ++ r.tail)
  have c : run0 table 24 ⟨4,[false,true,true,true,true,true],
      [false,false,false,false,false] ++ (rep [false,false] n ++ ([true,true] ++ r.tail))⟩ =
      some (cfg 0 false (false :: (rep [false,false] n ++ ([true,true] ++ r.tail)))) := by rfl
  have ab := join0 a b
  exact join0 ab c

theorem extend (n : Nat) (r : List Bool) :
    run0 table 4 (cfg n true (true::r)) = some (cfg (n+1) (r.headD false) r.tail) := by
  rfl

theorem drain (N j n : Nat) (hret : ∀ k, k < N → Return k) (hjn : j+n < N) (R : List Bool) :
    ∃ t, run0 table t (cfg j false (false :: (rep [false,false] n ++ true::R))) =
      some (cfg (j+n+1) true R) := by
  induction n generalizing j with
  | zero =>
    obtain ⟨t,ht,hr⟩ := hret j (by omega) (false::true::R) rfl
    exact ⟨t,hr⟩
  | succ n ih =>
    obtain ⟨t,ht,hr⟩ := hret j (by omega) (false::false::false::(rep [false,false] n ++ true::R)) rfl
    obtain ⟨u,hu⟩ := ih (j+1) (by omega)
    refine ⟨t+u,?_⟩
    have H := join0 hr hu
    rw [show j+1+n+1 = j+(n+1)+1 by omega] at H
    exact H

theorem returns (n : Nat) : Return n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact base
    | succ n =>
      intro r hr
      obtain ⟨t,ht⟩ := drain (n+1) 0 n ih (by omega) (true::r.tail)
      rw [Nat.zero_add] at ht
      have H := join0 (prefixStep n r hr) ht
      refine ⟨8+2*n+24+t+4,by omega,?_⟩
      exact join0 H (extend (n+1) r.tail)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_returns table (fun n => cfg n false []) 35 (by rfl) _ m hm
  intro n
  exact returns n [] rfl

#print axioms never
end BB6.Agent8Raw54.Rec39
