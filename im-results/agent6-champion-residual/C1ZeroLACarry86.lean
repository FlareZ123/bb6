import C1ZeroLACore
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace BB6.Agent6C1ZeroLACarry86
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6C1ZeroLACore
open BB6.Agent6C1ZeroLAFour (P Q T L0 h f z u as bs cs rep_add z_add shift)
def ctr : PartialMachine := FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,7]
def core : Core ctr where
  q := 5
  sc := 5
  st := 9
  start := by intro R; rfl
  scan := by intro L R; rfl
  pop := by intro L R; rfl
  finish := by intro R; rfl
abbrev J : List Bool := [false,true]
abbrev K : List Bool := [false,true,false,true,false,true,false,true,true]
abbrev W0 : List Bool := [false,false,false,false,false,false,false,false,true]
abbrev W1 : List Bool := [true,true,false,false,false,false,false,true]
abbrev W2 : List Bool := [false,false,false,false,true,true,false,false,false,true]
abbrev W3 : List Bool := [true,true,false,true,true,false,false,false,true]
inductive Tail : List Bool → Prop
  | end1 : Tail h
  | end2 : Tail (z 4++u 3)
  | end3 : Tail [true,true,false,true,true,true]
  | scan {R : List Bool} : Tail R → Tail (T++R)
  | d0 {R : List Bool} : Tail R → Tail (W0++R)
  | d1 {R : List Bool} : Tail R → Tail (W1++R)
  | d2 {R : List Bool} : Tail R → Tail (W2++R)
  | d3 {R : List Bool} : Tail R → Tail (W3++R)

theorem end1 (L : List Bool) : run0 ctr 20 ⟨5,L0++L,h⟩ = some ⟨4,L,J++(z 4++u 3)⟩ := rfl
theorem end3 (L : List Bool) : run0 ctr 26 ⟨5,L0++L,[true,true,false,true,true,true]⟩ = some ⟨4,L,J++W0++h⟩ := rfl
theorem zeros (L R : List Bool) : run0 ctr 16 ⟨5,L0++L,z 3++R⟩ = some ⟨4,L,J++T++u 2++R⟩ := rfl
theorem ones (L R : List Bool) : run0 ctr 16 ⟨5,L0++L,u 2++z 2++R⟩ = some ⟨4,L,J++z 4++u 2++R⟩ := rfl
theorem push (L R : List Bool) : run0 ctr 13 ⟨5,L0++L,W3++R⟩ = some ⟨5,L0++K++L,R⟩ := rfl
theorem pop (L R : List Bool) : run0 ctr 11 ⟨4,K++L,J++R⟩ = some ⟨4,L,J++W0++R⟩ := rfl
theorem scanPop (L R : List Bool) : run0 ctr 5 ⟨4,P++L,J++R⟩ = some ⟨4,L,J++T++R⟩ := rfl

theorem transform {R : List Bool} (hr : Tail R) :
    ∃ k U, 0<k ∧ Tail U ∧ ∀ L : List Bool, run0 ctr k ⟨5,L0++L,R⟩ = some ⟨4,L,J++U⟩ := by
  induction hr with
  | end1 => exact ⟨20,_,by decide,Tail.end2,end1⟩
  | end2 => exact ⟨16,_,by decide,Tail.scan Tail.end3,fun L => zeros L (f++u 3)⟩
  | end3 => exact ⟨26,_,by decide,Tail.d0 Tail.end1,end3⟩
  | @scan R hr ih =>
    obtain ⟨k,U,hk,hu,H⟩ := ih
    refine ⟨5+k+5,_,by omega,Tail.scan hu,?_⟩
    intro L
    have H1 : run0 ctr 5 ⟨5,L0++L,T++R⟩ = some ⟨5,L0++P++L,R⟩ := core.scan L R
    have H2 := join0 H1 (by simpa only [List.append_assoc] using H (P++L))
    simpa only [List.append_assoc] using join0 H2 (scanPop L U)
  | @d0 R hr ih =>
    refine ⟨16,_,by decide,Tail.scan (Tail.d1 hr),?_⟩
    intro L
    have H := zeros L (z 5++h++R)
    simpa only [List.append_assoc,z,u,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using H
  | @d1 R hr ih =>
    refine ⟨16,_,by decide,Tail.d2 hr,?_⟩
    intro L
    have H := ones L (z 3++h++R)
    simpa only [List.append_assoc,z,u,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using H
  | @d2 R hr ih =>
    refine ⟨16,_,by decide,Tail.scan (Tail.d3 hr),?_⟩
    intro L
    have H := zeros L (f++u 2++z 3++h++R)
    simpa only [List.append_assoc,z,u,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using H
  | @d3 R hr ih =>
    obtain ⟨k,U,hk,hu,H⟩ := ih
    refine ⟨13+k+11,_,by omega,Tail.d0 hu,?_⟩
    intro L
    have H1 := join0 (push L R) (by simpa only [List.append_assoc] using H (K++L))
    simpa only [List.append_assoc] using join0 H1 (pop L U)

abbrev SA (R : List Bool) := z 6++h++R
abbrev SB (R : List Bool) := u 3++z 5++h++R
abbrev SC (R : List Bool) := z 2++u 2++z 3++h++R
abbrev SD (R : List Bool) := u 3++f++u 2++z 3++h++R

theorem turnA (L R : List Bool) : run0 ctr 11 ⟨5,L0++L,z 2++SA R⟩ = some ⟨4,P++L,f++SB R⟩ := rfl
theorem turnB (L R : List Bool) : run0 ctr 21 ⟨5,L0++L,z 2++SB R⟩ = some ⟨4,P++L,f++Q++SC R⟩ := rfl
theorem turnC (L R : List Bool) : run0 ctr 11 ⟨5,L0++L,z 2++SC R⟩ = some ⟨4,P++L,f++SD R⟩ := rfl
theorem turnDpush (L R : List Bool) : run0 ctr 18 ⟨5,L0++L,z 2++SD R⟩ = some ⟨5,L0++K++P++L,R⟩ := rfl

theorem turnD {R : List Bool} (hr : Tail R) :
    ∃ k U, 0<k ∧ Tail U ∧ ∀ L, run0 ctr k ⟨5,L0++L,z 2++SD R⟩ = some ⟨4,P++L,f++Q++SA U⟩ := by
  obtain ⟨k,U,hk,hu,H⟩ := transform hr
  refine ⟨18+k+11,U,by omega,hu,?_⟩
  intro L
  have H1 := join0 (turnDpush L R) (by simpa only [List.append_assoc] using H (K++P++L))
  have H2 := pop (P++L) U
  simpa only [List.append_assoc,z,u,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using join0 H1 H2

theorem stepA (n : Nat) (R : List Bool) :
    run0 ctr (cost core n 11) (cfg n (SA R)) = some (cfg n (SB R)) :=
  step core n 11 _ _ (turnA · R)

theorem stepB (n : Nat) (R : List Bool) :
    run0 ctr (cost core n 21) (cfg n (SB R)) = some (cfg (n+1) (SC R)) := by
  rw [←cfg_add n 1]
  exact step core n 21 _ _ (fun L => by simpa only [show bs 1=Q by rfl,show core.q=5 by rfl,List.append_assoc] using turnB L R)

theorem stepC (n : Nat) (R : List Bool) :
    run0 ctr (cost core n 11) (cfg n (SC R)) = some (cfg n (SD R)) :=
  step core n 11 _ _ (turnC · R)

theorem stepD {R : List Bool} (hr : Tail R) (n : Nat) :
    ∃ k U, 0<k ∧ Tail U ∧ run0 ctr k (cfg n (SD R)) = some (cfg (n+1) (SA U)) := by
  obtain ⟨k,U,hk,hu,H⟩ := turnD hr
  refine ⟨cost core n k,U,by unfold cost; omega,hu,?_⟩
  rw [←cfg_add n 1]
  exact step core n k _ _ (fun L => by simpa only [show bs 1=Q by rfl,show core.q=5 by rfl,List.append_assoc] using H L)

theorem advance {R : List Bool} (hr : Tail R) (n : Nat) :
    ∃ k U, 0<k ∧ Tail U ∧ run0 ctr k (cfg n (SA R)) = some (cfg (n+2) (SA U)) := by
  obtain ⟨k,U,hk,hu,H⟩ := stepD hr (n+1)
  exact ⟨cost core n 11+cost core n 21+cost core (n+1) 11+k,U,by omega,hu,
    join0 (join0 (join0 (stepA n R) (stepB n R)) (stepC (n+1) R)) H⟩

theorem entry : run0 ctr 94 ⟨0,[],[]⟩ = some (cfg 1 (SA h)) := rfl

inductive Inv : Z0 → Prop
  | mk (n : Nat) {R : List Bool} : Tail R → Inv (cfg n (SA R))
theorem progress {c : Z0} (hc : Inv c) : ∃ k c', 0<k ∧ run0 ctr k c = some c' ∧ Inv c' := by
  cases hc with
  | @mk n R hr =>
    obtain ⟨k,U,hk,hu,H⟩ := advance hr n
    exact ⟨k,cfg (n+2) (SA U),hk,H,Inv.mk _ hu⟩
theorem next_exists (c : {c : Z0 // Inv c}) :
    ∃ p : Nat × {c : Z0 // Inv c}, 0<p.1 ∧ run0 ctr p.1 c.val = some p.2.val := by
  obtain ⟨k,t,hk,hr,ht⟩ := progress c.property
  exact ⟨(k,⟨t,ht⟩),hk,hr⟩
noncomputable def next (c : {c : Z0 // Inv c}) := Classical.choose (next_exists c)
theorem next_sound (c : {c : Z0 // Inv c}) :
    0<(next c).1 ∧ run0 ctr (next c).1 c.val = some (next c).2.val := Classical.choose_spec (next_exists c)
noncomputable def orbit : Nat → {c : Z0 // Inv c}
  | 0 => ⟨cfg 1 (SA h),Inv.mk 1 Tail.end1⟩
  | n+1 => (next (orbit n)).2

open BB6.Agent13BlankDelay
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => (orbit k).val) 94 (fun k => (next (orbit k)).1) entry
    (fun k => (next_sound (orbit k)).1) (fun k => (next_sound (orbit k)).2) m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms transform
#print axioms advance
#print axioms entry
#print axioms next_sound
#print axioms never
#print axioms cover
end BB6.Agent6C1ZeroLACarry86
