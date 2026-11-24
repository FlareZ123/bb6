import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48Counter
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def ZB : List Bool := [false,false,false,true]
def OB : List Bool := [false,true,false,true]

theorem rep_right (w : List Bool) (n : Nat) :
    rep w (n+1) = rep w n ++ w := by
  exact (rep_snoc w n).symm

def normCost (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => normCost a n + (a+12*n) + normCost a n

def initCost (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => initCost a n + (a+12*(n+1)) + normCost a (n+1)

theorem normalize (p : PartialMachine) (q : Fin 6) (P R : List Bool) (a : Nat)
    (inc : ∀ n S, run0 p (a+12*n) ⟨q,P++rep OB n++ZB++S,R⟩ =
      some ⟨q,P++rep ZB n++OB++S,R⟩)
    (n : Nat) (S : List Bool) :
    run0 p (normCost a n) ⟨q,P++rep ZB n++S,R⟩ =
      some ⟨q,P++rep OB n++S,R⟩ := by
  induction n generalizing S with
  | zero => simp [normCost,rep,run0]
  | succ n ih =>
    have h1 := ih (ZB++S)
    have h2 := inc n S
    have h3 := ih (OB++S)
    have h1' : run0 p (normCost a n) ⟨q,P++rep ZB n++ZB++S,R⟩ =
        some ⟨q,P++rep OB n++ZB++S,R⟩ := by
      simpa only [List.append_assoc] using h1
    have h3' : run0 p (normCost a n) ⟨q,P++rep ZB n++OB++S,R⟩ =
        some ⟨q,P++rep OB n++OB++S,R⟩ := by
      simpa only [List.append_assoc] using h3
    have H := join0 (join0 h1' h2) h3'
    simpa only [normCost,rep_right ZB n,rep_right OB n,List.append_assoc] using H

theorem normalizeInit (p : PartialMachine) (q : Fin 6) (P R : List Bool) (a : Nat)
    (inc : ∀ n S, run0 p (a+12*n) ⟨q,P++rep OB n++ZB++S,R⟩ =
      some ⟨q,P++rep ZB n++OB++S,R⟩)
    (n : Nat) (S : List Bool) :
    run0 p (initCost a n) ⟨q,P++OB++rep ZB n++S,R⟩ =
      some ⟨q,P++rep OB (n+1)++S,R⟩ := by
  induction n generalizing S with
  | zero => simp [initCost,rep,run0]
  | succ n ih =>
    have h1 := ih (ZB++S)
    have h2 := inc (n+1) S
    have h3 := normalize p q P R a inc (n+1) (OB++S)
    have h1' : run0 p (initCost a n) ⟨q,P++OB++rep ZB n++ZB++S,R⟩ =
        some ⟨q,P++rep OB (n+1)++ZB++S,R⟩ := by
      simpa only [List.append_assoc] using h1
    have h3' : run0 p (normCost a (n+1)) ⟨q,P++rep ZB (n+1)++OB++S,R⟩ =
        some ⟨q,P++rep OB (n+1)++OB++S,R⟩ := by
      simpa only [List.append_assoc] using h3
    have H := join0 (join0 h1' h2) h3'
    simpa only [initCost,rep_right ZB n,rep_right OB (n+1),List.append_assoc] using H

/-- Padding-sensitive counter.  The carry step increases the padding index,
    but the block-normalization induction does not require a closed form
    for the elapsed time. -/
def pad : Nat → List Bool := fun k => [false,false,false,false] ++ rep [false,false] k ++ [true]
def padFrame (k : Nat) (w : List Bool) : Z0 := ⟨3,pad k ++ w,[]⟩
def Reaches (p : PartialMachine) (c d : Z0) : Prop :=
  ∃ t, run0 p t c = some d
def PosReach (p : PartialMachine) (c d : Z0) : Prop :=
  ∃ t, 0 < t ∧ run0 p t c = some d

theorem padNormalize (p : PartialMachine)
    (inc : ∀ k n S, Reaches p (padFrame k (rep OB n ++ ZB ++ S))
      (padFrame (k+1) (rep ZB n ++ OB ++ S)))
    (n k : Nat) (S : List Bool) :
    ∃ k', Reaches p (padFrame k (rep ZB n ++ S))
      (padFrame k' (rep OB n ++ S)) := by
  induction n generalizing k S with
  | zero => exact ⟨k,0,rfl⟩
  | succ n ih =>
    obtain ⟨k1,t1,h1⟩ := ih k (ZB++S)
    obtain ⟨t2,h2⟩ := inc k1 n S
    obtain ⟨k2,t3,h3⟩ := ih (k1+1) (OB++S)
    have h1' : run0 p t1 (padFrame k (rep ZB n++ZB++S)) =
        some (padFrame k1 (rep OB n++ZB++S)) := by
      simpa only [List.append_assoc] using h1
    have h3' : run0 p t3 (padFrame (k1+1) (rep ZB n++OB++S)) =
        some (padFrame k2 (rep OB n++OB++S)) := by
      simpa only [List.append_assoc] using h3
    refine ⟨k2,t1+t2+t3,?_⟩
    simpa only [rep_right ZB n,rep_right OB n,List.append_assoc] using
      join0 (join0 h1' h2) h3'

theorem padNormalizeInit (p : PartialMachine)
    (inc : ∀ k n S, Reaches p (padFrame k (rep OB n ++ ZB ++ S))
      (padFrame (k+1) (rep ZB n ++ OB ++ S)))
    (n k : Nat) (S : List Bool) :
    ∃ k', Reaches p (padFrame k (OB ++ rep ZB n ++ S))
      (padFrame k' (rep OB (n+1) ++ S)) := by
  induction n generalizing k S with
  | zero => exact ⟨k,0,rfl⟩
  | succ n ih =>
    obtain ⟨k1,t1,h1⟩ := ih k (ZB++S)
    obtain ⟨t2,h2⟩ := inc k1 (n+1) S
    obtain ⟨k2,t3,h3⟩ := padNormalize p inc (n+1) (k1+1) (OB++S)
    have h1' : run0 p t1 (padFrame k (OB++rep ZB n++ZB++S)) =
        some (padFrame k1 (rep OB (n+1)++ZB++S)) := by
      simpa only [List.append_assoc] using h1
    have h3' : run0 p t3 (padFrame (k1+1) (rep ZB (n+1)++OB++S)) =
        some (padFrame k2 (rep OB (n+1)++OB++S)) := by
      simpa only [List.append_assoc] using h3
    refine ⟨k2,t1+t2+t3,?_⟩
    simpa only [rep_right ZB n,rep_right OB (n+1),List.append_assoc] using
      join0 (join0 h1' h2) h3'

def PadInvariant (c : Z0) : Prop :=
  ∃ k n, c = padFrame k (rep OB n ++ [false,true])

theorem padProgress (p : PartialMachine)
    (inc : ∀ k n S, Reaches p (padFrame k (rep OB n ++ ZB ++ S))
      (padFrame (k+1) (rep ZB n ++ OB ++ S)))
    (fin : ∀ k n, PosReach p (padFrame k (rep OB n ++ [false,true]))
      (padFrame k (OB ++ rep ZB n ++ [false,true])))
    (c : Z0) (hc : PadInvariant c) :
    ∃ t d, 0 < t ∧ run0 p t c = some d ∧ PadInvariant d := by
  obtain ⟨k,n,rfl⟩ := hc
  obtain ⟨t1,hpos,h1⟩ := fin k n
  obtain ⟨k',t2,h2⟩ := padNormalizeInit p inc n k [false,true]
  exact ⟨t1+t2,_,by omega,join0 h1 h2,k',n+1,rfl⟩

theorem arbitraryLive_of_progress (p : PartialMachine) (I : Z0 → Prop)
    (entry : Nat) (c : Z0) (first : run0 p entry ⟨0,[],[]⟩ = some c)
    (initial : I c)
    (progress : ∀ z, I z → ∃ t d, 0 < t ∧ run0 p t z = some d ∧ I d)
    (n : Nat) :
    ∃ t z, n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some z ∧ I z := by
  induction n with
  | zero => exact ⟨entry,c,by omega,first,initial⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hi⟩ := ih
    obtain ⟨u,d,hu,hd,hi'⟩ := progress z hi
    exact ⟨t+u,d,by omega,join0 hr hd,hi'⟩

/-- Transfer unbounded live prefixes to every compatible original machine. -/
theorem never_of_progress (p : PartialMachine) (I : Z0 → Prop)
    (entry : Nat) (c : Z0) (first : run0 p entry ⟨0,[],[]⟩ = some c)
    (initial : I c)
    (progress : ∀ z, I z → ∃ t d, 0 < t ∧ run0 p t z = some d ∧ I d)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := arbitraryLive_of_progress p I entry c first initial progress n
  have hz : (zrun p t BB6Coverage.Agent31Pump.start).map project = some z :=
    (run_project p t BB6Coverage.Agent31Pump.start).trans hr
  cases h : zrun p t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some zz =>
    have H := zrun_sound p m hm t BB6Coverage.Agent31Pump.start zz h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms normalize
#print axioms normalizeInit
#print axioms padNormalize
#print axioms padNormalizeInit
#print axioms padProgress
#print axioms arbitraryLive_of_progress
#print axioms never_of_progress
end BB6.Agent48Counter
