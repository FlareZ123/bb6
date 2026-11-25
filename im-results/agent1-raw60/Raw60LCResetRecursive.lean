import SweepPumping
namespace BB6.Agent1Raw60LCResetRecursive
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
inductive V where | m386 | m488 deriving DecidableEq

def table (v : V) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨v = .m488,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => none
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
abbrev U (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false
abbrev Q (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,L,R⟩
abbrev A := Q 0
abbrev C := Q 2
abbrev D := Q 3
abbrev F := Q 5

def s : V → Nat | .m386 => 2 | .m488 => 3
def K (v : V) (n : Nat) := s v*n+2

theorem merge (a b : Nat) (x : Bool) (L : List Bool) :
    List.replicate a x ++ (List.replicate b x ++ L) = List.replicate (a+b) x ++ L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem sweepF (v : V) (a : Nat) (L R : List Bool) :
    run0 (table v) (a+1) (F (true::L) (U a++false::R)) = some (F (false::(Z (a+1)++L)) R) := by
  induction a generalizing L with
  | zero => cases v <;> rfl
  | succ a ih =>
    have h : run0 (table v) 1 (F (true::L) (U (a+1)++false::R)) = some (F (true::false::L) (U a++false::R)) := by cases v <;> rfl
    have H := join0 h (ih (false::L))
    have e : Z (a+1)++false::L = Z (a+1+1)++L := by rw [← merge (a+1) 1 false]; rfl
    rw [e,show 1+(a+1)=a+1+1 by omega] at H
    exact H

theorem sweepD (v : V) (a : Nat) (L R : List Bool) :
    run0 (table v) a (D (Z a++L) R) = some (D L (U a++R)) := by
  induction a generalizing R with
  | zero => rfl
  | succ a ih =>
    have h : run0 (table v) 1 (D (Z (a+1)++L) R) = some (D (Z a++L) (true::R)) := by cases v <;> rfl
    have H := join0 h (ih (true::R))
    have e : U a++true::R = U (a+1)++R := by rw [← merge a 1 true]; rfl
    rw [e,Nat.add_comm 1 a] at H
    exact H

theorem sweepC (v : V) (a : Nat) (L R : List Bool) :
    run0 (table v) a (C (U a++L) R) = some (C L (U a++R)) := by
  induction a generalizing R with
  | zero => rfl
  | succ a ih =>
    have h : run0 (table v) 1 (C (U (a+1)++L) R) = some (C (U a++L) (true::R)) := by cases v <;> rfl
    have H := join0 h (ih (true::R))
    have e : U a++true::R = U (a+1)++R := by rw [← merge a 1 true]; rfl
    rw [e,Nat.add_comm 1 a] at H
    exact H

theorem clear (v : V) (a : Nat) (L R : List Bool) :
    run0 (table v) (1+a) (A (true::(U a++L)) R) = some (C L (U a++false::R)) := by
  have h : run0 (table v) 1 (A (true::(U a++L)) R) = some (C (U a++L) (false::R)) := by cases v <;> rfl
  exact join0 h (sweepC v a L (false::R))

theorem fstage (v : V) (k a : Nat) (L R : List Bool) :
    run0 (table v) (a+s v) (A (false::(U k++false::L)) (U (a+(s v-1))++false::R)) =
      some (F (false::(Z (a+1)++(U (k+s v-1)++false::L))) R) := by
  cases v with
  | m386 =>
    cases a with
    | zero => rfl
    | succ a =>
      have h : run0 (table .m386) 2 (A (false::(U k++false::L)) (U (a+1+(s .m386-1))++false::R)) =
        some (F (true::false::true::(U k++false::L)) (U a++false::R)) := by rfl
      have H := join0 h (sweepF .m386 a (false::true::(U k++false::L)) R)
      have e : Z (a+1)++false::true::(U k++false::L) = Z (a+1+1)++(U (k+s .m386-1)++false::L) := by
        rw [← merge (a+1) 1 false]; rfl
      rw [e,show 2+(a+1)=a+1+s .m386 by simp [s]; omega] at H
      exact H
  | m488 =>
    have h : run0 (table .m488) 2 (A (false::(U k++false::L)) (U (a+(s .m488-1))++false::R)) =
      some (F (true::true::true::(U k++false::L)) (U a++false::R)) := by rfl
    have H := join0 h (sweepF .m488 a (true::true::(U k++false::L)) R)
    rw [show 2+(a+1)=a+s .m488 by simp [s]; omega] at H
    exact H

def advCost (v : V) (a : Nat) := a+s v+1+(a+1)+2

theorem advance (v : V) (k a : Nat) (L R : List Bool) :
    run0 (table v) (advCost v a) (A (false::(U k++false::L)) (U (a+(s v-1))++false::R)) =
    some (A ((U a++false::R).headD false::(U (k+s v)++false::L)) (U a++false::R).tail) := by
  have h1 := fstage v k a L R
  have h2 : run0 (table v) 1 (F (false::(Z (a+1)++(U (k+s v-1)++false::L))) R) =
      some (D (Z (a+1)++(U (k+s v-1)++false::L)) (false::R)) := by cases v <;> rfl
  have h3 := sweepD v (a+1) (U (k+s v-1)++false::L) (false::R)
  have h4 : run0 (table v) 2 (D (U (k+s v-1)++false::L) (U (a+1)++false::R)) =
      some (A ((U a++false::R).headD false::(U (k+s v)++false::L)) (U a++false::R).tail) := by cases v <;> cases a <;> rfl
  exact join0 (join0 (join0 h1 h2) h3) h4

abbrev Reach (v : V) (a b : Z0) := ∃ t : Nat, run0 (table v) t a = some b

theorem reach_join {v : V} {a b c : Z0} (h : Reach v a b) (g : Reach v b c) : Reach v a c := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨u,hu⟩ := g
  exact ⟨t+u,join0 ht hu⟩

def Fill (v : V) (n : Nat) : Prop := ∀ L R : List Bool,
    Reach v (C (false::L) (U (K v n)++false::R)) (A (false::(U (K v n)++false::L)) R)

theorem k_succ (v : V) (n : Nat) : K v (n+1)=K v n+s v := by cases v <;> simp [K,s] <;> omega

theorem chain (v : V) (d j : Nat) (L R : List Bool)
    (hfill : ∀ i, j<i → i≤j+d → Fill v i) :
    Reach v (A (false::(U (K v j)++false::L)) (U (s v*(d+1)-1)++false::R))
      (A (false::(U (K v (j+d+1))++false::L)) R) := by
  induction d generalizing j with
  | zero =>
    have H := advance v (K v j) 0 L R
    rw [← k_succ] at H
    cases v <;> exact ⟨_,H⟩
  | succ d ih =>
    let a := s v*(d+1)
    have ha : 0<a := by cases v <;> simp [a,s] <;> omega
    have H := advance v (K v j) a L R
    have he : a+(s v-1)=s v*(d+1+1)-1 := by cases v <;> simp [a,s] <;> omega
    rw [he,← k_succ] at H
    have hsplit : U a++false::R = true::(U (a-1)++false::R) := by
      rw [← show a-1+1=a by omega]; rfl
    rw [hsplit] at H
    change run0 (table v) (advCost v a) _ = some (A (true::(U (K v (j+1))++false::L)) (U (a-1)++false::R)) at H
    have hc := clear v (K v (j+1)) (false::L) (U (a-1)++false::R)
    have hf := hfill (j+1) (by omega) (by omega) L (U (a-1)++false::R)
    have ht := ih (j+1) (fun i hi hi' => hfill i (by omega) (by omega))
    rw [show j+1+d+1=j+(d+1)+1 by omega] at ht
    exact reach_join ⟨_,H⟩ (reach_join ⟨_,hc⟩ (reach_join hf ht))

theorem fill (v : V) (n : Nat) : Fill v n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro L R
    cases n with
    | zero => exact ⟨3,by cases v <;> rfl⟩
    | succ n =>
      let a := s v*(n+1)-1
      have he : K v (n+1)=a+3 := by cases v <;> simp [K,s,a] <;> omega
      have h0 : run0 (table v) 6 (C (false::L) (U (K v (n+1))++false::R)) =
          some (C (false::L) (true::true::false::(U a++false::R))) := by rw [he]; cases v <;> rfl
      have h1 := ih 0 (by omega) L (U a++false::R)
      have h2 := chain v n 0 L R (fun i _ hi => ih i (by omega))
      rw [Nat.zero_add] at h2
      exact reach_join ⟨6,h0⟩ (reach_join h1 h2)

theorem chainExtra (d j : Nat) (L R : List Bool) :
    Reach .m386 (A (false::(U (K .m386 j)++false::L)) (U (2*(d+1))++false::R))
      (A (false::(U (K .m386 (j+d+1))++false::L)) (false::R)) := by
  induction d generalizing j with
  | zero =>
    have h1 := advance .m386 (K .m386 j) 1 L R
    rw [← k_succ] at h1
    have h2 := clear .m386 (K .m386 (j+1)) (false::L) (false::R)
    have h3 := fill .m386 (j+1) L (false::R)
    exact reach_join ⟨_,h1⟩ (reach_join ⟨_,h2⟩ h3)
  | succ d ih =>
    have h1 := advance .m386 (K .m386 j) (2*(d+1)+1) L R
    rw [← k_succ] at h1
    have h2 := clear .m386 (K .m386 (j+1)) (false::L) (U (2*(d+1))++false::R)
    have h3 := fill .m386 (j+1) L (U (2*(d+1))++false::R)
    have h4 := ih (j+1)
    rw [show j+1+d+1=j+(d+1)+1 by omega] at h4
    exact reach_join ⟨_,h1⟩ (reach_join ⟨_,h2⟩ (reach_join h3 h4))

theorem extraFill (n : Nat) (L R : List Bool) :
    Reach .m386 (C (false::L) (U (K .m386 n+1)++false::R))
      (A (false::(U (K .m386 n)++false::L)) (false::R)) := by
  have h1 : run0 (table .m386) 6 (C (false::L) (U (K .m386 n+1)++false::R)) =
      some (C (false::L) (true::true::false::(U (2*n)++false::R))) := by rfl
  have h2 := fill .m386 0 L (U (2*n)++false::R)
  cases n with
  | zero => exact reach_join ⟨_,h1⟩ h2
  | succ n =>
    have h3 := chainExtra n 0 L R
    rw [Nat.zero_add] at h3
    exact reach_join ⟨_,h1⟩ (reach_join h2 h3)

def family386 (n : Nat) : Z0 := A (false::(U (K .m386 n)++[false])) [false]
def family488 (n : Nat) : Z0 := A (false::(U (K .m488 (n+1))++[false])) []

theorem entry386 : run0 (table .m386) 20 ⟨0,[],[]⟩ = some (family386 0) := by rfl
theorem entry488 : run0 (table .m488) 49 ⟨0,[],[]⟩ = some (family488 0) := by rfl

theorem growth386_exists (n : Nat) : ∃ t, 0<t ∧ run0 (table .m386) t (family386 n) = some (family386 (n+1)) := by
  let k := K .m386 (n+1)+1
  have h1 : run0 (table .m386) 7 (family386 n) = some (A (true::(U k++[false])) []) := by rfl
  have h2 := clear .m386 k [false] []
  obtain ⟨t,h3⟩ := extraFill (n+1) [] []
  exact ⟨7+(1+k)+t,by omega,join0 (join0 h1 h2) h3⟩

theorem growth488_exists (n : Nat) : ∃ t, 0<t ∧ run0 (table .m488) t (family488 n) = some (family488 (n+1)) := by
  let k := K .m488 (n+2)
  have h1 : run0 (table .m488) 7 (family488 n) = some (A (true::(U k++[false])) []) := by rfl
  have h2 := clear .m488 k [false] []
  obtain ⟨t,h3⟩ := fill .m488 (n+2) [] []
  exact ⟨7+(1+k)+t,by omega,join0 (join0 h1 h2) h3⟩
#print axioms growth386_exists
#print axioms growth488_exists
#print axioms advance
#print axioms chain
#print axioms fill
namespace M386
def table : PartialMachine := BB6.Agent1Raw60LCResetRecursive.table .m386
noncomputable def cost (n : Nat) : Nat := Classical.choose (growth386_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family386 20 cost entry386
    (fun n => (Classical.choose_spec (growth386_exists n)).1)
    (fun n => (Classical.choose_spec (growth386_exists n)).2) m hm
#print axioms never
end M386
namespace M488
def table : PartialMachine := BB6.Agent1Raw60LCResetRecursive.table .m488
noncomputable def cost (n : Nat) : Nat := Classical.choose (growth488_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family488 49 cost entry488
    (fun n => (Classical.choose_spec (growth488_exists n)).1)
    (fun n => (Classical.choose_spec (growth488_exists n)).2) m hm
#print axioms never
end M488
end BB6.Agent1Raw60LCResetRecursive
