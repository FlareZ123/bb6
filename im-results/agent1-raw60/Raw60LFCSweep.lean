import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFCSweep
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none
abbrev C := Q 2

def FillC (k : Nat) (q : Fin 6) : Prop :=
  ∀ (b : Bool) (L R : List Bool), Reach table (C (false::L) (U k++b::R)) (Q q (b::(U k++false::L)) R)

theorem sweepC (k : Nat) (L R : List Bool) : run0 table k (C (U k++L) R) = some (C L (U k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 (C (U (k+1)++L) R) = some (C (U k++L) (true::R)) := by rfl
    have H := join0 h (ih (true::R))
    have he : U k++true::R=U (k+1)++R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
    rw [he,Nat.add_comm 1 k] at H
    exact H

theorem dir {k : Nat} {q z : Fin 6} (h : FillC k q) (hr : table (q,true) = some (some ⟨true,true,z⟩)) : FillC (k+1) z := by
  intro b L R
  have h1 := h true L (b::R)
  have h2 : run0 table 1 (Q q (true::(U k++false::L)) (b::R)) = some (Q z (b::(U (k+1)++false::L)) R) := by simp [run0,step0,move0,hr,List.replicate_succ]
  have he : U k++true::b::R=U (k+1)++b::R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
  rw [he] at h1
  exact reachTrans h1 ⟨1,h2⟩

theorem resetC (k : Nat) (h : FillC (k+1) 0) : FillC (k+2) 1 := by
  intro b L R
  have ha := h true L (b::R)
  have hb : run0 table 2 (Q 0 (true::(U (k+1)++false::L)) (b::R)) = some (C (U k++false::L) (true::false::b::R)) := by rfl
  have hc := sweepC k (false::L) (true::false::b::R)
  have hd := h false L (b::R)
  have he : run0 table 1 (Q 0 (false::(U (k+1)++false::L)) (b::R)) = some (Q 1 (b::(U (k+2)++false::L)) R) := by rfl
  have hh : U (k+1)++true::b::R = U (k+2)++b::R := by
    change U (k+1)++(U 1++b::R)=_
    rw [← List.append_assoc,List.replicate_append_replicate]
  have hj : U k++true::false::b::R = U (k+1)++false::b::R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
  rw [hh] at ha
  rw [hj] at hc
  exact reachTrans ha (reachTrans ⟨2,hb⟩ (reachTrans ⟨k,hc⟩ (reachTrans hd ⟨1,he⟩)))

theorem base : FillC 4 3 := by intro b L R; cases b <;> exact ⟨11,by rfl⟩
theorem fillPhase (n : Nat) : FillC (4*n+4) 3 := by
  induction n with
  | zero => exact base
  | succ n ih =>
    have h1 : FillC (4*n+5) 4 := dir ih (by rfl)
    have h2 : FillC (4*n+6) 0 := dir h1 (by rfl)
    have h3 : FillC (4*n+7) 1 := resetC (4*n+5) h2
    have h4 : FillC (4*n+8) 3 := dir h3 (by rfl)
    rw [show 4*(n+1)+4=4*n+8 by omega]
    exact h4

def family (n : Nat) : Z0 := C [false] (U (4*n+8)++[false])
theorem entry : run0 table 81 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h := fillPhase (n+1)
  rw [show 4*(n+1)+4=4*n+8 by omega] at h
  obtain ⟨a,ha⟩ := h false [] []
  have hb : run0 table 12 (Q 3 (false::(U (4*n+8)++[false])) []) = some (C (U (4*n+11)++[false]) [true,false]) := by rfl
  have hc := sweepC (4*n+11) [false] [true,false]
  have he : U (4*n+11)++[true,false]=U (4*n+12)++[false] := by
    change U (4*n+11)++(U 1++[false])=_
    rw [← List.append_assoc,List.replicate_append_replicate]
  rw [he] at hc
  unfold family
  rw [show 4*(n+1)+8=4*n+12 by omega]
  exact ⟨a+12+(4*n+11),by omega,join0 (join0 ha hb) hc⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 81 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end BB6.Agent1Raw60LFCSweep
