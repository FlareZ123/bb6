import SweepPumping
namespace BB6.Agent1Raw60LFUnaryCore
open BB6Coverage BB6Coverage.Agent31Pump
abbrev U (k : Nat) := List.replicate k true
abbrev Q (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,L,R⟩
abbrev F := Q 5
abbrev Reach (p : PartialMachine) (a b : Z0) := ∃ t : Nat, run0 p t a = some b

theorem trans {p : PartialMachine} {a b c : Z0} (h : Reach p a b) (g : Reach p b c) : Reach p a c := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨u,hu⟩ := g
  exact ⟨t+u,join0 ht hu⟩

def Fill (p : PartialMachine) (k : Nat) (q : Fin 6) : Prop :=
  ∀ (b : Bool) (L R : List Bool), Reach p (F (false::L) (U k++b::R)) (Q q (b::(U k++false::L)) R)

theorem sweep (p : PartialMachine) (hf : p (5,true) = some (some ⟨true,false,5⟩)) (k : Nat) (L R : List Bool) :
    run0 p k (F (U k++L) R) = some (F L (U k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 p 1 (F (U (k+1)++L) R) = some (F (U k++L) (true::R)) := by simp [run0,step0,move0,hf,List.replicate_succ]
    have H := join0 h (ih (true::R))
    have he : U k++true::R=U (k+1)++R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
    rw [he,Nat.add_comm 1 k] at H
    exact H

theorem direct {p : PartialMachine} {k : Nat} {q z : Fin 6}
    (h : Fill p k q) (hr : p (q,true) = some (some ⟨true,true,z⟩)) : Fill p (k+1) z := by
  intro b L R
  have h1 := h true L (b::R)
  have h2 : run0 p 1 (Q q (true::(U k++false::L)) (b::R)) = some (Q z (b::(U (k+1)++false::L)) R) := by simp [run0,step0,move0,hr,List.replicate_succ]
  have he : U k++true::b::R = U (k+1)++b::R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
  rw [he] at h1
  exact trans h1 ⟨1,h2⟩

theorem reset {p : PartialMachine} {k : Nat} {q z : Fin 6}
    (h : Fill p k q) (hf : p (5,true) = some (some ⟨true,false,5⟩))
    (h1 : p (q,true) = some (some ⟨false,false,5⟩))
    (h0 : p (q,false) = some (some ⟨true,true,z⟩)) : Fill p (k+1) z := by
  intro b L R
  have ha := h true L (b::R)
  have hb : run0 p 1 (Q q (true::(U k++false::L)) (b::R)) = some (F (U k++false::L) (false::b::R)) := by simp [run0,step0,move0,h1]
  have hc := sweep p hf k (false::L) (false::b::R)
  have hd := h false L (b::R)
  have he : run0 p 1 (Q q (false::(U k++false::L)) (b::R)) = some (Q z (b::(U (k+1)++false::L)) R) := by simp [run0,step0,move0,h0,List.replicate_succ]
  have hh : U k++true::b::R = U (k+1)++b::R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
  rw [hh] at ha
  exact trans ha (trans ⟨1,hb⟩ (trans ⟨k,hc⟩ (trans hd ⟨1,he⟩)))

end BB6.Agent1Raw60LFUnaryCore
