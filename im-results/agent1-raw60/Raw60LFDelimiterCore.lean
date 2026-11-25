import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFDelimiterCore
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
def FillS (p : PartialMachine) (S : List Bool) (k : Nat) (q : Fin 6) : Prop :=
  ∀ (b : Bool) (L R : List Bool), Reach p (F (S++L) (U k++b::R)) (Q q (b::(U k++(S++L))) R)

theorem directS {p : PartialMachine} {S : List Bool} {k : Nat} {q z : Fin 6}
    (h : FillS p S k q) (hr : p (q,true) = some (some ⟨true,true,z⟩)) : FillS p S (k+1) z := by
  intro b L R
  have h1 := h true L (b::R)
  have h2 : run0 p 1 (Q q (true::(U k++(S++L))) (b::R)) = some (Q z (b::(U (k+1)++(S++L))) R) := by simp [run0,step0,move0,hr,List.replicate_succ]
  have he : U k++true::b::R = U (k+1)++b::R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
  rw [he] at h1
  exact reachTrans h1 ⟨1,h2⟩

theorem resetS {p : PartialMachine} {S : List Bool} {k : Nat} {q z : Fin 6}
    (h : FillS p S k q) (hf : p (5,true) = some (some ⟨true,false,5⟩))
    (h1 : p (q,true) = some (some ⟨false,false,5⟩))
    (h0 : p (q,false) = some (some ⟨true,true,z⟩)) : FillS p S (k+1) z := by
  intro b L R
  have ha := h true L (b::R)
  have hb : run0 p 1 (Q q (true::(U k++(S++L))) (b::R)) = some (F (U k++(S++L)) (false::b::R)) := by simp [run0,step0,move0,h1]
  have hc := sweep p hf k (S++L) (false::b::R)
  have hd := h false L (b::R)
  have he : run0 p 1 (Q q (false::(U k++(S++L))) (b::R)) = some (Q z (b::(U (k+1)++(S++L))) R) := by simp [run0,step0,move0,h0,List.replicate_succ]
  have hh : U k++true::b::R = U (k+1)++b::R := by unfold U; rw [List.replicate_succ']; simp [List.append_assoc]
  rw [hh] at ha
  exact reachTrans ha (reachTrans ⟨1,hb⟩ (reachTrans ⟨k,hc⟩ (reachTrans hd ⟨1,he⟩)))

end BB6.Agent1Raw60LFDelimiterCore
