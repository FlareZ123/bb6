import SweepPumping

namespace BB6Coverage.Agent31Pump.Guarded
open BB6Coverage BB6Coverage.Agent31Pump

/-- The local frame may have an explicitly closed blank side. On an open
    side, accessing the unknown tail is rejected. -/
def readHead (closed : Bool) : List Bool → Option Bool
  | [] => if closed then some false else none
  | a::_ => some a

theorem readHead_sound {closed : Bool} {xs : List Bool} {a : Bool}
    (h : readHead closed xs = some a) (tail : List Bool)
    (hc : closed = true → tail = []) :
    (xs++tail).headD false = a ∧ (xs++tail).tail = xs.tail++tail := by
  cases xs with
  | nil =>
    cases closed with
    | false => simp [readHead] at h
    | true =>
      simp [readHead] at h
      subst a
      rw [hc rfl]
      decide
  | cons x xs =>
    simp [readHead] at h
    subst a
    exact ⟨rfl,rfl⟩

def extend (z : Z0) (L R : List Bool) : Z0 := ⟨z.q,z.l++L,z.r++R⟩

def guardStep (p : PartialMachine) (lc rc : Bool) (z : Z0) : Option Z0 :=
  match readHead lc z.l with
  | none => none
  | some a =>
    match (p (z.q,a)).bind id with
    | none => none
    | some mv =>
      if mv.right then
        match readHead rc z.r with
        | none => none
        | some b => some ⟨mv.next,b::mv.write::z.l.tail,z.r.tail⟩
      else some ⟨mv.next,z.l.tail,mv.write::z.r⟩

theorem guardStep_sound (p : PartialMachine) {lc rc : Bool} {z z' : Z0}
    (h : guardStep p lc rc z = some z') (L R : List Bool)
    (hL : lc=true → L=[]) (hR : rc=true → R=[]) :
    step0 p (extend z L R) = some (extend z' L R) := by
  unfold guardStep at h
  cases ha : readHead lc z.l with
  | none => simp [ha] at h
  | some a =>
    simp only [ha] at h
    obtain ⟨ha',hl⟩ := readHead_sound ha L hL
    cases hm : (p (z.q,a)).bind id with
    | none => simp [hm] at h
    | some mv =>
      simp only [hm] at h
      cases hd : mv.right
      · simp [hd] at h
        subst z'
        unfold step0
        change ((p (z.q,(z.l++L).headD false)).bind id).map (fun mv => move0 mv (extend z L R)) = _
        rw [ha',hm]
        simp only [Option.map_some,move0,hd,ite_false,Bool.false_eq_true]
        unfold extend
        rw [hl]
        rfl
      · simp only [hd,ite_true] at h
        cases hb : readHead rc z.r with
        | none => simp [hb] at h
        | some b =>
          simp [hb] at h
          subst z'
          obtain ⟨hb',hr⟩ := readHead_sound hb R hR
          unfold step0
          change ((p (z.q,(z.l++L).headD false)).bind id).map (fun mv => move0 mv (extend z L R)) = _
          rw [ha',hm]
          simp only [Option.map_some,move0,hd,ite_true]
          unfold extend
          rw [hl,hb',hr]
          rfl

def guardRun (p : PartialMachine) (lc rc : Bool) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => (guardStep p lc rc z).bind (guardRun p lc rc n)

theorem guardRun_sound (p : PartialMachine) (lc rc : Bool) (n : Nat) {z z' : Z0}
    (h : guardRun p lc rc n z = some z') (L R : List Bool)
    (hL : lc=true → L=[]) (hR : rc=true → R=[]) :
    run0 p n (extend z L R) = some (extend z' L R) := by
  induction n generalizing z with
  | zero => simp [guardRun] at h; subst z'; rfl
  | succ n ih =>
    simp only [guardRun] at h
    cases hs : guardStep p lc rc z with
    | none => simp [hs] at h
    | some t =>
      simp only [hs,Option.bind_some] at h
      simp only [run0,guardStep_sound p hs L R hL hR,Option.bind_some]
      exact ih h

#print axioms guardRun_sound
end BB6Coverage.Agent31Pump.Guarded
