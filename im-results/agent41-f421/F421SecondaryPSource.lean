import F421SecondaryInduction
import F421SourceLifetimeBridge

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

/-- A physical P vector does not observe the Q decrement. -/
theorem projectionDec (cs : List PC) :
    pProjection (dec cs) = (pProjection cs).map (· - 1) := by
  simp [pProjection,dec,List.map_map,Function.comp_def]

theorem projectionTrimQ (B : Nat) (cs : List PC) :
    pProjection (trimQ B cs)=pProjection cs := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih =>
    simpa [trimQ,pProjection] using ih (2*B)

theorem physicalP_append (B : Nat) (xs ys : List Nat) :
    physicalP B (xs++ys) = physicalP B xs ++ physicalP (B*2^xs.length) ys := by
  induction xs generalizing B with
  | nil => simp [physicalP]
  | cons x xs ih =>
    simp only [List.cons_append,physicalP,List.length_cons,List.cons.injEq,eq_self_iff_true,true_and]
    rw [ih]
    congr 1
    rw [Nat.pow_succ]
    ac_rfl

theorem physicalPLength (B : Nat) (xs : List Nat) :
    (physicalP B xs).length=xs.length := by
  induction xs generalizing B with
  | nil => rfl
  | cons x xs ih => simp [physicalP,ih]

theorem firstTwoP (p0 q0 p1 q1 : Nat) (hs : List PC)
    (h0 : 3≤p0) (h1 : 5≤p1) :
    pProjection (drain 0 0 (dec (⟨p0,q0⟩::⟨p1,q1⟩::hs))).1 =
      (p0-2)::(p1-4)::pProjection (drain 3 0 (dec hs)).1 := by
  have a0 : ¬p0-1≤1 := by omega
  have a1 : ¬p1-1≤3 := by omega
  simp only [dec,List.map_cons,drain,ite_eq_right a0,ite_eq_right a1,pProjection,List.map_cons]
  congr 1 <;> omega

/-- Exact physical P successor for two protected far cells.
    Independent of all Q values and full large-integer recurrence. -/
theorem secondarySourceP (b p0 q0 p1 q1 : Nat) (hs : List PC) (xs : List Nat)
    (h0 : 3≤p0) (h1 : 5≤p1) (hp : Positive xs)
    (hhs : pProjection hs=physicalP 4 xs) :
    pProjection (sNext b (⟨p0,q0⟩::⟨p1,q1⟩::hs)).2.2 =
    (p0-2)::(p1-4)::physicalP 4 (advance xs) := by
  have hdec : pProjection (dec hs) = markedPhysicalP 4 xs := by
    rw [projectionDec,hhs]; rfl
  rcases ha : advanceAux 0 xs with ⟨ys,D⟩
  have hL := originalDrainLifetime 4 4 0 0 xs (dec hs) (by decide)
    (by decide) hp hdec
  rw [ha] at hL
  rcases hd : drain 3 0 (dec hs) with ⟨as,A,rA⟩
  rw [hd] at hL
  change pProjection as = physicalP 4 ys at hL
  have hlen : as.length=ys.length := by
    have h := congrArg List.length hL
    simpa [pProjection,physicalPLength] using h
  have h0' : ¬p0-1≤1 := by omega
  have h1' : ¬p1-1≤3 := by omega
  have hfull : drain 0 0 (dec (⟨p0,q0⟩::⟨p1,q1⟩::hs)) =
      (⟨p0-2,q0+1⟩::⟨p1-4,q1+2⟩::as,A,rA) := by
    simp only [dec,List.map_cons,drain,ite_eq_right h0',ite_eq_right h1']
    change (⟨p0-1-1,q0+1⟩::⟨p1-1-3,q1+2⟩::(drain 3 0 (dec hs)).1,
      (drain 3 0 (dec hs)).2.1,(drain 3 0 (dec hs)).2.2) = _
    rw [hd]
    congr 2 <;> omega
  unfold sNext
  rw [hfull]
  simp only [Prod.fst,Prod.snd]
  change pProjection (trimQ 1 (⟨p0-2,q0+1⟩::⟨p1-4,q1+2⟩::as) ++
       [⟨4*2^((⟨p0,q0⟩::⟨p1,q1⟩::hs).length),b+1+A+rA-2^((⟨p0-2,q0+1⟩::⟨p1-4,q1+2⟩::as).length)⟩]) = _
  simp only [pProjection,List.map_append,List.map_cons,List.map_nil,List.append_nil]
  rw [show (trimQ 1 (⟨p0-2,q0+1⟩::⟨p1-4,q1+2⟩::as)).map Cell.p =
      pProjection (⟨p0-2,q0+1⟩::⟨p1-4,q1+2⟩::as) by exact projectionTrimQ 1 _]
  simp only [pProjection,List.map_cons]
  rw [show as.map Cell.p=physicalP 4 ys from hL]
  unfold advance
  rw [ha]
  rw [physicalP_append]
  have hlength := advanceAux_length 0 xs
  rw [ha] at hlength
  simp only [Prod.fst,Prod.snd,Nat.add_zero] at hlength
  have hslen : hs.length=xs.length := by
    have h := congrArg List.length hhs
    simpa [pProjection,physicalPLength] using h
  have hpower : 4*2^((⟨p0,q0⟩::⟨p1,q1⟩::hs).length) =
      2*(4*2^ys.length)*2^(D+1) := by
    simp only [List.length_cons,hslen]
    have hpows : 2^(xs.length+2)=2^ys.length*2^(D+2) := by
      rw [←Nat.pow_add]
      congr 1
      omega
    rw [show xs.length+1+1=xs.length+2 by omega,hpows,Nat.pow_succ]
    ac_rfl
  simp only [List.length_cons,pProjection] at hpower ⊢
  simp only [physicalP,physicalPLength]
  rw [hpower]
  simp [List.append_assoc]

#print axioms firstTwoP
#print axioms secondarySourceP
end F421SecondaryLifetimes
