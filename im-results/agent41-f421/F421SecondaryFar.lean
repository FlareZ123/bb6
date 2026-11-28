import F421SecondaryLifeIter

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

theorem nextFarQ (b p0 q0 p1 q1 : Nat) (hs : List PC)
    (h0 : 3≤p0) (h1 : 5≤p1) :
    ∃ a' b' ds, sNext b (⟨p0,q0⟩::⟨p1,q1⟩::hs) =
      (a',b',⟨p0-2,q0⟩::⟨p1-4,q1⟩::ds) := by
  have g0 : ¬p0-1≤1 := by omega
  have g1 : ¬p1-1≤3 := by omega
  rcases he : drain 3 0 (dec hs) with ⟨as,A,r⟩
  refine ⟨4*2^(as.length+2)-1,6*2^(as.length+2)-1,
    trimQ 4 as++[⟨4*2^((⟨p0,q0⟩::⟨p1,q1⟩::hs).length),
       b+1+A+r-2^(as.length+2)⟩],?_⟩
  unfold sNext
  simp only [dec,List.map_cons,drain,ite_eq_right g0,ite_eq_right g1,he,
    trimQ,List.length_cons,Prod.fst,Prod.snd]
  have hp0 : p0-1-1=p0-2 := by omega
  have hp1 : p1-1-3=p1-4 := by omega
  have hq0 : q0+1-1=q0 := by omega
  have hq1 : q1+2-2=q1 := by omega
  simp only [hp0,hp1,hq0,hq1]
  simp only [show 2*(2*0+1)+1=3 by decide,show 2*(2*1)=4 by decide]
  have he' : drain 3 0 (List.map (fun c : PC => ⟨c.p-1,c.q⟩) hs) = (as,A,r) := by
    simpa [dec] using he
  rw [he']
  rfl

theorem nextShapeFar (b p0 q0 p1 q1 : Nat) (hs : List PC) (xs : List Nat)
    (h0 : 3≤p0) (h1 : 5≤p1) (hp : Positive xs)
    (hh : pProjection hs=physicalP 4 xs) :
    ∃ a' b' hs',
      sNext b (⟨p0,q0⟩::⟨p1,q1⟩::hs) =
        (a',b',⟨p0-2,q0⟩::⟨p1-4,q1⟩::hs') ∧
      pProjection hs'=physicalP 4 (advance xs) := by
  obtain ⟨a',b',ds,hQ⟩ := nextFarQ b p0 q0 p1 q1 hs h0 h1
  have hP:=secondarySourceP b p0 q0 p1 q1 hs xs h0 h1 hp hh
  rw [hQ] at hP
  simp only [Prod.fst,Prod.snd,pProjection,List.map_cons,List.cons.injEq] at hP
  exact ⟨a',b',ds,hQ,hP.2.2⟩

theorem iterateSourceFar (k a b p0 q0 p1 q1 : Nat) (hs : List PC) (xs : List Nat)
    (h0 : 2*k+3≤p0) (h1 : 4*k+5≤p1) (hp : Positive xs)
    (hh : pProjection hs=physicalP 4 xs) :
    ∃ a' b' hs',
      sIter k (a,b,⟨p0,q0⟩::⟨p1,q1⟩::hs) =
        (a',b',⟨p0-2*k,q0⟩::⟨p1-4*k,q1⟩::hs') ∧
      pProjection hs'=physicalP 4 (lifeIter k xs) := by
  induction k generalizing a b p0 q0 p1 q1 hs xs with
  | zero =>
    refine ⟨a,b,hs,?_,?_⟩
    · simp [sIter]
    · simpa [lifeIter] using hh
  | succ k ih =>
    obtain ⟨a1,b1,hs1,he,hshape⟩ := nextShapeFar b p0 q0 p1 q1 hs xs
      (by omega) (by omega) hp hh
    have hpos := advancePositive xs hp
    obtain ⟨a2,b2,hs2,hr,hend⟩ := ih a1 b1 (p0-2) q0 (p1-4) q1 hs1 (advance xs)
      (by omega) (by omega) hpos hshape
    refine ⟨a2,b2,hs2,?_,?_⟩
    · simp only [sIter]
      rw [he,hr]
      rw [show p0-2-2*k=p0-2*(k+1) by omega,
          show p1-4-4*k=p1-4*(k+1) by omega]
    · simpa [lifeIter] using hend

theorem firstSecondaryFar :
    ∃ a' b' hs',
      sIter 32750 (2047,3071,firstPrimary) =
        (a',b',⟨2818045,131073⟩::⟨6946811,2883586⟩::hs') ∧
      pProjection hs'=physicalP 4 (lifeIter 32750 firstLives) := by
  have h := iterateSourceFar 32750 2047 3071 2883545 131073 7077811 2883586
     firstHead firstLives (by decide) (by decide)
      (by simp [Positive,firstLives]) initialHeadEncoding
  have he : firstPrimary=⟨2883545,131073⟩::⟨7077811,2883586⟩::firstHead := by rfl
  rw [←he] at h
  simpa only [show 2883545-2*32750=2818045 by decide,
              show 7077811-4*32750=6946811 by decide] using h

#print axioms nextFarQ
#print axioms nextShapeFar
#print axioms iterateSourceFar
#print axioms firstSecondaryFar
end F421SecondaryLifetimes
