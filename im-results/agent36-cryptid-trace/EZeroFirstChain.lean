import EZeroFirstLocal

namespace BB6.Agent36EZeroFirst
open CryptidBoundary BB6.Agent36EZeroPairs0 BB6.Agent36PositiveFirst
open BB6.Agent36PositiveDoubleZero BB6.CryptidFirstReturn

set_option maxHeartbeats 100000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

private def z0 (m r : Nat) (ys : List Bool) : Cfg := ePairZero m r ys
private def z1 (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨leftCarrier m,false,[true,true,false] ++ (pairs r ++ (false::ys)),0⟩
private def z2 (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,true] ++ leftCarrier m,false,pairs r ++ (false::ys),0⟩
private def z3 (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs r ++ ([false,true,true] ++ leftCarrier m),false,false::ys,0⟩
private def z4 (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨pairs r ++ ([true,true] ++ leftCarrier m),false,[true,true] ++ ys,3⟩
private def z5 (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,true] ++ leftCarrier m,false,
    List.replicate (2*r) true ++ ([true,true] ++ ys),3⟩
private def z6 (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨leftCarrier m,true,
    [true,true] ++ (List.replicate (2*r) true ++ ([true,true] ++ ys)),3⟩
private def z7 (m r : Nat) (ys : List Bool) : Cfg :=
  sweepB m (packetZero ++ (List.replicate (2*r) true ++ ys))

/-- Physical F/0 absence through the full q=0 E 110(10)^r0 transition,
    including the forty-four-step D terminal turn. -/
theorem eZeroBoundaryNoPhysical (m r : Nat) (ys : List Bool) :
    NoPhysical (ePairZero m r ys) (2*m+4*r+63) := by
  let a := z0 m r ys
  let b := z1 m r ys
  let c := z2 m r ys
  let d := z3 m r ys
  let e := z4 m r ys
  let f := z5 m r ys
  let g := z6 m r ys
  let h := z7 m r ys
  have hab : run 4 a = b := by
    dsimp [a,b,z0,z1]
    exact e_four m r ys
  have hbc : run 7 b = c := by
    dsimp [b,c,z1,z2]
    exact a_seven
      (true::(pairs (m+3) ++ [true,true]))
      (pairs r ++ (false::ys))
  have hcd : run (2*r) c = d := by
    dsimp [c,d,z2,z3]
    exact aTenOppIter r ([false,true,true] ++ leftCarrier m) (false::ys)
  have hde : run 3 d = e := by
    dsimp [d,e,z3,z4]
    exact a_three r (leftCarrier m) ys
  have hef : run (2*r) e = f := by
    dsimp [e,f,z4,z5]
    exact d_pair_run r ([true,true] ++ leftCarrier m) ([true,true] ++ ys)
  have hfg : run 2 f = g := by
    dsimp [f,g,z5,z6]
    exact d_two (leftCarrier m)
      (List.replicate (2*r) true ++ ([true,true] ++ ys))
  have hpack :
      [true,true] ++ (List.replicate (2*r) true ++ ([true,true] ++ ys)) =
      [true,true,true,true] ++ (List.replicate (2*r) true ++ ys) := by
    calc
      _ = List.replicate (2*r+4) true ++ ys := fourOnes r ys
      _ = _ := by
        rw [show 2*r+4=4+2*r by omega]
        rw [← List.replicate_append_replicate]
        simp [List.replicate_succ, List.append_assoc]
  have hpackcfg : z6 m r ys =
      (⟨leftCarrier m,true,
        [true,true,true,true] ++ (List.replicate (2*r) true ++ ys),3⟩ : Cfg) :=
    congrArg (fun z : List Bool =>
      (⟨leftCarrier m,true,z,3⟩ : Cfg)) hpack
  have hgh : run 44 g = h := by
    change run 44 (z6 m r ys) = z7 m r ys
    rw [hpackcfg]
    exact d_tail44 m (List.replicate (2*r) true ++ ys)
  have ha : NoPhysical a 4 := eFourNoPhysical m r ys
  have hb : NoPhysical b 7 :=
    aSevenNoPhysical
      (true::(pairs (m+3) ++ [true,true]))
      (pairs r ++ (false::ys))
  have hc : NoPhysical c (2*r) :=
    aTenNoPhysical r ([false,true,true] ++ leftCarrier m) (false::ys)
  have hd : NoPhysical d 3 :=
    aThreeNoPhysical r (leftCarrier m) ys
  have he : NoPhysical e (2*r) :=
    dPairsNoPhysical r ([true,true] ++ leftCarrier m) ([true,true] ++ ys)
  have hf : NoPhysical f 2 :=
    dTwoNoPhysical (leftCarrier m)
      (List.replicate (2*r) true ++ ([true,true] ++ ys))
  have hg : NoPhysical g 44 := by
    change NoPhysical (z6 m r ys) 44
    rw [hpackcfg]
    exact dTailNoPhysical m (List.replicate (2*r) true ++ ys)
  have hh : NoPhysical h (2*m+3) := by
    apply noF_noPhysical h (2*m+3)
    intro t ht
    exact sweepB_firstF m
      (packetZero ++ (List.replicate (2*r) true ++ ys)) t ht
  have h6 : NoPhysical g (44+(2*m+3)) :=
    join g h 44 (2*m+3) hg hgh hh
  have h5 : NoPhysical f (2+(44+(2*m+3))) :=
    join f g 2 (44+(2*m+3)) hf hfg h6
  have h4 : NoPhysical e (2*r+(2+(44+(2*m+3)))) :=
    join e f (2*r) (2+(44+(2*m+3))) he hef h5
  have h3 : NoPhysical d (3+(2*r+(2+(44+(2*m+3))))) :=
    join d e 3 (2*r+(2+(44+(2*m+3)))) hd hde h4
  have h2 : NoPhysical c (2*r+(3+(2*r+(2+(44+(2*m+3)))))) :=
    join c d (2*r) (3+(2*r+(2+(44+(2*m+3))))) hc hcd h3
  have h1 : NoPhysical b (7+(2*r+(3+(2*r+(2+(44+(2*m+3))))))) :=
    join b c 7 (2*r+(3+(2*r+(2+(44+(2*m+3)))))) hb hbc h2
  have h0 : NoPhysical a (4+(7+(2*r+(3+(2*r+(2+(44+(2*m+3)))))))) :=
    join a b 4 (7+(2*r+(3+(2*r+(2+(44+(2*m+3))))))) ha hab h1
  have htime :
      4+(7+(2*r+(3+(2*r+(2+(44+(2*m+3))))))) =
        2*m+4*r+63 := by omega
  change NoPhysical a (2*m+4*r+63)
  rwa [htime] at h0

#print axioms eZeroBoundaryNoPhysical
end BB6.Agent36EZeroFirst
