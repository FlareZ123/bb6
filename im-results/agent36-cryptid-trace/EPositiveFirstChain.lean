import EPositiveFirstFour

namespace BB6.Agent36PositiveFirst
open CryptidBoundary BB6.Agent36PositiveDoubleZero BB6.Agent36EZeroPairs0 BB6.CryptidFirstReturn

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

private def s0 (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs (q+2) ++ core m,false,
    [true,true,false] ++ (pairs r ++ (false::ys)),0⟩
private def s1 (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,true] ++ (oppairs (q+2) ++ core m),false,
    pairs r ++ (false::ys),0⟩
private def s2 (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs r ++ ([false,true,true] ++ (oppairs (q+2) ++ core m)),
    false,false::ys,0⟩
private def s3 (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨pairs r ++ ([true,true] ++ (oppairs (q+2) ++ core m)),
    false,[true,true] ++ ys,3⟩
private def s4 (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,true] ++ (oppairs (q+2) ++ core m),false,
    List.replicate (2*r) true ++ ([true,true] ++ ys),3⟩
private def s5 (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs (q+2) ++ core m,true,
    [true,true] ++ (List.replicate (2*r) true ++
      ([true,true] ++ ys)),3⟩
private def s6 (m q r : Nat) (ys : List Bool) : Cfg :=
  cWalk q (core m)
    ([true,false,true,true] ++
      (List.replicate (2*r+4) true ++ ys))
private def s7 (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨core m,true,List.replicate (2*q) true ++
    ([true,false,true,true] ++ (List.replicate (2*r+4) true ++ ys)),2⟩
private def s8 (m q r : Nat) (ys : List Bool) : Cfg :=
  sweepB m ([false,true,true,true] ++
    (List.replicate (2*q) true ++
    ([true,false,true,true] ++
    (List.replicate (2*r+4) true ++ ys))))

/-- Nine individually source-connected physical non-return phases,
    including the two transient F-state visits with a nonblank left tape. -/
theorem aPositiveFirst (m q r : Nat) (ys : List Bool) :
    NoPhysical (s0 m q r ys) (20+2*q+4*r+(2*m+3)) := by
  let a := s0 m q r ys
  let b := s1 m q r ys
  let c := s2 m q r ys
  let d := s3 m q r ys
  let e := s4 m q r ys
  let f := s5 m q r ys
  let g := s6 m q r ys
  let h := s7 m q r ys
  let i := s8 m q r ys
  have hab : run 7 a = b := by
    dsimp [a,b,s0,s1]
    exact aDoubleSeven (q+1) (core m) (pairs r ++ (false::ys))
  have hbc : run (2*r) b = c := by
    dsimp [b,c,s1,s2]
    rw [aTenOppIter]
  have hcd : run 3 c = d := by
    dsimp [c,d,s2,s3]
    exact a_three r (oppairs (q+2) ++ core m) ys
  have hde : run (2*r) d = e := by
    dsimp [d,e,s3,s4]
    rw [d_pair_run]
  have hef : run 2 e = f := by
    dsimp [e,f,s4,s5]
    exact d_two (oppairs (q+2) ++ core m)
      (List.replicate (2*r) true ++ ([true,true] ++ ys))
  have hfg : run 4 f = g := by
    change run 4 (s5 m q r ys) = s6 m q r ys
    have hp : s5 m q r ys =
        (⟨oppairs (q+2) ++ core m,true,
          List.replicate (2*r+4) true ++ ys,3⟩ : Cfg) := by
      simp [s5, fourOnes]
    rw [hp]
    exact dBridge q (core m) (List.replicate (2*r+4) true ++ ys)
  have hgh : run (2*q) g = h := by
    dsimp [g,h,s6,s7]
    rw [cWalk_run]
  have hhi : run 4 h = i := by
    change run 4 (s7 m q r ys) = s8 m q r ys
    exact cBase m
      (List.replicate (2*q) true ++
        ([true,false,true,true] ++ (List.replicate (2*r+4) true ++ ys)))
  have ha : NoPhysical a 7 :=
    aSevenNoPhysical (oppairs (q+2) ++ core m)
      (pairs r ++ (false::ys))
  have hb : NoPhysical b (2*r) :=
    aTenNoPhysical r
      ([false,true,true] ++ (oppairs (q+2) ++ core m)) (false::ys)
  have hc : NoPhysical c 3 :=
    aThreeNoPhysical r (oppairs (q+2) ++ core m) ys
  have hd : NoPhysical d (2*r) :=
    dPairsNoPhysical r ([true,true] ++ (oppairs (q+2) ++ core m))
      ([true,true] ++ ys)
  have he : NoPhysical e 2 :=
    dTwoNoPhysical (oppairs (q+2) ++ core m)
      (List.replicate (2*r) true ++ ([true,true] ++ ys))
  have hf : NoPhysical f 4 := dBridgeNoPhysical m q r ys
  have hg : NoPhysical g (2*q) :=
    walkNoPhysical q (core m)
      ([true,false,true,true] ++ (List.replicate (2*r+4) true ++ ys))
  have hh : NoPhysical h 4 := cBaseNoPhysical m q r ys
  have hi : NoPhysical i (2*m+3) := by
    apply noF_noPhysical i (2*m+3)
    intro t ht
    exact sweepB_firstF m
      ([false,true,true,true] ++
        (List.replicate (2*q) true ++
          ([true,false,true,true] ++
            (List.replicate (2*r+4) true ++ ys)))) t ht
  have h7 : NoPhysical h (4+(2*m+3)) :=
    join h i 4 (2*m+3) hh hhi hi
  have h6 : NoPhysical g (2*q+(4+(2*m+3))) :=
    join g h (2*q) (4+(2*m+3)) hg hgh h7
  have h5 : NoPhysical f (4+(2*q+(4+(2*m+3)))) :=
    join f g 4 (2*q+(4+(2*m+3))) hf hfg h6
  have h4 : NoPhysical e (2+(4+(2*q+(4+(2*m+3))))) :=
    join e f 2 (4+(2*q+(4+(2*m+3)))) he hef h5
  have h3 : NoPhysical d (2*r+(2+(4+(2*q+(4+(2*m+3)))))) :=
    join d e (2*r) (2+(4+(2*q+(4+(2*m+3))))) hd hde h4
  have h2 : NoPhysical c (3+(2*r+(2+(4+(2*q+(4+(2*m+3))))))) :=
    join c d 3 (2*r+(2+(4+(2*q+(4+(2*m+3)))))) hc hcd h3
  have h1 : NoPhysical b
      (2*r+(3+(2*r+(2+(4+(2*q+(4+(2*m+3)))))))) :=
    join b c (2*r) (3+(2*r+(2+(4+(2*q+(4+(2*m+3))))))) hb hbc h2
  have h0 : NoPhysical a
      (7+(2*r+(3+(2*r+(2+(4+(2*q+(4+(2*m+3))))))))) :=
    join a b 7 (2*r+(3+(2*r+(2+(4+(2*q+(4+(2*m+3)))))))) ha hab h1
  have htime :
      7+(2*r+(3+(2*r+(2+(4+(2*q+(4+(2*m+3)))))))) =
        20+2*q+4*r+(2*m+3) := by omega
  change NoPhysical a (20+2*q+4*r+(2*m+3))
  rwa [htime] at h0

#print axioms aPositiveFirst
end BB6.Agent36PositiveFirst
