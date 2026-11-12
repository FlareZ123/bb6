import Root119B0ParentCone
import Root119OddWaveRetreat

namespace BB6Root119

set_option maxHeartbeats 1000000

/-- Convert an exact source-transition path into the repository's run
    semantics. This keeps the physical path and macro semantics aligned. -/
theorem parentCone_path_run {n : Nat} {c d : Conf}
    (hp : Root119Path n c d) : run n c = some d := by
  induction hp with
  | refl c => rfl
  | @step n c u d hs ht ih =>
      simp [run, hs, ih]

/-- Every genuinely reached B/0 with left suffix 10 is exactly the output
    of one of two source-proved F/1 return macros.

    The short case is the five-step n=0 odd wave. In the long case, the
    tight ancestry corridor supplies the n=0, m-parameter hypotheses of
    odd_f1_retreat_to_b0. The theorem identifies the complete output
    configuration, not just its state and head. -/
theorem reached_B0_left10_exact_wave_output (c : Conf) (hc : Reach c)
    (hB : c.q = .B) (hcurrent : c.tape c.h = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hleft2 : c.tape (c.h-2) = false) :
    (∃ f, Reach f ∧ f.q = .F ∧ f.tape f.h = true ∧
      f.h = c.h+1 ∧
      c = (⟨.B,f.h-1,oddWaveTape 0 f.tape f.h⟩ : Conf)) ∨
    (∃ m f, Reach f ∧ f.q = .F ∧ f.tape f.h = true ∧
      f.h = c.h+2*(m:Int)+3 ∧
      c = (⟨.B,f.h-3-2*(m:Int),
        setBit (fbMany m
          (⟨.F,f.h-2,
            setBit (oddWaveTape 0 f.tape f.h) (f.h-1) true⟩ : Conf)).tape
          (f.h-2-2*(m:Int)) true⟩ : Conf)) := by
  obtain ⟨k,f,d,e,g,hk,hf,hF,hFbit,hposF,
    hd,hD,hDbit,hposD,hstepF,
    he,hE,hEzero,hposE,hstepD,
    hg,hG,hGzero,hGpos,hpath,hGstep⟩ :=
      reached_B0_left10_path_components c hc hB hcurrent hleft3 hleft2

  have hpathGC : Root119Path 1 g c :=
    Root119Path.step hGstep (Root119Path.refl c)
  have hpathEC : Root119Path (2*k+1) e c := by
    have h := root119Path_comp hpath hpathGC
    simpa using h
  have hpathFD : Root119Path 2 f e :=
    Root119Path.step hstepF
      (Root119Path.step hstepD (Root119Path.refl e))
  have hpathFC : Root119Path (2*k+3) f c := by
    have h := root119Path_comp hpathFD hpathEC
    have hlen : 2+(2*k+1)=2*k+3 := by omega
    simpa [hlen] using h

  have hrunFC : run (2*k+3) f = some c :=
    parentCone_path_run hpathFC
  have hfConfig : f = (⟨.F,f.h,f.tape⟩ : Conf) := by
    cases f with
    | mk q h t => simp_all
  have hrunInput : run (2*k+3) (⟨.F,f.h,f.tape⟩ : Conf) = some c := by
    simpa [hfConfig] using hrunFC

  have hdispEC : c.h = e.h-((2*k+1:Nat):Int) := by
    rw [hposE,hposF]
    omega
  have hdispEG : g.h = e.h-(2*k:Int) := by
    rw [hposE,hposF,hGpos]
    omega
  have hpattern := parentCone_f0_b0_corridor k e c
    hE hEzero hB hcurrent hpathEC hdispEC

  have hEF (x : Int) (hxf : x≠f.h) (hxd : x≠d.h) :
      e.tape x=f.tape x := by
    calc
      e.tape x = d.tape x :=
        parentCone_next_tape_away d e hstepD x hxd
      _ = f.tape x :=
        parentCone_next_tape_away f d hstepF x hxf

  have hDread : d.tape (f.h+1)=true := by
    simpa [hposD] using hDbit
  have hDaway := parentCone_next_tape_away f d hstepF
    (f.h+1) (by omega)
  have hones1 : f.tape (f.h+1)=true := hDaway.symm.trans hDread

  have heRead : e.tape (f.h+2)=false := by
    simpa [hposE] using hEzero
  have heAway := hEF (f.h+2) (by omega) (by omega)
  have hzero2 : f.tape (f.h+2)=false := heAway.symm.trans heRead

  have hones : ∀ j : Nat, j<1 →
      f.tape (f.h+1+(j:Int))=true := by
    intro j hj
    have hj0 : j=0 := by omega
    subst j
    simpa using hones1

  by_cases hk1 : k=1
  · have hrunInputShort : run 5 (⟨.F,f.h,f.tape⟩ : Conf) = some c := by
      simpa [hk1] using hrunInput
    have hret := odd_f1_to_b 0 f.tape f.h hFbit hones hzero2
    have hhead : f.h-1=c.h := by rw [hposF]; omega
    have hret' :
        run 5 (⟨.F,f.h,f.tape⟩ : Conf) =
          some (⟨.B,c.h,oddWaveTape 0 f.tape f.h⟩ : Conf) := by
      simpa [hhead] using hret
    have hout :
        (⟨.B,c.h,oddWaveTape 0 f.tape f.h⟩ : Conf)=c :=
      Option.some.inj (hret'.symm.trans hrunInputShort)
    exact Or.inl ⟨f,hf,hF,hFbit,by rw [hposF]; omega,hout.symm⟩
  · have hk2 : 2≤k := by omega
    have hleftE : e.tape (f.h-1)=true := by
      have hpatt := hpattern 1 (by omega)
      have hidxLeft : e.h-3=f.h-1 := by
        rw [hposE]
        omega
      rw [← hidxLeft]
      simpa using hpatt.2
    have heLeft := hEF (f.h-1) (by omega) (by omega)
    have hleft : f.tape (f.h-1)=true := heLeft.symm.trans hleftE

    have hfb : ∀ i : Nat, i<k-2 →
        f.tape (f.h-2-2*(i:Int))=false ∧
        f.tape (f.h-3-2*(i:Int))=true := by
      intro i hi
      have hpatt := hpattern (i+2) (by omega)
      have hidx1 : e.h-2*((i+2:Int))=f.h-2-2*(i:Int) := by
        rw [hposE]
        omega
      have hidx2 : e.h-2*((i+2:Int))-1=f.h-3-2*(i:Int) := by
        rw [hposE]
        omega
      have he1 : e.tape (f.h-2-2*(i:Int))=false := by
        rw [← hidx1]
        exact hpatt.1
      have he2 : e.tape (f.h-3-2*(i:Int))=true := by
        rw [← hidx2]
        exact hpatt.2
      have heq1 := hEF (f.h-2-2*(i:Int)) (by omega) (by omega)
      have heq2 := hEF (f.h-3-2*(i:Int)) (by omega) (by omega)
      exact ⟨heq1.symm.trans he1,heq2.symm.trans he2⟩

    have hpresG :=
      parentCone_path_tight_preserves_tape hpath hdispEG g.h (by omega)
    have heG : e.tape g.h=false := hpresG.symm.trans hGzero
    have hidxF : f.h-2*(k:Int)+2=g.h := by
      rw [hposF,hGpos]
      omega
    have heqG := hEF g.h
      (by rw [hidxF.symm]; omega)
      (by rw [hposD,hidxF.symm]; omega)
    have hfinalF : f.tape (f.h-2*(k:Int)+2)=false := by
      simpa [hidxF] using heqG.symm.trans heG

    have hpresC :=
      parentCone_path_tight_preserves_tape hpathEC hdispEC c.h (by omega)
    have heC : e.tape c.h=false := hpresC.symm.trans hcurrent
    have hidxB : f.h-2*(k:Int)+1=c.h := by
      rw [hposF]
      omega
    have heqC := hEF c.h
      (by rw [hidxB.symm]; omega)
      (by rw [hposD,hidxB.symm]; omega)
    have hfinalB : f.tape (f.h-2*(k:Int)+1)=false := by
      simpa [hidxB] using heqC.symm.trans heC

    let m : Nat := k-2
    have hmk : k=m+2 := by dsimp [m]; omega
    have hfbM : ∀ i : Nat, i<m →
        f.tape (f.h-2-2*(i:Int))=false ∧
        f.tape (f.h-3-2*(i:Int))=true := by
      intro i hi
      exact hfb i (by simpa [m] using hi)
    have hfinalFM :
        f.tape (f.h-2-2*(m:Int))=false := by
      have hidx : f.h-2-2*(m:Int)=f.h-2*(k:Int)+2 := by
        dsimp [m]
        omega
      simpa [hidx] using hfinalF
    have hfinalBM :
        f.tape (f.h-3-2*(m:Int))=false := by
      have hidx : f.h-3-2*(m:Int)=f.h-2*(k:Int)+1 := by
        dsimp [m]
        omega
      simpa [hidx] using hfinalB

    have hret := odd_f1_retreat_to_b0 0 m f.tape f.h
      hFbit hones hzero2 hleft hfbM hfinalFM hfinalBM
    have hhead : f.h-3-2*(m:Int)=c.h := by
      rw [hposF]
      dsimp [m]
      omega
    have hlen : 4*0+2*m+7=2*k+3 := by
      dsimp [m]
      omega
    have hret' :
        run (2*k+3) (⟨.F,f.h,f.tape⟩ : Conf) =
          some (⟨.B,c.h,
            setBit (fbMany m
              (⟨.F,f.h-2,
                setBit (oddWaveTape 0 f.tape f.h) (f.h-1) true⟩ : Conf)).tape
              (f.h-2-2*(m:Int)) true⟩ : Conf) := by
      simpa [hlen,hhead] using hret.1
    have hout :
        (⟨.B,c.h,
          setBit (fbMany m
            (⟨.F,f.h-2,
              setBit (oddWaveTape 0 f.tape f.h) (f.h-1) true⟩ : Conf)).tape
            (f.h-2-2*(m:Int)) true⟩ : Conf)=c :=
      Option.some.inj (hret'.symm.trans hrunInput)
    have hheight : f.h=c.h+2*(m:Int)+3 := by
      rw [hposF]
      dsimp [m]
      omega
    refine Or.inr ⟨m,f,hf,hF,hFbit,hheight,?_⟩
    simpa [hhead] using hout.symm

#print axioms parentCone_path_run
#print axioms reached_B0_left10_exact_wave_output

end BB6Root119
