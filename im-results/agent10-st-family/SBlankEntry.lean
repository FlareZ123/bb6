import STableWitness

namespace BB6.Portfolio

/-- The existing finite-support simulator specializes to either rooted
    table by changing only the transition function. -/
def sFiniteStep (c : FiniteCfg) : Option FiniteCfg :=
  (SRoot c.state (decide (c.head ∈ c.ones))).map fun (w,d,s) =>
    ⟨s,c.head+d.dx,writeOnes c.ones c.head w⟩

def sFiniteRun : Nat → Option FiniteCfg → Option FiniteCfg
  | 0, c => c
  | n+1, c => (sFiniteRun n c).bind sFiniteStep

theorem sEmbedStep (c : FiniteCfg) :
    step SRoot (embed c) = (sFiniteStep c).map embed := by
  cases h : SRoot c.state (decide (c.head ∈ c.ones)) with
  | none => simp [step,embed,sFiniteStep,h]
  | some instr =>
    rcases instr with ⟨w,d,s⟩
    simp only [step,embed,sFiniteStep,h,Option.map_some]
    congr 1
    congr 1
    exact (embed_writeOnes c.ones c.head w).symm

theorem sEmbedRun (n : Nat) (c : Option FiniteCfg) :
    run SRoot n (c.map embed) = (sFiniteRun n c).map embed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run,sFiniteRun,ih]
    cases h : sFiniteRun n c with
    | none => simp
    | some p => simp [sEmbedStep]

/-- Physical support for the published S0p(0,b,c) pattern, with a B-head
    scanning zero: 0^∞ 10(01)^c 01 0^b B>0011 0^∞. -/
def sZeroPositions (b c : Nat) (h : Int) : List Int :=
  ((List.range (c+1)).map (fun j => h - (b+1+2*j : Nat))) ++
   [h - (b+2*c+4 : Nat),h+2,h+3]

def S0pZero (b c : Nat) (h : Int) : Cfg :=
  ⟨(1:State),h,fun i => decide (i ∈ sZeroPositions b c h)⟩

private theorem sFin47 :
    sFiniteRun 47 (some (finBlank (1:State))) =
      some ⟨(1:State),3,[5,6,1,-1,-3,-5,-8]⟩ := by
  set_option maxRecDepth 65536 in
    decide

private theorem sSupport47 :
    embed (⟨(1:State),3,[5,6,1,-1,-3,-5,-8]⟩ : FiniteCfg) =
      S0pZero 1 3 3 := by
  simp only [embed,S0pZero]
  congr 1
  funext i
  simp [sZeroPositions, List.mem_cons]
  tauto

/-- Real infinite-blank physical tape, raw step exact, at the B initial state.
    This is the preimage under STPerm of TRoot's designated blank A. -/
theorem s_blank_B_47_to_S013 :
    run SRoot 47 (some (blank (1:State))) = some (S0pZero 1 3 3) := by
  have hr := sEmbedRun 47 (some (finBlank (1:State)))
  simpa only [Option.map_some,finBlank_embed,sFin47,sSupport47] using hr

theorem t_blank_A_47_to_S013_halts_iff :
    haltsFrom TRoot (0:State) ↔ HaltsCfg SRoot (S0pZero 1 3 3) := by
  exact ST_blank_rooted_halts_iff.trans
    ((haltsFrom_as_cfg SRoot (1:State)).trans
      (haltsCfg_after_prefix SRoot (blank (1:State)) (S0pZero 1 3 3) 47
        s_blank_B_47_to_S013))

theorem t_blank_A_47_to_S013_haltsAt_iff (n : Nat) :
    haltsAt TRoot (0:State) (47+n) ↔
      HaltsAtCfg SRoot (S0pZero 1 3 3) n := by
  exact (ST_blank_rooted_haltsAt_iff (47+n)).trans
    (haltsAt_after_prefix SRoot (blank (1:State))
      (S0pZero 1 3 3) 47 n s_blank_B_47_to_S013)

#print axioms sEmbedStep
#print axioms sEmbedRun
#print axioms s_blank_B_47_to_S013
#print axioms t_blank_A_47_to_S013_halts_iff
#print axioms t_blank_A_47_to_S013_haltsAt_iff

end BB6.Portfolio
