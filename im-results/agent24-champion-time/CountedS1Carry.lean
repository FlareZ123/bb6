import ChampionRootBridge
import S1Encoder
import TerminalCount
import UniformTM63

open BB6.ChampionTerminal
open BB6Coverage.Agent8S1Encoder

namespace BB6Coverage.Agent24CountedS1Carry

/-- State-number translation from the uniform zipper transcription to
Agent 8's partial TM63 zipper. -/
def natToQ : Nat → BB6.ChampionTerminal.Q
  | 0 => .A
  | 1 => .B
  | 2 => .C
  | 3 => .D
  | 4 => .E
  | 5 => .F
  | _ => .A

def cfgToZ (c : TM63Uniform.Cfg) : BB6.ChampionTerminal.Z :=
  ⟨natToQ c.st, c.l, c.h, c.r⟩

/-- The uniform totalized zipper never leaves the six machine states when
started in the source D state. -/
theorem step_state_lt_six (c : TM63Uniform.Cfg) (hc : c.st < 6) :
    (TM63Uniform.step c).st < 6 := by
  cases c with
  | mk st l b r =>
    have hs : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 := by omega
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 <;>
      subst st <;> cases b <;>
      simp [TM63Uniform.step, TM63Uniform.moveR, TM63Uniform.moveL] <;> omega

/-- One step of the totalized Agent 26 zipper is the partial Agent 8
zipper step whenever the original machine has not reached its sole
undefined transition A/1. -/
theorem cfgStep_toZ (c : TM63Uniform.Cfg) (hc : c.st < 6)
    (hsafe : ¬ (c.st = 0 ∧ c.h = true)) :
    BB6.ChampionTerminal.step (cfgToZ c) =
      some (cfgToZ (TM63Uniform.step c)) := by
  cases c with
  | mk st l b r =>
    have hs : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 := by omega
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 <;>
      subst st <;> cases b <;>
      simp [cfgToZ, natToQ, TM63Uniform.step, TM63Uniform.moveR,
        TM63Uniform.moveL, BB6.ChampionTerminal.step,
        BB6.ChampionTerminal.moveR, BB6.ChampionTerminal.moveL] at hsafe ⊢

/-- Transport every safe finite prefix of the totalized zipper run to
Agent 8's partial zipper run. -/
theorem cfgRun_toZ (n : Nat) (c : TM63Uniform.Cfg) (hc : c.st < 6)
    (hsafe : ∀ t, t ≤ n →
      ¬ ((TM63Uniform.run t c).st = 0 ∧ (TM63Uniform.run t c).h = true)) :
    BB6.ChampionTerminal.run n (cfgToZ c) =
      some (cfgToZ (TM63Uniform.run n c)) := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hsafe0 := hsafe 0 (by omega)
      have hstep := cfgStep_toZ c hc hsafe0
      have hc' : (TM63Uniform.step c).st < 6 := step_state_lt_six c hc
      have hsafe' : ∀ t, t ≤ n →
          ¬ ((TM63Uniform.run t (TM63Uniform.step c)).st = 0 ∧
             (TM63Uniform.run t (TM63Uniform.step c)).h = true) := by
        intro t ht
        have hrel : TM63Uniform.run t (TM63Uniform.step c) =
            TM63Uniform.run (t+1) c := rfl
        rw [hrel]
        exact hsafe (t+1) (by omega)
      calc
        BB6.ChampionTerminal.run (n+1) (cfgToZ c) =
            BB6.ChampionTerminal.run (1+n) (cfgToZ c) := by omega
        _ = (BB6.ChampionTerminal.run 1 (cfgToZ c)).bind
              (BB6.ChampionTerminal.run n) := by
            rw [BB6.ChampionTerminal.run_add]
        _ = (some (cfgToZ (TM63Uniform.step c))).bind
              (BB6.ChampionTerminal.run n) := by
            simp [BB6.ChampionTerminal.run, hstep]
        _ = BB6.ChampionTerminal.run n (cfgToZ (TM63Uniform.step c)) := by simp
        _ = some (cfgToZ (TM63Uniform.run n (TM63Uniform.step c))) :=
            ih (TM63Uniform.step c) hc' hsafe'
        _ = some (cfgToZ (TM63Uniform.run (n+1) c)) := by rfl

/-- Agent 26's exact counted macro, now interpreted in Agent 8's
halting zipper semantics. -/
theorem countedZRun (k c : Nat) (ls rs : List Bool) :
    BB6.ChampionTerminal.run (48+12*k+12*c)
      (cfgToZ (TM63Uniform.rawStart k c ls rs)) =
    some (cfgToZ (TM63Uniform.rawEnd k c ls rs)) := by
  have hc : (TM63Uniform.rawStart k c ls rs).st < 6 := by
    simp [TM63Uniform.rawStart, TM63Uniform.dBoundary]
  have hsafe : ∀ t, t ≤ 48+12*k+12*c →
      ¬ ((TM63Uniform.run t (TM63Uniform.rawStart k c ls rs)).st = 0 ∧
         (TM63Uniform.run t (TM63Uniform.rawStart k c ls rs)).h = true) := by
    intro t ht
    exact TM63Uniform.counted_no_early_halt k c ls rs t ht
  have hrun := cfgRun_toZ (48+12*k+12*c)
    (TM63Uniform.rawStart k c ls rs) hc hsafe
  rw [TM63Uniform.counted_all] at hrun
  exact hrun

/-- The first component of a located run is the ordinary zipper run.
This is re-proved here because Agent 8 keeps its corresponding lemma private. -/
theorem locatedStep_fst (zp : BB6.ChampionTerminal.Z × Int) :
    (BB6.ChampionTerminal.locatedStep zp).map Prod.fst =
      BB6.ChampionTerminal.step zp.1 := by
  unfold BB6.ChampionTerminal.locatedStep
  cases h : BB6.ChampionTerminal.step zp.1 <;> simp [h]

theorem locatedRun_fst (n : Nat) (z : BB6.ChampionTerminal.Z) (p : Int) :
    (BB6.ChampionTerminal.locatedRun n (z,p)).map Prod.fst =
      BB6.ChampionTerminal.run n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [BB6.ChampionTerminal.locatedRun, BB6.ChampionTerminal.run]
      rw [← ih]
      cases h : BB6.ChampionTerminal.locatedRun n (z,p) with
      | none => simp [h]
      | some w =>
          simp only [h, Option.bind_some, Option.map_some]
          exact locatedStep_fst w

theorem locatedRun_exists (n : Nat) (z zEnd : BB6.ChampionTerminal.Z)
    (p : Int) (hz : BB6.ChampionTerminal.run n z = some zEnd) :
    ∃ p', BB6.ChampionTerminal.locatedRun n (z,p) = some (zEnd,p') := by
  have hf := locatedRun_fst n z p
  rw [hz] at hf
  cases hloc : BB6.ChampionTerminal.locatedRun n (z,p) with
  | none => simp [hloc] at hf
  | some w =>
      rcases w with ⟨z',p'⟩
      have hz' : z' = zEnd := by simpa [hloc] using hf
      subst z'
      exact ⟨p', by simpa [hloc]⟩

/-- State translation from Agent 8's six constructors to the original
BB6Coverage.Config state type. -/
def qToFin : BB6.ChampionTerminal.Q → Fin 6
  | .A => 0
  | .B => 1
  | .C => 2
  | .D => 3
  | .E => 4
  | .F => 5

def fullToConfig (f : BB6.ChampionTerminal.Full) : BB6Coverage.Config :=
  ⟨qToFin f.state, f.head, f.tape⟩

/-- The absolute-head full-tape table is exactly the original
BB6Coverage Agent 48 champion machine. -/
theorem fullStep_toConfig (f : BB6.ChampionTerminal.Full) :
    (BB6.ChampionTerminal.fullStep f).map fullToConfig =
      BB6Coverage.rawStep BB6Coverage.Agent48Champion.tm2 (fullToConfig f) := by
  cases f with
  | mk q h t =>
      cases q <;> cases hb : t h <;>
        simp [BB6.ChampionTerminal.fullStep, BB6.ChampionTerminal.fullR,
          BB6.ChampionTerminal.fullL, fullToConfig, qToFin,
          BB6Coverage.rawStep, BB6Coverage.applyMove,
          BB6Coverage.Agent48Champion.tm2, hb]

theorem fullRun_toConfig (n : Nat) (f : BB6.ChampionTerminal.Full) :
    (BB6.ChampionTerminal.fullRun n f).map fullToConfig =
      BB6Coverage.run BB6Coverage.Agent48Champion.tm2 n (fullToConfig f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [BB6.ChampionTerminal.fullRun, BB6Coverage.run]
      cases h : BB6.ChampionTerminal.fullRun n f with
      | none =>
          have hrun : BB6Coverage.run BB6Coverage.Agent48Champion.tm2 n
              (fullToConfig f) = none := by
            simpa [h] using ih
          simp [h, hrun]
      | some g =>
          have hrun : BB6Coverage.run BB6Coverage.Agent48Champion.tm2 n
              (fullToConfig f) = some (fullToConfig g) := by
            simpa [h] using ih.symm
          rw [h, hrun]
          simp [fullStep_toConfig]

/-- Constructor injectivity gives the fieldwise extensionality needed for
the two full-tape encodings. -/
theorem config_ext {c d : BB6Coverage.Config}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) :
    c = d := by
  cases c with
  | mk cs ch ct =>
      cases d with
      | mk ds dh dt =>
          simp_all

theorem sideBit_eq (xs : List Bool) (i : Nat) :
    BB6.ChampionTerminal.sideBit xs i =
      BB6Coverage.Agent8S1Encoder.sideBit xs i := by
  induction xs generalizing i with
  | nil =>
      simp [BB6.ChampionTerminal.sideBit, BB6Coverage.Agent8S1Encoder.sideBit]
  | cons b xs ih =>
      cases i <;>
        simp [BB6.ChampionTerminal.sideBit, BB6Coverage.Agent8S1Encoder.sideBit, ih]

theorem sideBit_append_false (xs : List Bool) (i : Nat) :
    BB6.ChampionTerminal.sideBit (xs ++ [false,false,false]) i =
      BB6.ChampionTerminal.sideBit xs i := by
  induction xs generalizing i with
  | nil =>
      cases i with
      | zero => rfl
      | succ i =>
          cases i with
          | zero => rfl
          | succ i =>
              cases i with
              | zero => rfl
              | succ i => simp [BB6.ChampionTerminal.sideBit]
  | cons b xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

theorem embedFull_left_cell (z : BB6.ChampionTerminal.Z) (h : Int) (i : Nat) :
    (BB6.ChampionTerminal.embedFull z h).tape (h-(i:Int)) =
      BB6.ChampionTerminal.sideBit (z.cur :: z.left) i := by
  cases i with
  | zero =>
      simp [BB6.ChampionTerminal.embedFull, BB6.ChampionTerminal.relativeTape,
        BB6.ChampionTerminal.sideBit]
  | succ i =>
      have hd : h-((i+1:Int))-h = Int.negSucc i := by omega
      simp [BB6.ChampionTerminal.embedFull, BB6.ChampionTerminal.relativeTape,
        BB6.ChampionTerminal.sideBit, hd]

theorem embedFull_right_cell (z : BB6.ChampionTerminal.Z) (h : Int) (i : Nat) :
    (BB6.ChampionTerminal.embedFull z h).tape (h+1+(i:Int)) =
      BB6.ChampionTerminal.sideBit z.right i := by
  have hd : h+1+(i:Int)-h = (i:Int)+1 := by omega
  simp [BB6.ChampionTerminal.embedFull, BB6.ChampionTerminal.relativeTape,
    BB6.ChampionTerminal.sideBit, hd]

/-- Compare Agent 8's absolute full-tape embedding with the actual
source S1 configuration, using the head-facing and right-facing cell laws. -/
theorem fullToConfig_embed_s1 (z : BB6.ChampionTerminal.Z) (h : Int)
    (L n m a v b : Nat)
    (hstate : z.state = .D)
    (hleft : z.cur :: z.left =
      BB6Coverage.Agent8S1Encoder.s1LeftFacing L n m a v)
    (hright : ∀ i,
      BB6.ChampionTerminal.sideBit z.right i =
        BB6Coverage.Agent8S1Encoder.sideBit
          (BB6Coverage.Agent8S1Encoder.s1PhysicalRight b) i) :
    fullToConfig (BB6.ChampionTerminal.embedFull z h) =
      BB6Coverage.Agent8S1Encoder.s1Config L n m a v b h := by
  apply config_ext
  · simp [fullToConfig, qToFin, hstate]
  · rfl
  · funext x
    by_cases hle : x ≤ h
    · let i : Nat := (h-x).toNat
      have hi : (i:Int) = h-x := Int.toNat_of_nonneg (by omega)
      have hx : x = h-(i:Int) := by omega
      rw [hx, embedFull_left_cell,
        BB6Coverage.Agent8S1Encoder.s1Config_left_cell]
      rw [sideBit_eq, hleft]
    · let i : Nat := (x-h-1).toNat
      have hi : (i:Int) = x-h-1 := Int.toNat_of_nonneg (by omega)
      have hx : x = h+1+(i:Int) := by omega
      rw [hx, embedFull_right_cell,
        BB6Coverage.Agent8S1Encoder.s1Config_right_cell]
      exact hright i

theorem d1pow_eq_ones (r : Nat) :
    BB6Coverage.Agent8S1Encoder.d1pow r = TM63Uniform.ones (3*r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [BB6Coverage.Agent8S1Encoder.d1pow,
        BB6Coverage.Agent8S1Encoder.d1, TM63Uniform.ones, ih, Nat.mul_succ]

theorem tri_eq_d0pow (r : Nat) :
    TM63Uniform.tri r = BB6Coverage.Agent8S1Encoder.d0pow r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [TM63Uniform.tri, BB6Coverage.Agent8S1Encoder.d0pow,
        BB6Coverage.Agent8S1Encoder.d0, ih]

theorem rawStart_left_stream (r b : Nat) (ls : List Bool) :
    (cfgToZ (TM63Uniform.rawStart r b ls [])).cur ::
      (cfgToZ (TM63Uniform.rawStart r b ls [])).left =
    BB6Coverage.Agent8S1Encoder.d1pow r ++
      BB6Coverage.Agent8S1Encoder.d0 ++ ls := by
  cases r with
  | zero =>
      simp [cfgToZ, natToQ, TM63Uniform.rawStart,
        TM63Uniform.dBoundary, BB6Coverage.Agent8S1Encoder.d0,
        BB6Coverage.Agent8S1Encoder.d1pow]
  | succ r =>
      simp [cfgToZ, natToQ, TM63Uniform.rawStart,
        d1pow_eq_ones, TM63Uniform.ones,
        BB6Coverage.Agent8S1Encoder.d1,
        BB6Coverage.Agent8S1Encoder.d0, Nat.mul_succ,
        List.append_assoc]

theorem rawEnd_left_stream (r b : Nat) (ls : List Bool) :
    (cfgToZ (TM63Uniform.rawEnd r b ls [])).cur ::
      (cfgToZ (TM63Uniform.rawEnd r b ls [])).left =
    BB6Coverage.Agent8S1Encoder.d0pow r ++
      BB6Coverage.Agent8S1Encoder.d1 ++ ls := by
  cases r with
  | zero =>
      simp [cfgToZ, natToQ, TM63Uniform.rawEnd,
        TM63Uniform.dBoundaryZero, BB6Coverage.Agent8S1Encoder.d1,
        BB6Coverage.Agent8S1Encoder.d0pow]
  | succ r =>
      simp [cfgToZ, natToQ, TM63Uniform.rawEnd,
        TM63Uniform.tri, tri_eq_d0pow,
        BB6Coverage.Agent8S1Encoder.d0pow,
        BB6Coverage.Agent8S1Encoder.d0,
        BB6Coverage.Agent8S1Encoder.d1, List.append_assoc]

theorem rawStart_right_list (r b : Nat) (ls : List Bool) :
    (cfgToZ (TM63Uniform.rawStart r b ls [])).right =
      [false,true,true,true,false,false] ++
        BB6Coverage.Agent8S1Encoder.d1pow (b+1) ++
        [false,false,false] := by
  cases r <;>
    simp [cfgToZ, TM63Uniform.rawStart, TM63Uniform.dBoundary,
      TM63Uniform.dTail, TM63Uniform.ones, d1pow_eq_ones,
      BB6Coverage.Agent8S1Encoder.d1]

theorem rawEnd_right_list (r b : Nat) (ls : List Bool) :
    (cfgToZ (TM63Uniform.rawEnd r b ls [])).right =
      [false,true,true,true,false,false] ++
        BB6Coverage.Agent8S1Encoder.d1pow (b+2) := by
  cases r <;>
    simp [cfgToZ, TM63Uniform.rawEnd, TM63Uniform.dBoundaryZero,
      TM63Uniform.scoredRight, TM63Uniform.ones, d1pow_eq_ones,
      BB6Coverage.Agent8S1Encoder.d1]

/-- The original TM63 machine executes the complete source S1 decrement
microstep for every odd-part factorization. The head position is allowed
to be existential because the located simulation tracks it exactly. -/
theorem s1_inc0_counted_of_factorization
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len) :
    ∃ h',
      BB6Coverage.run BB6Coverage.Agent48Champion.tm2 (48+12*r+12*b)
        (BB6Coverage.Agent8S1Encoder.s1Config L n m (len+1+r)
          ((2*q+1)*2^r) b h) =
      some (BB6Coverage.Agent8S1Encoder.s1Config L n m (len+1+r)
        (((2*q+1)*2^r)-1) (b+1) h') := by
  let ls := BB6Coverage.Agent8S1Encoder.binDec len q ++
    BB6Coverage.Agent8S1Encoder.markerWord m ++
    BB6Coverage.Agent8S1Encoder.d0 ++
    BB6Coverage.Agent8S1Encoder.binDec L n ++
    BB6Coverage.Agent8S1Encoder.lh
  let zStart := cfgToZ (TM63Uniform.rawStart r b ls [])
  let zEnd := cfgToZ (TM63Uniform.rawEnd r b ls [])
  have hzStart : zStart.state = .D := by
    simp [zStart, cfgToZ, natToQ, TM63Uniform.rawStart,
      TM63Uniform.dBoundary]
  have hzEnd : zEnd.state = .D := by
    simp [zEnd, cfgToZ, natToQ, TM63Uniform.rawEnd,
      TM63Uniform.dBoundaryZero]
  have hleftStart :
      zStart.cur :: zStart.left =
        BB6Coverage.Agent8S1Encoder.s1LeftFacing L n m (len+1+r)
          ((2*q+1)*2^r) := by
    rw [rawStart_left_stream]
    rw [BB6Coverage.Agent8S1Encoder.s1LeftFacing_carryPrefix
      L n m len q r hq]
    simp [ls, List.append_assoc]
  have hleftEnd :
      zEnd.cur :: zEnd.left =
        BB6Coverage.Agent8S1Encoder.s1LeftFacing L n m (len+1+r)
          (((2*q+1)*2^r)-1) := by
    rw [rawEnd_left_stream]
    unfold BB6Coverage.Agent8S1Encoder.s1LeftFacing
    rw [BB6Coverage.Agent8S1Encoder.binDec_sub_one_carryPrefix
      len q r hq]
    simp [ls, List.append_assoc]
  have hrightStart : ∀ i,
      BB6.ChampionTerminal.sideBit zStart.right i =
        BB6Coverage.Agent8S1Encoder.sideBit
          (BB6Coverage.Agent8S1Encoder.s1PhysicalRight b) i := by
    intro i
    rw [rawStart_right_list]
    rw [sideBit_append_false]
    rw [sideBit_eq]
    rw [BB6Coverage.Agent8S1Encoder.s1PhysicalRight_source]
  have hrightEnd : ∀ i,
      BB6.ChampionTerminal.sideBit zEnd.right i =
        BB6Coverage.Agent8S1Encoder.sideBit
          (BB6Coverage.Agent8S1Encoder.s1PhysicalRight (b+1)) i := by
    intro i
    rw [rawEnd_right_list]
    rw [sideBit_eq]
    rw [BB6Coverage.Agent8S1Encoder.s1PhysicalRight_source]
  have hzrun : BB6.ChampionTerminal.run (48+12*r+12*b) zStart =
      some zEnd := by
    have hc : (TM63Uniform.rawStart r b ls []).st < 6 := by
      simp [TM63Uniform.rawStart, TM63Uniform.dBoundary]
    have hsafe : ∀ t, t ≤ 48+12*r+12*b →
        ¬ ((TM63Uniform.run t (TM63Uniform.rawStart r b ls [])).st = 0 ∧
           (TM63Uniform.run t (TM63Uniform.rawStart r b ls [])).h = true) := by
      intro t ht
      exact TM63Uniform.counted_no_early_halt r b ls [] t ht
    have hrun := cfgRun_toZ (48+12*r+12*b)
      (TM63Uniform.rawStart r b ls []) hc hsafe
    rw [TM63Uniform.counted_all] at hrun
    exact hrun
  obtain ⟨h', hloc⟩ :=
    locatedRun_exists (48+12*r+12*b) zStart zEnd h hzrun
  have hfull :
      BB6.ChampionTerminal.fullRun (48+12*r+12*b)
        (BB6.ChampionTerminal.embedFull zStart h) =
      some (BB6.ChampionTerminal.embedFull zEnd h') := by
    have hsem := BB6.ChampionTerminal.run_semiconjugacy
      (48+12*r+12*b) zStart h
    rw [hloc] at hsem
    simpa using hsem.symm
  have htransport := fullRun_toConfig (48+12*r+12*b)
    (BB6.ChampionTerminal.embedFull zStart h)
  have hsource :
      BB6Coverage.run BB6Coverage.Agent48Champion.tm2 (48+12*r+12*b)
        (fullToConfig (BB6.ChampionTerminal.embedFull zStart h)) =
      some (fullToConfig (BB6.ChampionTerminal.embedFull zEnd h')) := by
    rw [hfull] at htransport
    simpa using htransport.symm
  have hin :
      fullToConfig (BB6.ChampionTerminal.embedFull zStart h) =
        BB6Coverage.Agent8S1Encoder.s1Config L n m (len+1+r)
          ((2*q+1)*2^r) b h := by
    apply fullToConfig_embed_s1 zStart h L n m (len+1+r)
      ((2*q+1)*2^r) b hzStart hleftStart hrightStart
  have hout :
      fullToConfig (BB6.ChampionTerminal.embedFull zEnd h') =
        BB6Coverage.Agent8S1Encoder.s1Config L n m (len+1+r)
          (((2*q+1)*2^r)-1) (b+1) h' := by
    apply fullToConfig_embed_s1 zEnd h' L n m (len+1+r)
      (((2*q+1)*2^r)-1) (b+1) hzEnd hleftEnd hrightEnd
  rw [hin, hout] at hsource
  exact ⟨h', hsource⟩

/-- Every valid positive source S1 counter has a counted original-machine
Inc0 decrement step. The odd-part factorization is supplied internally. -/
theorem s1_inc0_counted_anyPositive
    (L n m a z b : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) :
    ∃ q r len h',
      z = (2*q+1)*2^r ∧
      a = len+1+r ∧
      q < 2^len ∧
      BB6Coverage.run BB6Coverage.Agent48Champion.tm2 (48+12*r+12*b)
        (BB6Coverage.Agent8S1Encoder.s1Config L n m a z b h) =
      some (BB6Coverage.Agent8S1Encoder.s1Config L n m a (z-1) (b+1) h') := by
  obtain ⟨q,r,len,hr,ha,hq,_hcells⟩ :=
    BB6Coverage.Agent8S1Encoder.s1Config_anyPositive_carry
      L n m a z b h hz hzlt
  obtain ⟨h', hrun⟩ :=
    s1_inc0_counted_of_factorization L n m len q r b h hq
  refine ⟨q,r,len,h',hr,ha,hq,?_⟩
  simpa [ha,hr] using hrun

end BB6Coverage.Agent24CountedS1Carry
