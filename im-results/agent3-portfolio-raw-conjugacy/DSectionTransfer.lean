import DStartFinite
import Lean.Elab.Tactic.Omega
namespace BB6.Portfolio

/-- Composition of partial-machine raw runs at arbitrary times. -/
theorem run_add (M : Machine) (t n : Nat) (c : Option Cfg) :
    run M (t+n) c = run M n (run M t c) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    change (run M (t+n) c).bind (step M) =
      (run M n (run M t c)).bind (step M)
    rw [ih]

theorem run_none (M : Machine) (n : Nat) : run M n none=none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run,ih]

def HaltsAtCfg (M : Machine) (c : Cfg) (t : Nat) : Prop :=
  ∃ last, run M t (some c)=some last ∧ step M last=none

def HaltsCfg (M : Machine) (c : Cfg) : Prop :=
  ∃ t, HaltsAtCfg M c t

theorem haltsAt_after_prefix (M : Machine) (c d : Cfg) (t n : Nat)
    (hp : run M t (some c)=some d) :
    HaltsAtCfg M c (t+n) ↔ HaltsAtCfg M d n := by
  unfold HaltsAtCfg
  rw [run_add, hp]

theorem no_halt_before_prefix (M : Machine) (c d : Cfg) (t k : Nat)
    (hp : run M t (some c)=some d) (hk : HaltsAtCfg M c k) :
    t ≤ k := by
  by_cases hle : t ≤ k
  · exact hle
  have hlt : k < t := by omega
  have hle2 : k+1≤t := by omega
  obtain ⟨last, hr, hs⟩ := hk
  have hnone : run M (k+1) (some c)=none := by
    simp [run,hr,hs]
  have heq : (k+1)+(t-(k+1))=t := by omega
  have hbad : run M t (some c)=none := by
    rw [←heq,run_add,hnone]
    exact run_none M _
  rw [hp] at hbad
  cases hbad

theorem haltsCfg_after_prefix (M : Machine) (c d : Cfg) (t : Nat)
    (hp : run M t (some c)=some d) :
    HaltsCfg M c ↔ HaltsCfg M d := by
  constructor
  · rintro ⟨k,hk⟩
    have hle := no_halt_before_prefix M c d t k hp hk
    have heq : t+(k-t)=k := by omega
    refine ⟨k-t, ?_⟩
    apply (haltsAt_after_prefix M c d t (k-t) hp).mp
    simpa only [heq] using hk
  · rintro ⟨n,hn⟩
    exact ⟨t+n,(haltsAt_after_prefix M c d t n hp).mpr hn⟩

theorem haltsFrom_as_cfg (M : Machine) (s : State) :
    haltsFrom M s ↔ HaltsCfg M (blank s) := Iff.rfl

/-- Translation of both entire physical tape and head, for arbitrary offset. -/
def translateCfg (delta : Int) (c : Cfg) : Cfg :=
  ⟨c.state,c.head+delta,fun i => c.tape (i-delta)⟩

theorem translate_update (tape : Int → Bool) (head delta : Int) (w : Bool) :
    (fun i => updateTape tape head w (i-delta)) =
      updateTape (fun i => tape (i-delta)) (head+delta) w := by
  funext i
  by_cases hi : i-delta=head
  · have hi' : i=head+delta := by omega
    simp [updateTape,hi,hi']
  · have hi' : i≠head+delta := by omega
    simp [updateTape,hi,hi']

theorem translate_step (M : Machine) (delta : Int) (c : Cfg) :
    step M (translateCfg delta c)=(step M c).map (translateCfg delta) := by
  cases h : M c.state (c.tape c.head) with
  | none => simp [step,translateCfg,h]
  | some instr =>
    rcases instr with ⟨w,d,s⟩
    have hloc : c.head+delta-delta=c.head := by omega
    simp only [step,translateCfg,hloc,h,Option.map_some]
    congr 1
    congr 1
    · omega
    · exact (translate_update c.tape c.head delta w).symm

theorem translate_roundtrip (delta : Int) (c : Cfg) :
    translateCfg (-delta) (translateCfg delta c) = c := by
  cases c with
  | mk s h tape =>
    simp only [translateCfg]
    congr 1
    · omega
    · funext i
      have : i- -delta-delta=i := by omega
      simp only [this]

theorem translate_haltsAt_forward (M : Machine) (delta : Int) (c : Cfg)
    (n : Nat) (hh : HaltsAtCfg M c n) :
    HaltsAtCfg M (translateCfg delta c) n := by
  obtain ⟨last,hr,hs⟩ := hh
  have ht := run_transport M M (translateCfg delta) (translate_step M delta)
    n (some c)
  simp only [Option.map_some,hr] at ht
  refine ⟨translateCfg delta last, ht, ?_⟩
  rw [translate_step,hs]
  rfl

theorem translate_haltsCfg_iff (M : Machine) (delta : Int) (c : Cfg) :
    HaltsCfg M (translateCfg delta c) ↔ HaltsCfg M c := by
  constructor
  · rintro ⟨n,hn⟩
    have hh := translate_haltsAt_forward M (-delta) (translateCfg delta c) n hn
    simpa only [translate_roundtrip] using (show HaltsCfg M
      (translateCfg (-delta) (translateCfg delta c)) from ⟨n,hh⟩)
  · rintro ⟨n,hn⟩
    exact ⟨n,translate_haltsAt_forward M delta c n hn⟩

theorem translate_F0Pure (n : Nat) (h delta : Int) :
    translateCfg delta (F0Pure n h) = F0Pure n (h+delta) := by
  simp only [translateCfg,F0Pure]
  congr 1
  funext i
  have hiff : (h < i-delta ∧ i-delta ≤ h+(n:Int)) ↔
      (h+delta < i ∧ i≤h+delta+(n:Int)) := by omega
  by_cases hp : h < i-delta ∧ i-delta ≤ h+(n:Int)
  · have hq := hiff.mp hp
    simp [hp,hq]
  · have hq : ¬(h+delta < i ∧ i≤h+delta+(n:Int)) := by
      intro htmp
      exact hp (hiff.mpr htmp)
    simp [hp,hq]

theorem halts_F0Pure_shift (M : Machine) (n : Nat) (h : Int) :
    HaltsCfg M (F0Pure n h) ↔ HaltsCfg M (F0Pure n 0) := by
  have htrans := translate_haltsCfg_iff M (-h) (F0Pure n h)
  rw [translate_F0Pure] at htrans
  have heq : h+ -h=0 := by omega
  rw [heq] at htrans
  exact htrans.symm

theorem root_B_halts_iff_I5 :
    HaltsCfg D0 (blank (1:State)) ↔ HaltsCfg D0 (F0Pure 5 0) := by
  exact (haltsCfg_after_prefix D0 (blank (1:State)) (F0Pure 5 (-3)) 15
    blank_root_B_to_I5).trans (halts_F0Pure_shift D0 5 (-3))

theorem root_C_halts_iff_I15 :
    HaltsCfg D0 (blank (2:State)) ↔ HaltsCfg D0 (F0Pure 15 0) := by
  exact (haltsCfg_after_prefix D0 (blank (2:State)) (F0Pure 15 (-12)) 92
    blank_root_C_to_I15).trans (halts_F0Pure_shift D0 15 (-12))

theorem root_F_halts_iff_I39 :
    HaltsCfg D0 (blank (5:State)) ↔ HaltsCfg D0 (F0Pure 39 0) := by
  exact (haltsCfg_after_prefix D0 (blank (5:State)) (F0Pure 39 (-35)) 403
    blank_root_F_to_I39).trans (halts_F0Pure_shift D0 39 (-35))

/-- The three *rooted original machine* halting problems, expressed as exact
    universal equivalences to pure-unary sections of the common D0 table. -/
theorem D3_root_halts_iff_I5 :
    haltsFrom D3 (0:State) ↔ HaltsCfg D0 (F0Pure 5 0) :=
  D3_halts_from_blank.trans (haltsFrom_as_cfg D0 (1:State) |>.trans root_B_halts_iff_I5)

theorem D2_root_halts_iff_I15 :
    haltsFrom D2 (0:State) ↔ HaltsCfg D0 (F0Pure 15 0) :=
  D2_halts_from_blank.trans (haltsFrom_as_cfg D0 (2:State) |>.trans root_C_halts_iff_I15)

theorem D1_root_halts_iff_I39 :
    haltsFrom D1 (0:State) ↔ HaltsCfg D0 (F0Pure 39 0) :=
  D1_halts_from_blank.trans (haltsFrom_as_cfg D0 (5:State) |>.trans root_F_halts_iff_I39)

#print axioms translate_step
#print axioms haltsCfg_after_prefix
#print axioms D3_root_halts_iff_I5
#print axioms D2_root_halts_iff_I15
#print axioms D1_root_halts_iff_I39
end BB6.Portfolio
