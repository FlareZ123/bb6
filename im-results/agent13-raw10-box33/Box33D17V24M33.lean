import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V24M33
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (right .F false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .E true c)
  | .E,false => some (right .F true c)
  | .E,true => some (left .B true c)
  | .F,false => some (right .B true c)
  | .F,true => some (right .F false c)
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
def Path (c d : Config) : Prop := ∃ t, run t c = some d
theorem path_of {c d : Config} {t : Nat} (h : run t c = some d) : Path c d := ⟨t,h⟩
theorem Path.trans {a b c : Config} (h : Path a b) (g : Path b c) : Path a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨s,hs⟩ := g
  exact ⟨t+s,by rw [run_add,ht,Option.bind_some,hs]⟩
abbrev A := cfg .A
abbrev B := cfg .B
abbrev D := cfg .D
theorem popP (l r : Stream) : Path (cfg .A (word [false,false,true,false,false,false] l) (word [false,false,true,true,true,false] r)) (cfg .A l (word [false,false,true,true,true,false,true,true,true,true,true,false] r)) := by
  have h0 : run 12 (cfg .A (word [false,false,true,false,false,false] l) (word [false,false,true,true,true,false] r)) = some (cfg .A l (word [false,false,true,true,true,false,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem restoreP (l r : Stream) : Path (cfg .B l (word [true,true,true,true,true,false] r)) (cfg .B (word [true,false,false,false,false,false] l) r) := by
  have h0 : run 6 (cfg .B l (word [true,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem restore4 (l r : Stream) : Path (cfg .B l (word [true,true,true,true,false] r)) (cfg .B (word [true,false,false,false,false] l) r) := by
  have h0 : run 5 (cfg .B l (word [true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem restore6 (l r : Stream) : Path (cfg .B l (word [true,true,true,true,true,true,false] r)) (cfg .B (word [true,false,false,false,false,false,false] l) r) := by
  have h0 : run 7 (cfg .B l (word [true,true,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem exitB (l : Stream) : Path (cfg .B (word [true,false,false,false] l) (word [true,true] z)) (cfg .A l (word [false,false,true,true,true,false,true,true] z)) := by
  have h0 : run 12 (cfg .B (word [true,false,false,false] l) (word [true,true] z)) = some (cfg .B (word [false,false] l) (word [false,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 2 (cfg .B (word [false,false] l) (word [false,true,true,false,true,true] z)) = some (cfg .A l (word [false,false,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (path_of h0).trans (path_of h1)

theorem phase0Core (l r : Stream) : Path (cfg .A (word [false,false,false,true,false,false,false,false] l) (word [false,false,true,true,true,false] r)) (cfg .B (word [true,false,false,false,false,false,true,false,true,true,false,false,false,false] l) r) := by
  have h0 : run 12 (cfg .A (word [false,false,false,true,false,false,false,false] l) (word [false,false,true,true,true,false] r)) = some (cfg .B (word [true,false,true,true,false,false,false,false] l) (word [true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 6 (cfg .B (word [true,false,true,true,false,false,false,false] l) (word [true,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,true,false,true,true,false,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (path_of h0).trans (path_of h1)

theorem phase1Core (l r : Stream) : Path (cfg .A (word [false,false,true,false,true,true,false,false,false,false] l) (word [false,false,true,true,true,false] r)) (cfg .B (word [true,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false] l) r) := by
  have h0 : run 12 (cfg .A (word [false,false,true,false,true,true,false,false,false,false] l) (word [false,false,true,true,true,false] r)) = some (cfg .D (word [false,false,false,false] l) (word [true,false,true,true,true,false,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .D (word [false,false,false,false] l) (word [true,false,true,true,true,false,true,true,true,true,true,false] r)) = some (cfg .F (word [false,false,false,false,true,false,false,false,true,false,true,false,false,false] l) (word [true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 2 (cfg .F (word [false,false,false,false,true,false,false,false,true,false,true,false,false,false] l) (word [true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact ((path_of h0).trans (path_of h1)).trans (path_of h2)

theorem phase2Core (l r : Stream) : Path (cfg .A (word [true,false,true,false,false,false] l) (word [false,false,true,true,true,false] r)) (cfg .B (word [true,false,false,false,false,true,false,true,true,false,false,false] l) r) := by
  have h0 : run 12 (cfg .A (word [true,false,true,false,false,false] l) (word [false,false,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,true,false,true,true,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem phase3Enter (l r : Stream) : Path (cfg .A (word [false,true,false,true,true,false,false,false] l) (word [false,false,true,true,true,false] r)) (cfg .D l (word [true,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) := by
  have h0 : run 12 (cfg .A (word [false,true,false,true,true,false,false,false] l) (word [false,false,true,true,true,false] r)) = some (cfg .F (word [false,true,false,true,false,false] l) (word [true,false,false,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .F (word [false,true,false,true,false,false] l) (word [true,false,false,true,true,true,true,false] r)) = some (cfg .C (word [false,false] l) (word [true,true,true,true,false,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 6 (cfg .C (word [false,false] l) (word [true,true,true,true,false,true,true,true,true,true,true,false] r)) = some (cfg .D l (word [true,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact ((path_of h0).trans (path_of h1)).trans (path_of h2)

theorem prefix1000 (l r : Stream) : Path (cfg .D (word [true,false,false,false] l) (word [true,false] r)) (cfg .A l (word [false,false,true,true,true,false] r)) := by
  have h0 : run 4 (cfg .D (word [true,false,false,false] l) (word [true,false] r)) = some (cfg .A l (word [false,false,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem prefix00 (l r : Stream) : Path (cfg .A (word [false,false] l) (word [false,false,true,true,true,false] r)) (cfg .D l (word [true,false,true,true,true,true,true,false] r)) := by
  have h0 : run 8 (cfg .A (word [false,false] l) (word [false,false,true,true,true,false] r)) = some (cfg .D l (word [true,false,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem gY (l r : Stream) : Path (cfg .D (word [false,true,false,false,false,false] l) (word [true,false] r)) (cfg .B (word [true,false,true,true,false,false,false,false] l) r) := by
  have h0 : run 4 (cfg .D (word [false,true,false,false,false,false] l) (word [true,false] r)) = some (cfg .B (word [true,false,true,true,false,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem gZ (l r : Stream) : Path (cfg .D (word [true,false,true,true,false,false,false,false] l) (word [true,false] r)) (cfg .B (word [true,false,false,false,true,false,true,false,false,false] l) r) := by
  have h0 : run 12 (cfg .D (word [true,false,true,true,false,false,false,false] l) (word [true,false] r)) = some (cfg .B (word [true,false,false,false,true,false,true,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem gW (l r : Stream) : Path (cfg .D (word [true,false,false,false,true,false,true,false,false,false] l) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,true,false,true,true,false,false,false] l) r) := by
  have h0 : run 12 (cfg .D (word [true,false,false,false,true,false,true,false,false,false] l) (word [true,false] r)) = some (cfg .F (word [false,true,false,true,true,false,false,false] l) (word [true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 4 (cfg .F (word [false,true,false,true,true,false,false,false] l) (word [true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,true,false,true,true,false,false,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (path_of h0).trans (path_of h1)

theorem gBase0 (r : Stream) : Path (cfg .D (word [true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,true] z) (word [true,false] r)) = some (cfg .F (word [false,true] z) (word [false,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 6 (cfg .F (word [false,true] z) (word [false,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (path_of h0).trans (path_of h1)

theorem gBase1 (r : Stream) : Path (cfg .D (word [true,false,false,false,false,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,false,false,true,false,true,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,false,false,false,true,false,true] z) (word [true,false] r)) = some (cfg .E z (word [false,false,false,true,true,false,false,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .E z (word [false,false,false,true,true,false,false,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,true,false,true] z) (word [false,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 12 (cfg .B (word [true,false,false,false,true,false,true] z) (word [false,true,true,true,true,false] r)) = some (cfg .F (word [false,true,false,true,true,false,true] z) (word [true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 6 (cfg .F (word [false,true,false,true,true,false,true] z) (word [true,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,false,true,false,true,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)

theorem gBase2 (r : Stream) : Path (cfg .D (word [false,true,false,true,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,true,true,false,true,true,false,true] z) r) := by
  have h0 : run 4 (cfg .D (word [false,true,false,true,true,false,true] z) (word [true,false] r)) = some (cfg .B (word [true,false,true,true,false,true,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem gBase3 (r : Stream) : Path (cfg .D (word [true,false,true,true,false,true,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,true,false,true,true,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,true,true,false,true,true,false,true] z) (word [true,false] r)) = some (cfg .B (word [true,false,false,false,true,false,true,true,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem gBase4 (r : Stream) : Path (cfg .D (word [true,false,false,false,true,false,true,true,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,true,false,true,true,true,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,false,false,true,false,true,true,true,false,true] z) (word [true,false] r)) = some (cfg .F (word [false,true,false,true,true,true,true,false,true] z) (word [true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 4 (cfg .F (word [false,true,false,true,true,true,true,false,true] z) (word [true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,true,false,true,true,true,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (path_of h0).trans (path_of h1)

theorem gBase5 (r : Stream) : Path (cfg .D (word [true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [true,false] r)) = some (cfg .E (word [true,false,true] z) (word [true,true,false,true,true,false,false,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .E (word [true,false,true] z) (word [true,true,false,true,true,false,false,true,true,true,true,false] r)) = some (cfg .F (word [true,true,false,false,false,false,true] z) (word [false,false,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 12 (cfg .F (word [true,true,false,false,false,false,true] z) (word [false,false,true,true,true,true,true,false] r)) = some (cfg .B z (word [false,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 12 (cfg .B z (word [false,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) = some (cfg .F (word [true] z) (word [true,false,true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 12 (cfg .F (word [true] z) (word [true,false,true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) = some (cfg .B (word [true,true,false,false,true,false,true] z) (word [false,true,true,true,true,true,false,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h5 : run 12 (cfg .B (word [true,true,false,false,true,false,true] z) (word [false,true,true,true,true,true,false,true,true,true,true,true,true,false] r)) = some (cfg .F (word [false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [false,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h6 : run 8 (cfg .F (word [false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [false,true,true,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact ((((((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)).trans (path_of h4)).trans (path_of h5)).trans (path_of h6)

theorem gBase6 (r : Stream) : Path (cfg .D (word [false,false,true,false,true,false,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,true,false,true,false,true,false,true,false,true] z) r) := by
  have h0 : run 4 (cfg .D (word [false,false,true,false,true,false,true,false,true] z) (word [true,false] r)) = some (cfg .B (word [true,false,true,false,true,false,true,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact path_of h0

theorem gBase7 (r : Stream) : Path (cfg .D (word [true,false,true,false,true,false,true,false,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,false,true,false,true,false,true,false,true,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,true,false,true,false,true,false,true,false,true] z) (word [true,false] r)) = some (cfg .D z (word [false,false,true,true,false,false,true,true,false,false,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .D z (word [false,false,true,true,false,false,true,true,false,false,true,true,true,false] r)) = some (cfg .F (word [false,false,false,true,false,true] z) (word [false,false,true,true,false,false,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 12 (cfg .F (word [false,false,false,true,false,true] z) (word [false,false,true,true,false,false,true,true,true,false] r)) = some (cfg .B (word [true,false,true,true,false,true] z) (word [true,true,true,true,false,false,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 12 (cfg .B (word [true,false,true,true,false,true] z) (word [true,true,true,true,false,false,true,true,true,false] r)) = some (cfg .D (word [false,false,true,false,true,true,false,true] z) (word [true,false,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 10 (cfg .D (word [false,false,true,false,true,true,false,true] z) (word [true,false,true,true,true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,true,false,true,false,true,false,true,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact ((((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)).trans (path_of h4)

theorem gBase8 (r : Stream) : Path (cfg .D (word [true,false,true,false,true,false,true,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,false,true,false,false,false,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,true,false,true,false,true,true,false,true] z) (word [true,false] r)) = some (cfg .B (word [true,false,true,true] z) (word [true,true,false,false,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .B (word [true,false,true,true] z) (word [true,true,false,false,true,true,true,false] r)) = some (cfg .B (word [true,true] z) (word [false,true,true,false,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 12 (cfg .B (word [true,true] z) (word [false,true,true,false,true,true,true,true,true,false] r)) = some (cfg .F (word [false,false,true,false,false,false,true,false,true] z) (word [true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 4 (cfg .F (word [false,false,true,false,false,false,true,false,true] z) (word [true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,true,false,false,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)

theorem gBase9 (r : Stream) : Path (cfg .D (word [true,false,false,false,true,false,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,true,false,true,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,false,false,true,false,true] z) (word [true,false] r)) = some (cfg .F (word [false,true,false,true,true] z) (word [true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 4 (cfg .F (word [false,true,false,true,true] z) (word [true,true,true,false] r)) = some (cfg .B (word [true,false,false,false,false,true,false,true,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (path_of h0).trans (path_of h1)

theorem gBase10 (r : Stream) : Path (cfg .D (word [true,false,false,false,false,true,false,true,true] z) (word [true,false] r)) (cfg .B (word [true,false,false,false,false,false,false,true,false,false,false,false,true,false,true] z) r) := by
  have h0 : run 12 (cfg .D (word [true,false,false,false,false,true,false,true,true] z) (word [true,false] r)) = some (cfg .E z (word [false,true,false,true,true,false,false,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .E z (word [false,true,false,true,true,false,false,true,true,true,true,false] r)) = some (cfg .C (word [true,true,false,true] z) (word [true,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 12 (cfg .C (word [true,true,false,true] z) (word [true,true,true,true,true,true,true,false] r)) = some (cfg .F (word [true] z) (word [true,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 12 (cfg .F (word [true] z) (word [true,false,true,true,true,true,false,true,true,true,true,true,true,false] r)) = some (cfg .F (word [false,false,false,false,false,true,false,false,false,false,true,false,true] z) (word [true,false] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 2 (cfg .F (word [false,false,false,false,false,true,false,false,false,false,true,false,true] z) (word [true,false] r)) = some (cfg .B (word [true,false,false,false,false,false,false,true,false,false,false,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact ((((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)).trans (path_of h4)

theorem initPath  : Path (cfg .A z z) (cfg .A (word [false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [false,false,true,true,true,false,true,true] z)) := by
  have h0 : run 12 (cfg .A z z) = some (cfg .B (word [true,false,true] z) (word [true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 12 (cfg .B (word [true,false,true] z) (word [true,true] z)) = some (cfg .B (word [true] z) (word [false,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 12 (cfg .B (word [true] z) (word [false,true,true,false,true,true] z)) = some (cfg .F (word [false,true,false,true] z) (word [true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 12 (cfg .F (word [false,true,false,true] z) (word [true,true,true,false,true,true] z)) = some (cfg .B (word [true,true,true,false,false,false,false,true,false,true] z) (word [false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 12 (cfg .B (word [true,true,true,false,false,false,false,true,false,true] z) (word [false,true] z)) = some (cfg .C z (word [true,true,true,false,false,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h5 : run 12 (cfg .C z (word [true,true,true,false,false,true,true,true,true,false,true,true] z)) = some (cfg .F (word [false,false,true,false,true] z) (word [true,false,false,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h6 : run 12 (cfg .F (word [false,false,true,false,true] z) (word [true,false,false,true,true,true,true,false,true,true] z)) = some (cfg .F (word [false,true,true,false,true] z) (word [false,true,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h7 : run 12 (cfg .F (word [false,true,true,false,true] z) (word [false,true,true,true,true,true,true,false,true,true] z)) = some (cfg .C (word [false,false,true,false,false,false,false,false,false,true,false,true,true,false,true] z) (word [true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h8 : run 12 (cfg .C (word [false,false,true,false,false,false,false,false,false,true,false,true,true,false,true] z) (word [true,true] z)) = some (cfg .C (word [false,false,false,true,false,true,true,false,true] z) (word [true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h9 : run 12 (cfg .C (word [false,false,false,true,false,true,true,false,true] z) (word [true,true,true,true,true,false,true,true] z)) = some (cfg .F (word [false,false,true,false,true,true,false,true,true,false,true] z) (word [true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h10 : run 12 (cfg .F (word [false,false,true,false,true,true,false,true,true,false,true] z) (word [true,true,true,false,true,true] z)) = some (cfg .B (word [true,true,true,false,false,false,false,false,true,false,true,true,false,true,true,false,true] z) (word [false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h11 : run 12 (cfg .B (word [true,true,true,false,false,false,false,false,true,false,true,true,false,true,true,false,true] z) (word [false,true] z)) = some (cfg .B (word [true,true,true,false,true,true,false,true,true,false,true] z) (word [false,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h12 : run 12 (cfg .B (word [true,true,true,false,true,true,false,true,true,false,true] z) (word [false,true,true,true,true,false,true,true] z)) = some (cfg .F (word [false,false,true,false,true,true,true,false,true] z) (word [true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h13 : run 12 (cfg .F (word [false,false,true,false,true,true,true,false,true] z) (word [true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .C (word [false,false,true,false,false,false,false,false,true,false,false,false,true,false,true,true,true,false,true] z) (word [true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h14 : run 12 (cfg .C (word [false,false,true,false,false,false,false,false,true,false,false,false,true,false,true,true,true,false,true] z) (word [true,true] z)) = some (cfg .C (word [false,false,true,false,false,false,true,false,true,true,true,false,true] z) (word [true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h15 : run 12 (cfg .C (word [false,false,true,false,false,false,true,false,true,true,true,false,true] z) (word [true,true,true,true,true,false,true,true] z)) = some (cfg .C (word [true,false,true,true,true,false,true] z) (word [true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h16 : run 12 (cfg .C (word [true,false,true,true,true,false,true] z) (word [true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .F (word [false,false,true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h17 : run 12 (cfg .F (word [false,false,true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [true,true,true,false,true,true] z)) = some (cfg .B (word [true,true,true,false,false,false,false,false,true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h18 : run 12 (cfg .B (word [true,true,true,false,false,false,false,false,true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [false,true] z)) = some (cfg .B (word [true,true,true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [false,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h19 : run 12 (cfg .B (word [true,true,true,false,false,false,false,true,false,true,true,true,true,false,true] z) (word [false,true,true,true,true,false,true,true] z)) = some (cfg .C (word [true,true,true,false,true] z) (word [true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h20 : run 12 (cfg .C (word [true,true,true,false,true] z) (word [true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .D (word [false,true,false,false,false,false,true] z) (word [false,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h21 : run 12 (cfg .D (word [false,true,false,false,false,false,true] z) (word [false,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .D (word [true] z) (word [false,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h22 : run 12 (cfg .D (word [true] z) (word [false,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .D z (word [true,false,true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h23 : run 12 (cfg .D z (word [true,false,true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .E (word [false,false,true,false,true] z) (word [false,false,false,true,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h24 : run 12 (cfg .E (word [false,false,true,false,true] z) (word [false,false,false,true,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .F (word [false,false,false,false,true,false,true,false,true,false,true] z) (word [true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h25 : run 12 (cfg .F (word [false,false,false,false,true,false,true,false,true,false,true] z) (word [true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] z)) = some (cfg .F (word [false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h26 : run 12 (cfg .F (word [false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [true,true,true,false,true,true] z)) = some (cfg .B (word [true,true,true,false,false,false,false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h27 : run 6 (cfg .B (word [true,true,true,false,false,false,false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [false,true] z)) = some (cfg .A (word [false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,true,false,true] z) (word [false,false,true,true,true,false,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact (((((((((((((((((((((((((((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)).trans (path_of h4)).trans (path_of h5)).trans (path_of h6)).trans (path_of h7)).trans (path_of h8)).trans (path_of h9)).trans (path_of h10)).trans (path_of h11)).trans (path_of h12)).trans (path_of h13)).trans (path_of h14)).trans (path_of h15)).trans (path_of h16)).trans (path_of h17)).trans (path_of h18)).trans (path_of h19)).trans (path_of h20)).trans (path_of h21)).trans (path_of h22)).trans (path_of h23)).trans (path_of h24)).trans (path_of h25)).trans (path_of h26)).trans (path_of h27)


abbrev pword := [false,false,true,false,false,false]
abbrev xword := [true,false,false,false,false,false]
abbrev qword := [true,true,true,true,true,false]
abbrev rw := [false,false,true,true,true,false]
abbrev r0 := word [false,false,true,true,true,false,true,true] z
abbrev bx := [true,false,false,false]
abbrev P := rep pword
abbrev X := rep xword
abbrev Qp := rep qword
abbrev G (l v : Stream) := ∀ r : Stream, Path (D l (word [true,false] r)) (B v r)

theorem gX {l v : Stream} (h : G l v) : G (word xword l) (word xword v) := by
  intro r
  exact (((prefix1000 (word [false,false] l) r).trans (prefix00 l r)).trans (h (word qword r))).trans (restoreP v r)

theorem gV {l v : Stream} (h : G l v) : G (word [true,false,false,false,false,true,false,true,true,false,false,false] l) (word xword (word [false,true,false,false,false,false] v)) := by
  intro r
  exact ((((prefix1000 (word [false,true,false,true,true,false,false,false] l) r).trans (phase3Enter l r)).trans (h (word [true,true,true,true,false,true,true,true,true,true,true,false] r))).trans (restore4 v (word [true,true,true,true,true,true,false] r))).trans (restore6 (word [true,false,false,false,false] v) r)

inductive Good : Stream → Prop where
  | b0 : Good (word [true,false,true] z)
  | b1 : Good (word [true,false,false,false,false,true,false,true] z)
  | b2 : Good (word [false,true,false,true,true,false,true] z)
  | b3 : Good (word [true,false,true,true,false,true,true,false,true] z)
  | b4 : Good (word [true,false,false,false,true,false,true,true,true,false,true] z)
  | b5 : Good (word [true,false,false,false,false,true,false,true,true,true,true,false,true] z)
  | b6 : Good (word [false,false,true,false,true,false,true,false,true] z)
  | b7 : Good (word [true,false,true,false,true,false,true,false,true,false,true] z)
  | b8 : Good (word [true,false,true,false,true,false,true,true,false,true] z)
  | b9 : Good (word [true,false,false,false,true,false,true] z)
  | b10 : Good (word [true,false,false,false,false,true,false,true,true] z)
  | c0 {u : Stream} : Good u → Good (word [true,false,false,false,false,false] u)
  | c1 {u : Stream} : Good u → Good (word [false,true,false,false,false,false] u)
  | c2 {u : Stream} : Good u → Good (word [true,false,true,true,false,false,false,false] u)
  | c3 {u : Stream} : Good u → Good (word [true,false,false,false,true,false,true,false,false,false] u)
  | c4 {u : Stream} : Good u → Good (word [true,false,false,false,false,true,false,true,true,false,false,false] u)

theorem goodG (u : Stream) (hu : Good u) : ∃ v, Good v ∧ G u v := by
  induction hu with
  | b0 => exact ⟨_, Good.b1, gBase0⟩
  | b1 => exact ⟨_, Good.c0 (Good.b2), gBase1⟩
  | b2 => exact ⟨_, Good.b3, gBase2⟩
  | b3 => exact ⟨_, Good.b4, gBase3⟩
  | b4 => exact ⟨_, Good.b5, gBase4⟩
  | b5 => exact ⟨_, Good.c0 (Good.c1 (Good.b6)), gBase5⟩
  | b6 => exact ⟨_, Good.b7, gBase6⟩
  | b7 => exact ⟨_, Good.c0 (Good.b8), gBase7⟩
  | b8 => exact ⟨_, Good.c0 (Good.b9), gBase8⟩
  | b9 => exact ⟨_, Good.b10, gBase9⟩
  | b10 => exact ⟨_, Good.c0 (Good.c1 (Good.b0)), gBase10⟩
  | c0 hu ih =>
    obtain ⟨v,hv,h⟩ := ih
    exact ⟨_, Good.c0 hv, gX h⟩
  | c1 hu ih => exact ⟨_,Good.c2 hu,gY _⟩
  | c2 hu ih => exact ⟨_,Good.c3 hu,gZ _⟩
  | c3 hu ih => exact ⟨_,Good.c4 hu,gW _⟩
  | c4 hu ih =>
    obtain ⟨v,hv,h⟩ := ih
    exact ⟨_,Good.c0 (Good.c1 hv),gV h⟩

theorem sweepLeft (n : Nat) (l r : Stream) : Path (A (P n l) (word rw r)) (A l (word rw (Qp n r))) := by
  induction n generalizing r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h := (popP (P n l) r).trans (ih (word qword r))
    rw [show Qp (n+1) r = Qp n (word qword r) from rep_add _ n 1 r]
    exact h

theorem sweepRight (n : Nat) (l r : Stream) : Path (B l (Qp n r)) (B (X n l) r) := by
  induction n generalizing l with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h := (restoreP l (Qp n r)).trans (ih (word xword l))
    rw [show X (n+1) l = X n (word xword l) from rep_add _ n 1 l]
    exact h

theorem shift (n : Nat) (l : Stream) : X n (word bx l) = word bx (P n l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change word xword (X n (word bx l)) = word bx (word pword (P n l))
    rw [ih]
    rfl

theorem liftCore (n : Nat) (l l' : Stream) (h : ∀ r : Stream, Path (A l (word rw r)) (B (word bx l') r)) : ∃ t, 0<t ∧ run t (A (P n l) r0) = some (A (P n l') r0) := by
  have h1 := (sweepLeft n l (word [true,true] z)).trans (h (Qp n (word [true,true] z)))
  have h2 := (sweepRight n (word bx l') (word [true,true] z))
  rw [shift] at h2
  obtain ⟨t,ht⟩ := h1.trans h2
  obtain ⟨s,hs⟩ := exitB (P n l')
  have hp : 0 < t := by
    cases t with
    | zero => simp [BB6.Agent13.Box33PrefixMacro.run,cfg] at ht
    | succ t => omega
  change run t (A (P n l) r0) = some (B (word bx (P n l')) (word [true,true] z)) at ht
  exact ⟨t+s,by omega,by rw [run_add,ht,Option.bind_some,hs]⟩

theorem phase3Core {l v : Stream} (h : G l v) (r : Stream) : Path (A (word [false,true,false,true,true,false,false,false] l) (word rw r)) (B (word bx (word [false,false,false,true,false,false,false,false] v)) r) := by
  exact (((phase3Enter l r).trans (h (word [true,true,true,true,false,true,true,true,true,true,true,false] r))).trans (restore4 v (word [true,true,true,true,true,true,false] r))).trans (restore6 (word [true,false,false,false,false] v) r)

def S0 (n : Nat) (u : Stream) := A (P n (word [false,false,false,true,false,false,false,false] u)) r0
def S1 (n : Nat) (u : Stream) := A (P n (word [false,false,true,false,true,true,false,false,false,false] u)) r0
def S2 (n : Nat) (u : Stream) := A (P n (word [true,false,true,false,false,false] u)) r0
def S3 (n : Nat) (u : Stream) := A (P n (word [false,true,false,true,true,false,false,false] u)) r0

theorem epoch (n : Nat) (u : Stream) (hu : Good u) : ∃ t v, 0<t ∧ Good v ∧ run t (S0 n u) = some (S0 (n+1) v) := by
  obtain ⟨v,hv,hg⟩ := goodG u hu
  obtain ⟨a,ha,h1⟩ := liftCore n _ _ (phase0Core u)
  obtain ⟨b,hb,h2⟩ := liftCore n _ _ (phase1Core u)
  obtain ⟨c,hc,h3⟩ := liftCore (n+1) _ _ (phase2Core u)
  obtain ⟨d,hd,h4⟩ := liftCore (n+1) _ _ (phase3Core hg)
  refine ⟨a+b+c+d,v,by omega,hv,?_⟩
  have h1' : run a (S0 n u) = some (S1 n u) := h1
  have h2' : run b (S1 n u) = some (S2 (n+1) u) := by
    unfold S1 S2
    rw [show P (n+1) (word [true,false,true,false,false,false] u) = P n (word pword (word [true,false,true,false,false,false] u)) from rep_add _ n 1 _]
    exact h2
  have h3' : run c (S2 (n+1) u) = some (S3 (n+1) u) := h3
  have h4' : run d (S3 (n+1) u) = some (S0 (n+1) v) := h4
  rw [run_add (a+b+c) d,run_add (a+b) c,run_add a b,h1',Option.bind_some,h2',Option.bind_some,h3',Option.bind_some,h4']

theorem neverPhase (t n : Nat) (u : Stream) (hu : Good u) : run t (S0 n u) ≠ none := by
  induction t using Nat.strongRecOn generalizing n u with
  | ind t ih =>
    intro h
    obtain ⟨s,v,hs,hv,he⟩ := epoch n u hu
    by_cases ht : t≤s
    · rw [←show t+(s-t)=s by omega,run_add,h] at he
      contradiction
    · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ _ hv h

theorem neverBlank (t : Nat) : run t (A z z) ≠ none := by
  have hi : Path (A z z) (S0 1 (word [false,false,true,false,true,false,true,false,true] z)) := initPath
  obtain ⟨s,he⟩ := hi
  intro h
  by_cases ht : t≤s
  · rw [←show t+(s-t)=s by omega,run_add,h] at he
    contradiction
  · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
    exact neverPhase _ _ _ Good.b6 h
#print axioms neverBlank
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,0,11,22,1,13,17,19,24,7,8,22]
def table : Machine := fun s => decode (codes.getD (index s).val 0)
theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map BB6.Agent13.Box33PrefixMacro.project = step (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never : NeverHalts table := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever table step project_step
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank n
def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V24M33
