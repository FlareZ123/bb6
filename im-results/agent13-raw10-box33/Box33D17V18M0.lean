import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V18M0
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .B false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .A true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .D true c)
  | .E,false => some (right .E false c)
  | .E,true => some (left .F true c)
  | .F,false => some (right .A true c)
  | .F,true => none
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
theorem leftOne (l r : Stream) : run 18 (cfg .A (word [true,true,true,false,true,false,true,false] l) (word [false,false] r)) = some (cfg .A l (word [false,false,true,true,true,true,true,true,false,true] r)) := by
  have h0 : run 10 (cfg .A (word [true,true,true,false,true,false,true,false] l) (word [false,false] r)) = some (cfg .B (word [false,true,true,false] l) (word [false,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 8 (cfg .B (word [false,true,true,false] l) (word [false,true,true,true,false,true] r)) = some (cfg .A l (word [false,false,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 18=10+8 by decide,run_add (10) 8,h0,Option.bind_some,h1]
theorem rightOne (l r : Stream) : run 8 (cfg .A l (word [true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false] l) r) := by
  have h0 : run 8 (cfg .A l (word [true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false] l) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact h0
theorem core3 (r : Stream) : run 134 (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,false] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) r) := by
  have h0 : run 10 (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,false] r)) = some (cfg .B (word [false,true,true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 10 (cfg .B (word [false,true,true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true] r)) = some (cfg .C (word [true,true,true,false,true,false,true] z) (word [true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 10 (cfg .C (word [true,true,true,false,true,false,true] z) (word [true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true] z) (word [true,false,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 10 (cfg .A (word [true] z) (word [true,false,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .E z (word [false,false,false,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 10 (cfg .E z (word [false,false,false,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .B (word [false,true,false,true,false,true,false,false] z) (word [true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h5 : run 10 (cfg .B (word [false,true,false,true,false,true,false,false] z) (word [true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .D (word [false,true,false,true,false,false] z) (word [true,false,true,true,true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h6 : run 10 (cfg .D (word [false,true,false,true,false,false] z) (word [true,false,true,true,true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [false,false] z) (word [true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h7 : run 10 (cfg .A (word [false,false] z) (word [true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .E (word [false,false,false] z) (word [true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h8 : run 10 (cfg .E (word [false,false,false] z) (word [true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .B (word [false,false,true,false,true,false,false] z) (word [false,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h9 : run 10 (cfg .B (word [false,false,true,false,true,false,false] z) (word [false,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .B (word [false,true,false] z) (word [false,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h10 : run 10 (cfg .B (word [false,true,false] z) (word [false,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .E (word [false] z) (word [false,false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h11 : run 10 (cfg .E (word [false] z) (word [false,false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h12 : run 10 (cfg .A (word [true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h13 : run 4 (cfg .A (word [true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,false,true] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 134=10+10+10+10+10+10+10+10+10+10+10+10+10+4 by decide,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10) 4,run_add (10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10) 10,run_add (10+10+10+10+10) 10,run_add (10+10+10+10) 10,run_add (10+10+10) 10,run_add (10+10) 10,run_add (10) 10,h0,Option.bind_some,h1,Option.bind_some,h2,Option.bind_some,h3,Option.bind_some,h4,Option.bind_some,h5,Option.bind_some,h6,Option.bind_some,h7,Option.bind_some,h8,Option.bind_some,h9,Option.bind_some,h10,Option.bind_some,h11,Option.bind_some,h12,Option.bind_some,h13]
theorem core6 (r : Stream) : run 156 (cfg .A (word [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,false] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) r) := by
  have h0 : run 10 (cfg .A (word [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,false] r)) = some (cfg .B (word [false,true,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 10 (cfg .B (word [false,true,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true] r)) = some (cfg .C (word [true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 10 (cfg .C (word [true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .C (word [true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 10 (cfg .C (word [true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .D (word [true,false,true] z) (word [false,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 10 (cfg .D (word [true,false,true] z) (word [false,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .B (word [false] z) (word [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h5 : run 10 (cfg .B (word [false] z) (word [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .F (word [false,false] z) (word [false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h6 : run 10 (cfg .F (word [false,false] z) (word [false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [false,true,false,true,false,true,false,false] z) (word [true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h7 : run 10 (cfg .A (word [false,true,false,true,false,true,false,false] z) (word [true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,true,false,false] z) (word [true,false,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h8 : run 10 (cfg .A (word [true,true,false,false] z) (word [true,false,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .B (word [true,false] z) (word [false,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h9 : run 10 (cfg .B (word [true,false] z) (word [false,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,true,false,false] z) (word [true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h10 : run 10 (cfg .A (word [true,false,true,false,false] z) (word [true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .C (word [true,false,true,false,false] z) (word [true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h11 : run 10 (cfg .C (word [true,false,true,false,false] z) (word [true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .C (word [false] z) (word [false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h12 : run 10 (cfg .C (word [false] z) (word [false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h13 : run 10 (cfg .A (word [true,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h14 : run 10 (cfg .A (word [true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h15 : run 6 (cfg .A (word [true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,false,true] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 156=10+10+10+10+10+10+10+10+10+10+10+10+10+10+10+6 by decide,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10+10+10) 6,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10) 10,run_add (10+10+10+10+10) 10,run_add (10+10+10+10) 10,run_add (10+10+10) 10,run_add (10+10) 10,run_add (10) 10,h0,Option.bind_some,h1,Option.bind_some,h2,Option.bind_some,h3,Option.bind_some,h4,Option.bind_some,h5,Option.bind_some,h6,Option.bind_some,h7,Option.bind_some,h8,Option.bind_some,h9,Option.bind_some,h10,Option.bind_some,h11,Option.bind_some,h12,Option.bind_some,h13,Option.bind_some,h14,Option.bind_some,h15]
theorem core5 (r : Stream) : run 84 (cfg .A (word [true,true,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,false] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) r) := by
  have h0 : run 10 (cfg .A (word [true,true,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,false] r)) = some (cfg .B (word [false,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 10 (cfg .B (word [false,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true] r)) = some (cfg .C (word [true,false,true,false,true,true,true,false,true,false,true] z) (word [true,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 10 (cfg .C (word [true,false,true,false,true,true,true,false,true,false,true] z) (word [true,true,true,true,true,true,true,true,false,true] r)) = some (cfg .C (word [true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 10 (cfg .C (word [true,true,true,false,true,false,true] z) (word [false,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,true] z) (word [false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 10 (cfg .A (word [true,false,true] z) (word [false,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A z (word [true,false,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h5 : run 10 (cfg .A z (word [true,false,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .E (word [false,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h6 : run 10 (cfg .E (word [false,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h7 : run 10 (cfg .A (word [true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,false,true] r)) = some (cfg .A (word [true,false,true,false,true,true,true,false,true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,false,true] r)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h8 : run 4 (cfg .A (word [true,false,true,false,true,true,true,false,true,false,true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,false,true] r)) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) r) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 84=10+10+10+10+10+10+10+10+4 by decide,run_add (10+10+10+10+10+10+10+10) 4,run_add (10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10) 10,run_add (10+10+10+10+10) 10,run_add (10+10+10+10) 10,run_add (10+10+10) 10,run_add (10+10) 10,run_add (10) 10,h0,Option.bind_some,h1,Option.bind_some,h2,Option.bind_some,h3,Option.bind_some,h4,Option.bind_some,h5,Option.bind_some,h6,Option.bind_some,h7,Option.bind_some,h8]
theorem initCore  : run 166 (cfg .A z z) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) z) := by
  have h0 : run 10 (cfg .A z z) = some (cfg .B (word [false,true,false,false] z) z) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h1 : run 10 (cfg .B (word [false,true,false,false] z) z) = some (cfg .E (word [false] z) (word [false,false,true,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h2 : run 10 (cfg .E (word [false] z) (word [false,false,true,true,true] z)) = some (cfg .B (word [false,false,true,false,false] z) (word [false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h3 : run 10 (cfg .B (word [false,false,true,false,false] z) (word [false,true] z)) = some (cfg .F (word [false] z) (word [false,true,false,true,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h4 : run 10 (cfg .F (word [false] z) (word [false,true,false,true,true,true] z)) = some (cfg .D z (word [false,false,true,true,true,true,true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h5 : run 10 (cfg .D z (word [false,false,true,true,true,true,true,true] z)) = some (cfg .A (word [true,false,true,false,true,false,false] z) (word [true,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h6 : run 10 (cfg .A (word [true,false,true,false,true,false,false] z) (word [true,true] z)) = some (cfg .B (word [false,true,true,false,true,false,false] z) (word [false,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h7 : run 10 (cfg .B (word [false,true,true,false,true,false,false] z) (word [false,true,false,true] z)) = some (cfg .C (word [true,false,false] z) (word [true,true,true,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h8 : run 10 (cfg .C (word [true,false,false] z) (word [true,true,true,true,true,true,false,true] z)) = some (cfg .A (word [false] z) (word [true,false,true,true,true,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h9 : run 10 (cfg .A (word [false] z) (word [true,false,true,true,true,true,true,true,false,true] z)) = some (cfg .E (word [false,false,false] z) (word [true,true,true,true,true,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h10 : run 10 (cfg .E (word [false,false,false] z) (word [true,true,true,true,true,true,true,true,false,true] z)) = some (cfg .A (word [true,false,true,false,true,false,true,false,true,false,false] z) (word [false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h11 : run 10 (cfg .A (word [true,false,true,false,true,false,true,false,true,false,false] z) (word [false,true] z)) = some (cfg .F (word [true,false,true,false,true,false,false] z) (word [false,true,false,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h12 : run 10 (cfg .F (word [true,false,true,false,true,false,false] z) (word [false,true,false,true,true,true,false,true] z)) = some (cfg .A (word [true,false,true,false,false] z) (word [false,false,true,true,true,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h13 : run 10 (cfg .A (word [true,false,true,false,false] z) (word [false,false,true,true,true,true,true,true,false,true] z)) = some (cfg .A (word [false] z) (word [true,false,true,true,false,true,true,true,true,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h14 : run 10 (cfg .A (word [false] z) (word [true,false,true,true,false,true,true,true,true,true,true,true,false,true] z)) = some (cfg .E (word [false,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h15 : run 10 (cfg .E (word [false,false,false] z) (word [true,true,true,true,false,true,true,true,true,true,true,true,false,true] z)) = some (cfg .A (word [true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,false,true] z)) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h16 : run 6 (cfg .A (word [true,false,true,true,true,false,true,false,true,false,false] z) (word [true,true,true,true,false,true] z)) = some (cfg .A (word [true,true,true,false,true,false,true,false,true,true,true,false,true,false,true] z) z) := by
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 166=10+10+10+10+10+10+10+10+10+10+10+10+10+10+10+10+6 by decide,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10+10+10+10) 6,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10+10) 10,run_add (10+10+10+10+10+10) 10,run_add (10+10+10+10+10) 10,run_add (10+10+10+10) 10,run_add (10+10+10) 10,run_add (10+10) 10,run_add (10) 10,h0,Option.bind_some,h1,Option.bind_some,h2,Option.bind_some,h3,Option.bind_some,h4,Option.bind_some,h5,Option.bind_some,h6,Option.bind_some,h7,Option.bind_some,h8,Option.bind_some,h9,Option.bind_some,h10,Option.bind_some,h11,Option.bind_some,h12,Option.bind_some,h13,Option.bind_some,h14,Option.bind_some,h15,Option.bind_some,h16]
abbrev X := rep [true,true,true,false,true,false,true,false]
abbrev Y := rep [true,true,true,true,true,true,false,true]
abbrev marker := word [false,false]
abbrev P := rep [true,false]
abbrev Q := word [true,true]
abbrev T := Q (P 2 (push true z))

theorem leftSweep (n : Nat) (l r : Stream) :
    run (18*n) (A (X n l) (marker r)) = some (A l (marker (Y n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 18*(n+1)=18+18*n by omega,run_add]
    change (run 18 (cfg .A (word [true,true,true,false,true,false,true,false] (X n l)) (word [false,false] r))).bind _ = _
    rw [leftOne,Option.bind_some]
    change run (18*n) (A (X n l) (marker (Y 1 r))) = _
    rw [ih]
    rw [show Y (n+1) r = Y n (Y 1 r) from rep_add _ n 1 r]

theorem rightSweep (n : Nat) (l r : Stream) :
    run (8*n) (A l (Y n r)) = some (A (X n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 8*(n+1)=8+8*n by omega,run_add]
    change (run 8 (cfg .A l (word [true,true,true,true,true,true,false,true] (Y n r)))).bind _ = _
    rw [rightOne,Option.bind_some]
    change run (8*n) (A (X 1 l) (Y n r)) = _
    rw [ih]
    rw [show X (n+1) l = X n (X 1 l) from rep_add _ n 1 l]

inductive Mode where | three | six | five

def count : Mode → Nat | .three => 3 | .six => 6 | .five => 5
def next : Mode → Mode | .three => .six | .six => .five | .five => .three
def extra : Mode → Nat | .three => 0 | _ => 1
def cost : Mode → Nat | .three => 134 | .six => 156 | .five => 84
def core (k : Mode) : Stream := Q (P (count k) T)
def phase (n : Nat) (k : Mode) : Config := A (X n (core k)) z

theorem coreRun (k : Mode) (r : Stream) : run (cost k) (A (core k) (marker r)) = some (A (X (extra k) (core (next k))) r) := by
  cases k with
  | three => exact core3 r
  | six => exact core6 r
  | five => exact core5 r

theorem epoch (n : Nat) (k : Mode) : run (18*n+cost k+8*n) (phase n k) = some (phase (n+extra k) (next k)) := by
  have hz : marker z = z := by simp [word]
  have h := leftSweep n (core k) z
  rw [hz] at h
  unfold phase
  rw [run_add (18*n+cost k) (8*n),run_add (18*n) (cost k),h,Option.bind_some,coreRun,Option.bind_some,rightSweep]
  rw [show X (n+extra k) (core (next k)) = X n (X (extra k) (core (next k))) from rep_add _ _ _ _]

theorem neverPhase (t n : Nat) (k : Mode) : run t (phase n k) ≠ none := by
  induction t using Nat.strongRecOn generalizing n k with
  | ind t ih =>
    let s := 18*n+cost k+8*n
    have hs : 0 < s := by cases k <;> simp [s,cost] <;> omega
    have he : run s (phase n k) = some (phase (n+extra k) (next k)) := epoch n k
    intro h
    by_cases ht : t ≤ s
    · rw [←show t+(s-t)=s by omega,run_add,h] at he
      contradiction
    · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
      exact ih (t-s) (by omega) _ _ h

theorem neverBlank (t : Nat) : run t (A z z) ≠ none := by
  have hinit : run 166 (A z z) = some (phase 0 .three) := initCore
  intro h
  by_cases ht : t ≤ 166
  · rw [←show t+(166-t)=166 by omega,run_add,h] at hinit
    contradiction
  · rw [←show 166+(t-166)=t by omega,run_add,hinit,Option.bind_some] at h
    exact neverPhase _ _ _ h
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,6,11,4,1,13,17,15,18,23,4,0]
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
end BB6.Agent13.Box33D17V18M0
