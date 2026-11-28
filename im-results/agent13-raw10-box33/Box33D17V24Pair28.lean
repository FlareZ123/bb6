import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V24Pair28
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ rep_zero cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
inductive Variant where | m28 | m41 deriving DecidableEq

def step (v : Variant) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .B false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .B false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (if v = .m28 then right .C true c else right .B false c)
  | .E,false => some (right .F true c)
  | .E,true => some (left .F false c)
  | .F,false => some (right .A false c)
  | .F,true => none
abbrev run (v : Variant) := BB6.Agent13.Box33PrefixMacro.run (step v)
theorem run_add (v : Variant) (m n : Nat) (c : Config) : run v (m+n) c = (run v m c).bind (run v n) :=
  BB6.Agent13.Box33PrefixMacro.run_add (step v) m n c
def Path (v : Variant) (c d : Config) : Prop := ∃ t, run v t c = some d
theorem path_of {v : Variant} {c d : Config} {t : Nat} (h : run v t c = some d) : Path v c d := ⟨t,h⟩
theorem Path.trans {v : Variant} {a b c : Config} (h : Path v a b) (g : Path v b c) : Path v a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨s,hs⟩ := g
  exact ⟨t+s,by rw [run_add,ht,Option.bind_some,hs]⟩
abbrev A := cfg .A
abbrev B := cfg .B
abbrev P := rep [true,false]
abbrev Qp := rep [false,true]
abbrev O := rep [true]
abbrev Zeros := rep [false]
abbrev R (s : Nat) (r : Stream) := word [false,false] (O s r)
abbrev R0 := R 1 z
abbrev I := word [true,false,true]
theorem popP (v : Variant) (l r : Stream) : Path v (cfg .A (word [true,false] l) (word [false,false,true] r)) (cfg .A l (word [false,false,true,true,true] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 8 (cfg .A (word [true,false] l) (word [false,false,true] r)) = some (cfg .A l (word [false,false,true,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 6 (cfg .A (word [true,false] l) (word [false,false,true] r)) = some (cfg .A l (word [false,false,true,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem pop110 (v : Variant) (l r : Stream) : Path v (cfg .A (word [true,true,false] l) (word [false,false,true] r)) (cfg .A l (word [false,false,true,true,true,true] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 11 (cfg .A (word [true,true,false] l) (word [false,false,true] r)) = some (cfg .A l (word [false,false,true,true,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 9 (cfg .A (word [true,true,false] l) (word [false,false,true] r)) = some (cfg .A l (word [false,false,true,true,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem turn00 (v : Variant) (l r : Stream) : Path v (cfg .A (word [false,false] l) (word [false,false,true] r)) (cfg .A (word [false,true] l) (word [false,true,true] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 6 (cfg .A (word [false,false] l) (word [false,false,true] r)) = some (cfg .A (word [false,true] l) (word [false,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 6 (cfg .A (word [false,false] l) (word [false,false,true] r)) = some (cfg .A (word [false,true] l) (word [false,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem qFirst (v : Variant) (l r : Stream) : Path v (cfg .A (word [false,true,false] l) (word [false,false,true] r)) (cfg .A (word [false] l) (word [false,false,false,true,true] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 6 (cfg .A (word [false,true,false] l) (word [false,false,true] r)) = some (cfg .A (word [false] l) (word [false,false,false,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 6 (cfg .A (word [false,true,false] l) (word [false,false,true] r)) = some (cfg .A (word [false] l) (word [false,false,false,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem qNext (v : Variant) (l r : Stream) : Path v (cfg .A (word [false,true,false] l) (word [false,false,false] r)) (cfg .A (word [false] l) (word [false,false,false,true,false] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 6 (cfg .A (word [false,true,false] l) (word [false,false,false] r)) = some (cfg .A (word [false] l) (word [false,false,false,true,false] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 6 (cfg .A (word [false,true,false] l) (word [false,false,false] r)) = some (cfg .A (word [false] l) (word [false,false,false,true,false] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem qTurn (v : Variant) (l r : Stream) : Path v (cfg .A (word [false,false] l) (word [false,false,false] r)) (cfg .A (word [false,true] l) (word [false,true,false] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 6 (cfg .A (word [false,false] l) (word [false,false,false] r)) = some (cfg .A (word [false,true] l) (word [false,true,false] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 6 (cfg .A (word [false,false] l) (word [false,false,false] r)) = some (cfg .A (word [false,true] l) (word [false,true,false] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem qFlip (v : Variant) (l r : Stream) : Path v (cfg .A l (word [false,true,false] r)) (cfg .A l (word [true,false,true] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 4 (cfg .A l (word [false,true,false] r)) = some (cfg .A l (word [true,false,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 4 (cfg .A l (word [false,true,false] r)) = some (cfg .A l (word [true,false,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem qExit (v : Variant) (l r : Stream) : Path v (cfg .A (word [false,true] l) (word [true,false,true] r)) (cfg .A (word [true] l) (word [false,false,true,true] r)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 3 (cfg .A (word [false,true] l) (word [true,false,true] r)) = some (cfg .A (word [true] l) (word [false,false,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 3 (cfg .A (word [false,true] l) (word [true,false,true] r)) = some (cfg .A (word [true] l) (word [false,false,true,true] r)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem root0 (v : Variant) (l : Stream) : Path v (cfg .A (word [false,false] l) (word [false,false,true] z)) (cfg .A (word [true,false,true] l) (word [false,false,true] z)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 11 (cfg .A (word [false,false] l) (word [false,false,true] z)) = some (cfg .A (word [true,false,true] l) (word [false,false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0
  | m41 =>
    have h0 : run .m41 11 (cfg .A (word [false,false] l) (word [false,false,true] z)) = some (cfg .A (word [true,false,true] l) (word [false,false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact path_of h0

theorem root1 (v : Variant) (l : Stream) : Path v (cfg .A (word [true,false,true,false,false,false] l) (word [false,false,true] z)) (cfg .A (word [false,false,false,false,true,false,true] l) (word [false,false,true] z)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 12 (cfg .A (word [true,false,true,false,false,false] l) (word [false,false,true] z)) = some (cfg .C (word [true,false,false,false] l) (word [false,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h1 : run .m28 12 (cfg .C (word [true,false,false,false] l) (word [false,true,true,true,true] z)) = some (cfg .B (word [false,true,false,true] l) (word [true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h2 : run .m28 7 (cfg .B (word [false,true,false,true] l) (word [true,true,true,true,true] z)) = some (cfg .A (word [false,false,false,false,true,false,true] l) (word [false,false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact ((path_of h0).trans (path_of h1)).trans (path_of h2)
  | m41 =>
    have h0 : run .m41 12 (cfg .A (word [true,false,true,false,false,false] l) (word [false,false,true] z)) = some (cfg .A (word [false,false] l) (word [false,false,true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h1 : run .m41 12 (cfg .A (word [false,false] l) (word [false,false,true,true,true,true,true] z)) = some (cfg .B (word [false,false,false,false,false,true,false,true] l) (word [true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h2 : run .m41 3 (cfg .B (word [false,false,false,false,false,true,false,true] l) (word [true] z)) = some (cfg .A (word [false,false,false,false,true,false,true] l) (word [false,false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact ((path_of h0).trans (path_of h1)).trans (path_of h2)

theorem rootStart (v : Variant)  : Path v (cfg .A z z) (cfg .A (word [false,false,false,false,false,false,false,false,true,false,true] z) (word [false,false,true] z)) := by
  cases v with
  | m28 =>
    have h0 : run .m28 12 (cfg .A z z) = some (cfg .C (word [false,true] z) (word [false,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h1 : run .m28 12 (cfg .C (word [false,true] z) (word [false,true,true] z)) = some (cfg .D z (word [false,false,true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h2 : run .m28 12 (cfg .D z (word [false,false,true,true,true,true,true] z)) = some (cfg .B (word [true,false,false,false,true,false,true] z) (word [false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h3 : run .m28 12 (cfg .B (word [true,false,false,false,true,false,true] z) (word [false,true] z)) = some (cfg .C (word [true,false,true,false,true,false,true] z) (word [true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h4 : run .m28 12 (cfg .C (word [true,false,true,false,true,false,true] z) (word [true,true,true] z)) = some (cfg .B (word [false,false,true,false,true] z) (word [false,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h5 : run .m28 12 (cfg .B (word [false,false,true,false,true] z) (word [false,true,true,true,true] z)) = some (cfg .C (word [true] z) (word [true,true,true,true,true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h6 : run .m28 12 (cfg .C (word [true] z) (word [true,true,true,true,true,true,true,true,true] z)) = some (cfg .A (word [false,true] z) (word [false,true,true,true,true,true,true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h7 : run .m28 12 (cfg .A (word [false,true] z) (word [false,true,true,true,true,true,true,true,true,true,true] z)) = some (cfg .C (word [false,false,false,false,false,false,false,false,false,true,false,true] z) (word [false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h8 : run .m28 1 (cfg .C (word [false,false,false,false,false,false,false,false,false,true,false,true] z) (word [false,true] z)) = some (cfg .A (word [false,false,false,false,false,false,false,false,true,false,true] z) (word [false,false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact ((((((((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)).trans (path_of h4)).trans (path_of h5)).trans (path_of h6)).trans (path_of h7)).trans (path_of h8)
  | m41 =>
    have h0 : run .m41 12 (cfg .A z z) = some (cfg .C (word [false,true] z) (word [false,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h1 : run .m41 12 (cfg .C (word [false,true] z) (word [false,true,true] z)) = some (cfg .F (word [true] z) (word [false,false,true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h2 : run .m41 12 (cfg .F (word [true] z) (word [false,false,true,true,true,true,true] z)) = some (cfg .D (word [false,false,true,false,true] z) (word [false,false,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h3 : run .m41 12 (cfg .D (word [false,false,true,false,true] z) (word [false,false,true,true] z)) = some (cfg .B (word [false,false,true,false,true,false,true] z) (word [false,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h4 : run .m41 12 (cfg .B (word [false,false,true,false,true,false,true] z) (word [false,true,true] z)) = some (cfg .B (word [false,false,true] z) (word [false,true,true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h5 : run .m41 12 (cfg .B (word [false,false,true] z) (word [false,true,true,true,true,true,true] z)) = some (cfg .E z (word [false,false,false,true,true,true,true,true,true,true,true,true,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h6 : run .m41 12 (cfg .E z (word [false,false,false,true,true,true,true,true,true,true,true,true,true] z)) = some (cfg .B (word [false,false,false,false,false,false,false,false,false,true,false,true] z) (word [true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    have h7 : run .m41 3 (cfg .B (word [false,false,false,false,false,false,false,false,false,true,false,true] z) (word [true] z)) = some (cfg .A (word [false,false,false,false,false,false,false,false,true,false,true] z) (word [false,false,true] z)) := by
      simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
    exact (((((((path_of h0).trans (path_of h1)).trans (path_of h2)).trans (path_of h3)).trans (path_of h4)).trans (path_of h5)).trans (path_of h6)).trans (path_of h7)


theorem zadd (a b : Nat) (l : Stream) : Zeros (a+b) l = Zeros a (Zeros b l) := rep_add _ _ _ _
theorem oadd (a b : Nat) (l : Stream) : O (a+b) l = O a (O b l) := rep_add _ _ _ _
theorem padd (a b : Nat) (l : Stream) : P (a+b) l = P a (P b l) := rep_add _ _ _ _
theorem qadd (a b : Nat) (l : Stream) : Qp (a+b) l = Qp a (Qp b l) := rep_add _ _ _ _
theorem shiftQ (n : Nat) (l : Stream) : Qp n (push false l) = push false (P n l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change word [false,true] (Qp n (push false l)) = push false (word [true,false] (P n l))
    rw [ih]; rfl

theorem pSweep (v : Variant) (n : Nat) (l r : Stream) : Path v (A (P n l) (R 1 r)) (A l (R 1 (O (2*n) r))) := by
  induction n generalizing r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h := (popP v (P n l) r).trans (ih (O 2 r))
    rw [show 2*(n+1)=2*n+2 by omega,oadd]
    exact h

theorem bSweep (v : Variant) (n : Nat) (l r : Stream) : run v n (B l (O n r)) = some (B (Zeros n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add,oadd]
    change (run v 1 (B l (push true (O n r)))).bind (run v n) = _
    have h : run v 1 (B l (push true (O n r))) = some (B (push false l) (O n r)) := by
      simp [cfg,BB6.Agent13.Box33PrefixMacro.run,step,right]
    rw [h,Option.bind_some,ih]
    rw [show 1+n=n+1 by omega,zadd]
    rfl

theorem rightSweep (v : Variant) (n : Nat) (l r : Stream) : Path v (A l (push false (O (n+2) (push false r)))) (A (Zeros n (push true l)) (R 1 r)) := by
  have h0 : run v 1 (A l (push false (O (n+2) (push false r)))) = some (B (push true l) (O (n+2) (push false r))) := by
    simp [cfg,BB6.Agent13.Box33PrefixMacro.run,step,right]
  have h1 := bSweep v (n+2) (push true l) (push false r)
  have h2 : run v 2 (B (Zeros (n+2) (push true l)) (push false r)) = some (A (Zeros n (push true l)) (R 1 r)) := by
    rw [show n+2=2+n by omega,zadd]
    simp [cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  exact ((path_of h0).trans (path_of h1)).trans (path_of h2)

theorem consume (v : Variant) (s : Nat) (l r : Stream) : Path v (A (Zeros 2 l) (R (s+2) (push false r))) (A (Zeros (s+1) (I l)) (R 1 r)) := by
  have h0 := turn00 v l (O (s+1) (push false r))
  have h1 := rightSweep v (s+1) (word [false,true] l) r
  exact h0.trans h1

theorem qSweep0 (v : Variant) (n : Nat) (l r : Stream) : Path v (A (Qp n (push false l)) (Zeros 3 r)) (A (push false l) (Zeros 3 (P n r))) := by
  induction n generalizing r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h0 := qNext v (P n l) r
    have h1 := ih (word [true,false] r)
    rw [shiftQ n l] at h1
    have h := h0.trans h1
    rw [show P (n+1) r = P n (word [true,false] r) from padd n 1 r]
    change Path v (A (word [false,true] (Qp n (push false l))) (Zeros 3 r)) _
    rw [shiftQ n l]
    exact h

theorem qSweep (v : Variant) (n : Nat) (l r : Stream) : Path v (A (Qp (n+1) (push false l)) (R 1 r)) (A (push false l) (Zeros 3 (P n (O 2 r)))) := by
  have h0 := qFirst v (P n l) r
  have h1 := qSweep0 v n l (O 2 r)
  rw [shiftQ n l] at h1
  change Path v (A (word [false,true] (Qp n (push false l))) (R 1 r)) _
  rw [shiftQ n l]
  exact h0.trans h1

theorem enter (v : Variant) (i : Nat) (l r : Stream) : Path v (A (Qp (2*i+2) (Zeros 2 l)) (R 1 r)) (A (push true l) (R 3 (Qp (2*i) (push false (O 2 r))))) := by
  have h0 := qSweep v (2*i+1) (push false l) r
  have h1 := qTurn v l (P (2*i+1) (O 2 r))
  have h2 := qFlip v (word [false,true] l) (P (2*i+1) (O 2 r))
  have h3 := qExit v l (P (2*i+1) (O 2 r))
  have h := ((h0.trans h1).trans h2).trans h3
  have e : P (2*i+1) (O 2 r) = push true (Qp (2*i) (push false (O 2 r))) := by
    rw [shiftQ]
    rfl
  rw [e] at h
  exact h

def Base (v : Variant) (u : Stream) (d : Nat) (w : Stream) : Prop :=
  ∀ s r, Path v (A (push true u) (R (s+3) (push false r))) (A (Zeros (s+3+d) (I w)) (R 1 r))
def Transfer (v : Variant) (j : Nat) (u : Stream) (d : Nat) (w : Stream) : Prop :=
  ∀ r, Path v (A (push true (Zeros (3*j) u)) (R 3 (Qp (2*j) (push false r))))
    (A (Zeros 3 (P (2*j) (Zeros (3*j+d) (I w)))) (R 1 r))

theorem baseGeneric (v : Variant) (w : Stream) : Base v (Zeros 3 w) 1 w := by
  intro s r
  have h0 := popP v (Zeros 2 w) (O (s+2) (push false r))
  have h1 := consume v (s+3) w r
  have e : O 3 (O (s+2) (push false r)) = O ((s+3)+2) (push false r) := by
    rw [←oadd]; congr 1; omega
  change Path v (A (push true (Zeros 3 w)) (R 1 (O (s+2) (push false r)))) (A (Zeros 2 w) (word [false,false] (O 3 (O (s+2) (push false r))))) at h0
  rw [e] at h0
  have h := h0.trans h1
  change Path v (A (push true (Zeros 3 w)) (word [false,false] (O 1 (O (s+2) (push false r))))) _ at h
  rw [←oadd,show 1+(s+2)=s+3 by omega] at h
  exact h

theorem basePrepend (v : Variant) (u : Stream) (d : Nat) (w : Stream) (h : Base v u d w) : Base v (I u) (d+3) w := by
  intro s r
  have h0 := pop110 v (push true u) (O (s+2) (push false r))
  change Path v (A (push true (I u)) (word [false,false] (O 1 (O (s+2) (push false r))))) (A (push true u) (word [false,false] (O 4 (O (s+2) (push false r))))) at h0
  rw [←oadd,←oadd,show 1+(s+2)=s+3 by omega,show 4+(s+2)=(s+3)+3 by omega] at h0
  have h1 := h (s+3) r
  have hh := h0.trans h1
  rw [show s+3+3+d=s+3+(d+3) by omega] at hh
  exact hh

theorem baseSpecial (v : Variant) : Base v (push false (I z)) 5 z := by
  intro s r
  have h0 := pSweep v 3 (Zeros 2 z) (O (s+2) (push false r))
  have h1 := consume v (s+7) z r
  have e : O 6 (O (s+2) (push false r)) = O (s+8) (push false r) := by rw [←oadd]; congr 1; omega
  change Path v (A (P 3 (Zeros 2 z)) (R 1 (O (s+2) (push false r)))) (A (Zeros 2 z) (R 1 (O 6 (O (s+2) (push false r))))) at h0
  rw [e] at h0
  have e2 : R 1 (O (s+8) (push false r)) = R (s+7+2) (push false r) := by
    change word [false,false] (O 1 (O (s+8) (push false r))) = word [false,false] (O (s+7+2) (push false r))
    rw [←oadd,show 1+(s+8)=s+7+2 by omega]
  rw [e2] at h0
  have h := h0.trans h1
  have el : P 3 (Zeros 2 z) = push true (push false (I z)) := by simp [P,Zeros,I,rep,word]
  rw [el] at h
  change Path v (A (push true (push false (I z))) (word [false,false] (O 1 (O (s+2) (push false r))))) _ at h
  rw [←oadd,show 1+(s+2)=s+3 by omega,show s+7+1=s+3+5 by omega] at h
  exact h

def Acc (i k : Nat) (u r : Stream) : Config :=
  A (Zeros 3 (P (2*i) (Zeros (3*i+1) (I (Zeros (3*k) u)))))
    (R 2 (Qp (2*k+1) (push false r)))

theorem accStep (v : Variant) (i k : Nat) (u r : Stream) (d : Nat) (w : Stream)
    (ht : Transfer v i (I (Zeros (3*k) u)) d w) :
    Path v (Acc i k u r) (A (Zeros 3 (P (2*(i+1)) (Zeros (3*i+d) (I w)))) (R 1 (P (2*k) r))) := by
  let tail := I (Zeros (3*k) u)
  let u0 := Zeros (3*i+1) tail
  let right := P (2*k+1) r
  have h0 := consume v 0 (push false (P (2*i) u0)) right
  have el : Zeros 1 (I (push false (P (2*i) u0))) = Qp (2*i+2) (Zeros 2 (Zeros (3*i) tail)) := by
    rw [show 2*i+2=2+2*i by omega,qadd]
    change Zeros 1 (I (push false (P (2*i) u0))) = Qp 2 (Qp (2*i) (push false (Zeros (3*i+1) tail)))
    rw [shiftQ]
    rfl
  rw [el] at h0
  have h1 := enter v i (Zeros (3*i) tail) right
  have er : right = push true (Qp (2*k) (push false r)) := by
    unfold right
    rw [shiftQ]
    rfl
  rw [er] at h1
  have h2 := ht (O 3 (Qp (2*k) (push false r)))
  have h3 := h1.trans h2
  have h4 := consume v 2 (push false (P (2*i) (Zeros (3*i+d) (I w)))) (P (2*k) r)
  have hr : R 1 (O 3 (Qp (2*k) (push false r))) = R 4 (push false (P (2*k) r)) := by rw [shiftQ]; rfl
  rw [hr] at h3
  have hh := h3.trans h4
  rw [show 2*(i+1)=2+2*i by omega,padd]
  have hh' : Path v (A (Qp (2*i+2) (Zeros 2 (Zeros (3*i) tail))) (R 1 right))
      (A (Zeros 3 (P 2 (P (2*i) (Zeros (3*i+d) (I w))))) (R 1 (P (2*k) r))) := by
    rw [er]
    exact hh
  have ha : Path v (Acc i k u r) (A (Qp (2*i+2) (Zeros 2 (Zeros (3*i) tail))) (R 1 right)) := by
    unfold Acc
    rw [shiftQ]
    exact h0
  exact ha.trans hh'

theorem accLoop (v : Variant) (i k : Nat) (u : Stream) (d : Nat) (w : Stream) (hb : Base v u d w)
    (small : ∀ j, j < i+k+1 → ∀ u' d' w', Base v u' d' w' → Transfer v j u' d' w') (r : Stream) :
    Path v (Acc i k u r) (A (Zeros 3 (P (2*(i+k+1)) (Zeros (3*(i+k+1)+d) (I w)))) (R 1 r)) := by
  induction k generalizing i with
  | zero =>
    have hs := small i (by omega) (I u) (d+3) w (basePrepend v u d w hb)
    have h := accStep v i 0 u r (d+3) w hs
    rw [show i+0+1=i+1 by omega,show 3*(i+1)+d=3*i+(d+3) by omega]
    exact h
  | succ k ih =>
    have hg := baseGeneric v (Zeros (3*k) u)
    have he : Zeros (3*(k+1)) u = Zeros 3 (Zeros (3*k) u) := by rw [show 3*(k+1)=3+3*k by omega,zadd]
    have hp := basePrepend v (Zeros 3 (Zeros (3*k) u)) 1 (Zeros (3*k) u) hg
    rw [←he] at hp
    have hs := small i (by omega) _ _ _ hp
    have h := accStep v i (k+1) u r 4 (Zeros (3*k) u) hs
    have h' : Path v (Acc i (k+1) u r) (Acc (i+1) k u r) := by
      unfold Acc
      rw [show 3*(i+1)+1=3*i+4 by omega]
      have hr : R 2 (Qp (2*k+1) (push false r)) = R 1 (P (2*(k+1)) r) := by
        rw [shiftQ]
        rw [show 2*(k+1)=2*k+1+1 by omega]
        rfl
      rw [hr]
      exact h
    have h'' := ih (i+1) (fun j hj => small j (by omega))
    rw [show i+1+k+1=i+(k+1)+1 by omega] at h''
    exact h'.trans h''

theorem transfer (v : Variant) (j : Nat) (u : Stream) (d : Nat) (w : Stream) (hb : Base v u d w) : Transfer v j u d w := by
  induction j using Nat.strongRecOn generalizing u d w with
  | ind j ih =>
    cases j with
    | zero =>
      intro r
      have h := hb 0 r
      rw [show 3+d=3+d by rfl,zadd] at h
      simpa only [Nat.mul_zero,Nat.zero_add,rep_zero] using h
    | succ j =>
      intro r
      have h0 := popP v (Zeros 2 (Zeros (3*j) u)) (O 2 (Qp (2*(j+1)) (push false r)))
      have h1 := consume v 3 (Zeros (3*j) u) (P (2*(j+1)) r)
      have hr : Qp (2*(j+1)) (push false r) = push false (P (2*(j+1)) r) := shiftQ _ _
      rw [hr] at h0
      have h := h0.trans h1
      have h' : Path v (A (push true (Zeros (3*(j+1)) u)) (R 3 (Qp (2*(j+1)) (push false r)))) (Acc 0 j u r) := by
        unfold Acc
        rw [show 3*(j+1)=3+3*j by omega,zadd]
        rw [hr]
        have he : R 2 (Qp (2*j+1) (push false r)) = R 1 (P (2*(j+1)) r) := by
          rw [shiftQ]
          rw [show 2*(j+1)=2*j+1+1 by omega]
          rfl
        rw [he]
        exact h
      have h'' := accLoop v 0 j u d w hb (fun n hn u' d' w' hb' => ih n (by omega) u' d' w' hb') r
      exact h'.trans (by simpa only [Nat.zero_add] using h'')

def Root (n : Nat) : Config := A (Zeros 6 (P (2*n) (Zeros (3*n+2) (I z)))) R0

theorem root0Exact (v : Variant) (l : Stream) : run v 11 (A (Zeros 2 l) R0) = some (A (I l) R0) := by
  cases v <;> simp [cfg,word,Zeros,R0,R,O,I,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem epoch (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run v t (Root n) = some (Root (n+1)) := by
  let u := Zeros (3*n+2) (I z)
  let l := P (2*n) u
  have h0 := root0Exact v (Zeros 4 l)
  have h1 := root1 v (push false l)
  have h2 := root0 v (Zeros 2 (P (2*n+2) u))
  have h12 : Path v (A (I (Zeros 4 l)) R0) (A (I (Zeros 2 (P (2*n+2) u))) R0) := by
    have e : P (2*n+2) u = P 2 l := by
      unfold l
      rw [show 2*n+2=2+2*n by omega,padd]
    rw [e] at h2 ⊢
    exact h1.trans h2
  have h3 := pSweep v 2 (push false (P (2*n+2) u)) z
  have h4 := enter v n (Zeros (3*n) (push false (I z))) (O 4 z)
  have h3' : Path v (A (I (Zeros 2 (P (2*n+2) u))) R0)
      (A (Qp (2*n+2) (Zeros 2 (Zeros (3*n) (push false (I z))))) (R 1 (O 4 z))) := by
    have e : Zeros 2 (Zeros (3*n) (push false (I z))) = push false u := by
      unfold u
      change Zeros 2 (Zeros (3*n) (Zeros 1 (I z))) = Zeros 1 (Zeros (3*n+2) (I z))
      rw [←zadd,←zadd,←zadd]
      congr 1
      omega
    rw [e,shiftQ]
    exact h3
  have h5 := transfer v n (push false (I z)) 5 z (baseSpecial v) (O 6 z)
  have h4' : Path v (A (Qp (2*n+2) (Zeros 2 (Zeros (3*n) (push false (I z))))) (R 1 (O 4 z)))
      (A (push true (Zeros (3*n) (push false (I z)))) (R 3 (Qp (2*n) (push false (O 6 z))))) := by
    rw [←show O 2 (O 4 z)=O 6 z from (oadd 2 4 z).symm]
    exact h4
  have h6 := consume v 5 (push false (P (2*n) (Zeros (3*n+5) (I z)))) z
  have hr : R 1 (O 6 z) = R 7 (push false z) := by simp
  rw [hr] at h5
  have h6' : Path v (A (Zeros 3 (P (2*n) (Zeros (3*n+5) (I z)))) (R 7 (push false z))) (Root (n+1)) := by
    unfold Root
    rw [show 2*(n+1)=2+2*n by omega,padd,show 3*(n+1)+2=3*n+5 by omega]
    exact h6
  obtain ⟨s,hs⟩ := (((h12.trans h3').trans h4').trans h5).trans h6'
  exact ⟨11+s,by omega,by unfold Root; change run v (11+s) (A (Zeros 2 (Zeros 4 l)) R0) = _; rw [run_add,h0,Option.bind_some,hs]; rfl⟩

theorem neverPhase (v : Variant) (t n : Nat) : run v t (Root n) ≠ none := by
  induction t using Nat.strongRecOn generalizing n with
  | ind t ih =>
    intro h
    obtain ⟨s,hp,he⟩ := epoch v n
    by_cases ht : t≤s
    · rw [←show t+(s-t)=s by omega,run_add,h] at he
      contradiction
    · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ h

theorem neverBlank (v : Variant) (t : Nat) : run v t (A z z) ≠ none := by
  have h : Path v (A z z) (Root 0) := rootStart v
  obtain ⟨s,hs⟩ := h
  intro ht
  by_cases hle : t≤s
  · rw [←show t+(s-t)=s by omega,run_add,ht] at hs
    contradiction
  · rw [←show s+(t-s)=t by omega,run_add,hs,Option.bind_some] at ht
    exact neverPhase v _ 0 ht
open BB6Coverage
open Box17 (index decode)
def codes : Variant → List (Fin 25)
  | .m28 => [8,6,11,6,1,13,17,12,24,21,2,0]
  | .m41 => [8,6,11,6,1,13,17,6,24,21,2,0]
def table (v : Variant) : Machine := fun s => decode ((codes v).getD (index s).val 0)
theorem project_step (v : Variant) (c : BB6Coverage.Config) :
    (rawStep (table v) c).map BB6.Agent13.Box33PrefixMacro.project = step v (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases v <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never (v : Variant) : NeverHalts (table v) := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever (table v) (step v) (project_step v)
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank v n
def partialTable (v : Variant) : PartialMachine := fun s => some (table v s)
theorem compatible_never (v : Variant) (m : Machine) (hm : compatible (partialTable v) m) : NeverHalts m := by
  have he : m = table v := funext fun s => hm s _ rfl
  rw [he]
  exact never v
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V24Pair28
