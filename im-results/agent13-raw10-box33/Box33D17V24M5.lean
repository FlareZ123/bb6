import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V24M5
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .A true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => none
  | .E,false => some (right .F true c)
  | .E,true => some (left .D false c)
  | .F,false => some (right .B false c)
  | .F,true => some (left .E false c)
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
abbrev D := cfg .D
abbrev F := cfg .F
abbrev p := rep [true,false]
abbrev q := rep [false,true]
abbrev zeros := rep [false]
abbrev ones := rep [true]
abbrev R (r : Stream) := word [false,false,true] r
abbrev B (n : Nat) (r : Stream) := push false (ones (2*n+1) (push false (ones (2*n+1) r)))
def T (k : Nat) (u : Stream) := q (k+1) (word [false,false,false] (p k (word [true,true] u)))
def S (n : Nat) (u : Stream) := word [false,false,true,true] (q n (zeros 2 u))
def Path (c d : Config) : Prop := ∃ t, run t c = some d
theorem path_of {c d : Config} {t : Nat} (h : run t c = some d) : Path c d := ⟨t,h⟩
theorem Path.trans {a b c : Config} (h : Path a b) (g : Path b c) : Path a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨s,hs⟩ := g
  exact ⟨t+s,by rw [run_add,ht,Option.bind_some,hs]⟩
theorem shiftQ (n : Nat) (u : Stream) : q n (push false u) = push false (p n u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change push false (push true (q n (push false u))) = _
    rw [ih]; rfl
theorem shiftP (n : Nat) (u : Stream) : p n (push true u) = push true (q n u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change push true (push false (p n (push true u))) = _
    rw [ih]; rfl

theorem start (l r : Stream) : run 3 (A (push false l) (R r)) = some (D l (word [false,false,true,true] r)) := by
  simp [A,D,cfg,R,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem dOne (l r : Stream) : run 2 (D (p 1 l) (zeros 2 r)) = some (D l (zeros 2 (zeros 2 r))) := by
  simp [D,cfg,p,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem dSweep (n : Nat) (l r : Stream) : run (2*n) (D (p n l) (zeros 2 r)) = some (D l (zeros 2 (zeros (2*n) r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,run_add]
    change (run 2 (D (p 1 (p n l)) (zeros 2 r))).bind _ = _
    rw [dOne,Option.bind_some,ih,show 2+2*n=2*n+2 by omega,show zeros (2*n+2) r = zeros (2*n) (zeros 2 r) from rep_add _ _ _ _]
theorem dExit (l r : Stream) : run 5 (D (zeros 2 l) (zeros 2 r)) = some (A (push false l) (word [true,false,true] r)) := by
  simp [A,D,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aPop0 (l r : Stream) : run 1 (A (push false l) (push true r)) = some (A l (word [false,true] r)) := by
  simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aPop1 (l r : Stream) : run 1 (A (push true l) (push true r)) = some (A l (ones 2 r)) := by
  simp [A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aPop11 (l r : Stream) : run 2 (A (ones 2 l) (push true r)) = some (A l (ones 3 r)) := by
  simp [A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aPop10 (l r : Stream) : run 2 (A (p 1 l) (push true r)) = some (A l (push false (ones 2 r))) := by
  simp [A,cfg,p,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aPop110 (l r : Stream) : run 3 (A (word [true,true,false] l) (push true r)) = some (A l (push false (ones 3 r))) := by
  simp [A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aPop111 (l r : Stream) : run 3 (A (ones 3 l) (push true r)) = some (A l (ones 4 r)) := by
  simp [A,cfg,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem simpleRestore (l r : Stream) : run 7 (A l (word [false,true,false,true,false,false] r)) = some (A (word [false,false,true] l) (R r)) := by
  simp [A,cfg,R,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem emit (l r : Stream) : run 8 (A (word [false,false,true] l) (R r)) = some (A (push true l) (word [true,false,true,true,true] r)) := by
  simp [A,cfg,R,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem prep (k : Nat) (l r : Stream) : Path (A (q (k+1) (word [false,false,false] l)) (R r)) (A (push true l) (word [true,false,true,true,true] (zeros (2*k) (ones 2 r)))) := by
  have hstart : run 3 (A (q (k+1) (word [false,false,false] l)) (R r)) = some (D (p (k+1) (zeros 2 l)) (zeros 2 (ones 2 r))) := by
    rw [show q (k+1) (word [false,false,false] l) = push false (p (k+1) (zeros 2 l)) from shiftQ (k+1) (zeros 2 l)]
    exact start _ _
  have h1 := (path_of hstart).trans (path_of (dSweep (k+1) (zeros 2 l) (ones 2 r)))
  have h2 := h1.trans (path_of (dExit l (zeros (2*(k+1)) (ones 2 r))))
  have hz : zeros (2*(k+1)) (ones 2 r) = zeros 2 (zeros (2*k) (ones 2 r)) := by
    rw [show 2*(k+1)=2+2*k by omega]; exact rep_add _ _ _ _
  rw [hz] at h2
  have h3 := h2.trans (path_of (aPop0 l (word [false,true] (zeros 2 (zeros (2*k) (ones 2 r))))))
  have h4 := h3.trans (path_of (simpleRestore l (zeros (2*k) (ones 2 r))))
  exact h4.trans (path_of (emit l (zeros (2*k) (ones 2 r))))

theorem fStart (l r : Stream) : run 2 (A l (word [false,true] r)) = some (F (word [false,true] l) r) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fOne (l r : Stream) : run 4 (F (push false l) (ones 2 r)) = some (F (push false (q 1 l)) r) := by
  simp [F,cfg,q,ones,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fSweep (n : Nat) (l r : Stream) : run (4*n) (F (push false l) (ones (2*n) r)) = some (F (push false (q n l)) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 4*(n+1)=4+4*n by omega,show 2*(n+1)=2+2*n by omega,show ones (2+2*n) r = ones 2 (ones (2*n) r) from rep_add _ _ _ _,run_add,fOne,Option.bind_some,ih,show q (n+1) l = q n (q 1 l) from rep_add _ n 1 l]
theorem fBridge (l r : Stream) : run 2 (F l (word [false,true] r)) = some (F (zeros 2 l) r) := by
  simp [F,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fExit (l r : Stream) : run 3 (F (push false l) (zeros 2 r)) = some (A l (R r)) := by
  simp [A,F,cfg,R,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem restore (k : Nat) (l r : Stream) : Path (A l (B (k+1) (zeros 2 r))) (A (T k l) (R r)) := by
  have hs : run 2 (A l (B (k+1) (zeros 2 r))) = some (F (push false (push true l)) (ones (2*(k+1)) (push false (ones (2*(k+1)+1) (zeros 2 r))))) := by
    exact fStart _ _
  have h1 := (path_of hs).trans (path_of (fSweep (k+1) (push true l) (push false (ones (2*(k+1)+1) (zeros 2 r)))))
  have h2 := h1.trans (path_of (fBridge (push false (q (k+1) (push true l))) (ones (2*(k+1)) (zeros 2 r))))
  have h3 := h2.trans (path_of (fSweep (k+1) (zeros 2 (q (k+1) (push true l))) (zeros 2 r)))
  have h4 := h3.trans (path_of (fExit (q (k+1) (zeros 2 (q (k+1) (push true l)))) r))
  have he : zeros 2 (q (k+1) (push true l)) = word [false,false,false] (p k (word [true,true] l)) := by
    change zeros 2 (push false (push true (q k (push true l)))) = _
    rw [←shiftP k (push true l)]
    rfl
  rw [he] at h4
  exact h4

def out (k : Nat) (r : Stream) := ones (2*k+4) (push false (ones (2*k+5) r))
-- Nested traversal: every intermediate transfer has index strictly smaller than the outer transfer.
theorem chain (i j : Nat) (u r : Stream)
    (hsmall : ∀ a, a < i+j+1 → ∀ l r, Path (A (T a l) (R r)) (A l (out a r))) :
    Path (A (p j (ones 2 u)) (B (i+1) (zeros (2*(j+1)) (ones 2 r))))
      (A u (out (i+j+1) r)) := by
  induction j generalizing i with
  | zero =>
    have h := restore i (ones 2 u) (ones 2 r)
    have h1 := h.trans (hsmall i (by omega) (ones 2 u) (ones 2 r))
    have ha : out i (ones 2 r) = push true (ones (2*i+3) (push false (ones (2*i+5) (ones 2 r)))) := rfl
    rw [ha] at h1
    have h2 := h1.trans (path_of (aPop11 u (ones (2*i+3) (push false (ones (2*i+5) (ones 2 r))))))
    change Path _ (A u (ones (2*(i+0+1)+4) (push false (ones (2*(i+0+1)+5) r))))
    have hcount : ones (2*i+5) (ones 2 r) = ones (2*(i+0+1)+5) r := by
      rw [show 2*(i+0+1)+5=(2*i+5)+2 by omega]; exact (rep_add [true] _ _ _).symm
    rw [hcount] at h2
    change Path _ (A u (ones (2*i+3+3) (push false (ones (2*(i+0+1)+5) r)))) at h2
    rw [show 2*i+3+3=2*(i+0+1)+4 by omega] at h2
    exact h2
  | succ j ih =>
    have hz : zeros (2*(j+1+1)) (ones 2 r) = zeros 2 (zeros (2*(j+1)) (ones 2 r)) := by
      rw [show 2*(j+1+1)=2+2*(j+1) by omega]; exact rep_add _ _ _ _
    rw [hz]
    have h := restore i (p (j+1) (ones 2 u)) (zeros (2*(j+1)) (ones 2 r))
    have h1 := h.trans (hsmall i (by omega) _ _)
    change Path _ (A (p 1 (p j (ones 2 u))) (push true (ones (2*i+3) (push false (ones (2*i+5) (zeros (2*(j+1)) (ones 2 r))))))) at h1
    have h2 := h1.trans (path_of (aPop10 (p j (ones 2 u)) (ones (2*i+3) (push false (ones (2*i+5) (zeros (2*(j+1)) (ones 2 r)))))))
    have he : push false (ones 2 (ones (2*i+3) (push false (ones (2*i+5) (zeros (2*(j+1)) (ones 2 r)))))) = B ((i+1)+1) (zeros (2*(j+1)) (ones 2 r)) := by
      change push false (ones 2 (ones (2*i+3) (push false (ones (2*i+5) (zeros (2*(j+1)) (ones 2 r)))))) = push false (ones (2*((i+1)+1)+1) (push false (ones (2*((i+1)+1)+1) (zeros (2*(j+1)) (ones 2 r)))))
      rw [show 2*((i+1)+1)+1=2*i+5 by omega]
      rfl
    rw [he] at h2
    have h3 := h2.trans (ih (i+1) (fun a ha => hsmall a (by omega)))
    rw [show i+1+j+1=i+(j+1)+1 by omega] at h3
    exact h3

theorem transfer (k : Nat) (u r : Stream) : Path (A (T k u) (R r)) (A u (out k r)) := by
  induction k using Nat.strongRecOn generalizing u r with
  | ind k ih =>
    cases k with
    | zero =>
      have h := prep 0 (ones 2 u) r
      exact h.trans (path_of (aPop111 u (word [false,true,true,true,true,true] r)))
    | succ k =>
      have h := prep (k+1) (p (k+1) (ones 2 u)) r
      have h1 := h.trans (path_of (aPop110 (p k (ones 2 u)) (word [false,true,true,true] (zeros (2*(k+1)) (ones 2 r)))))
      change Path (A (T (k+1) u) (R r)) (A (p k (ones 2 u)) (B 1 (zeros (2*(k+1)) (ones 2 r)))) at h1
      have h2 := chain 0 k u r (fun a ha => ih a (by omega))
      simp only [Nat.zero_add] at h2
      exact h1.trans h2

theorem balance (k : Nat) (u : Stream) : Path (A (T k (p 1 u)) (R z)) (A (T (k+1) u) (R z)) := by
  have h := transfer k (p 1 u) z
  change Path _ (A (p 1 u) (push true (ones (2*k+3) (push false (ones (2*k+5) z))))) at h
  have h1 := h.trans (path_of (aPop10 u (ones (2*k+3) (push false (ones (2*k+5) z)))))
  have he : push false (ones 2 (ones (2*k+3) (push false (ones (2*k+5) z)))) = B (k+2) (zeros 2 z) := by
    have hz : zeros 2 z = z := by simp [zeros,rep,word]
    rw [hz]
    rfl
  rw [he] at h1
  exact h1.trans (restore (k+1) u z)

theorem fEvenExit (l r : Stream) : run 5 (F (push false l) (word [true,false] r)) = some (A l (word [true,false,true] r)) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fSecondStart (l r : Stream) : run 4 (A l (word [false,true,false,true] r)) = some (F (word [false,false,false,true] l) r) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fLast (l : Stream) : run 5 (F (push false l) (push true z)) = some (A l (word [true,false,true] z)) := by
  simp [A,F,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem finish (k : Nat) (u : Stream) : Path (A (T k (push false u)) (R z)) (A (S (k+1) (ones 2 (q k (push true u)))) (R z)) := by
  have h := transfer k (push false u) z
  change Path _ (A (push false u) (push true (ones (2*k+3) (push false (ones (2*k+5) z))))) at h
  have h1 := h.trans (path_of (aPop0 u (ones (2*k+3) (push false (ones (2*k+5) z)))))
  change Path _ (A u (word [false,true] (ones (2*k+3) (push false (ones (2*k+5) z))))) at h1
  have h2 := h1.trans (path_of (fStart u (ones (2*k+3) (push false (ones (2*k+5) z)))))
  rw [show 2*k+3=2*(k+1)+1 by omega] at h2
  rw [show ones (2*(k+1)+1) (push false (ones (2*k+5) z)) = ones (2*(k+1)) (push true (push false (ones (2*k+5) z))) from rep_add [true] _ _ _] at h2
  change Path _ (F (push false (push true u)) (ones (2*(k+1)) (word [true,false] (ones (2*k+5) z)))) at h2
  have h3 := h2.trans (path_of (fSweep (k+1) (push true u) (word [true,false] (ones (2*k+5) z))))
  have h4 := h3.trans (path_of (fEvenExit (q (k+1) (push true u)) (ones (2*k+5) z)))
  change Path _ (A (push false (push true (q k (push true u)))) (push true (push false (ones (2*k+6) z)))) at h4
  have h5 := h4.trans (path_of (aPop0 (push true (q k (push true u))) (push false (ones (2*k+6) z))))
  change Path _ (A (push true (q k (push true u))) (word [false,true,false,true] (ones (2*(k+2)+1) z))) at h5
  have h6 := h5.trans (path_of (fSecondStart (push true (q k (push true u))) (ones (2*(k+2)+1) z)))
  change Path _ (F (push false (word [false,false,true,true] (q k (push true u)))) (ones (2*(k+2)+1) z)) at h6
  have ho : ones (2*(k+2)+1) z = ones (2*(k+2)) (push true z) := rep_add _ _ _ _
  rw [ho] at h6
  have h7 := h6.trans (path_of (fSweep (k+2) (word [false,false,true,true] (q k (push true u))) (push true z)))
  have h8 := h7.trans (path_of (fLast (q (k+2) (word [false,false,true,true] (q k (push true u))))))
  change Path _ (A (push false (push true (q (k+1) (word [false,false,true,true] (q k (push true u)))))) (push true (word [false,true] z))) at h8
  have h9 := h8.trans (path_of (aPop0 (push true (q (k+1) (word [false,false,true,true] (q k (push true u))))) (word [false,true] z)))
  have hz : zeros 2 z = z := by simp [zeros,rep,word]
  have h10 := simpleRestore (push true (q (k+1) (word [false,false,true,true] (q k (push true u))))) z
  change run 7 (A _ (word [false,true,false,true] (zeros 2 z))) = _ at h10
  rw [hz] at h10
  exact h9.trans (path_of h10)

theorem beginEpoch (n : Nat) (u : Stream) : run 26 (A (S n u) (R z)) = some (A (T 0 (p n (push false u))) (R z)) := by
  rw [show 26=8+3+15 by decide,run_add (8+3) 15,run_add 8 3]
  change ((run 8 (A (word [false,false,true] (push true (q n (zeros 2 u)))) (R z))).bind (run 3)).bind _ = _
  rw [emit,Option.bind_some]
  have he : q n (zeros 2 u) = push false (p n (push false u)) := shiftQ n (push false u)
  rw [he]
  change (run 3 (A (word [true,true,false] (p n (push false u))) (push true (word [false,true,true,true] z)))).bind _ = _
  rw [aPop110,Option.bind_some]
  have h : run 15 (A (p n (push false u)) (B 1 (zeros 2 z))) = some (A (T 0 (p n (push false u))) (R z)) := by
    simp [A,cfg,B,T,p,q,ones,zeros,rep,word,R,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have hz : zeros 2 z = z := by simp [zeros,rep,word]
  rw [hz] at h
  exact h

theorem advance (k n : Nat) (u : Stream) : Path (A (T k (p n (push false u))) (R z)) (A (S (k+n+1) (ones 2 (q (k+n) (push true u)))) (R z)) := by
  induction n generalizing k with
  | zero => exact finish k u
  | succ n ih =>
    have h := balance k (p n (push false u))
    have h1 := h.trans (ih (k+1))
    rw [show k+1+n=k+(n+1) by omega] at h1
    exact h1

theorem progress (n : Nat) (u : Stream) : ∃ t u', 0<t ∧ run t (A (S n u) (R z)) = some (A (S (n+1) u') (R z)) := by
  obtain ⟨t,h⟩ := advance 0 n u
  exact ⟨26+t,ones 2 (q n (push true u)),by omega,by rw [run_add,beginEpoch,Option.bind_some]; simpa using h⟩
theorem neverPhase (t n : Nat) (u : Stream) : run t (A (S n u) (R z)) ≠ none := by
  induction t using Nat.strongRecOn generalizing n u with
  | ind t ih =>
    intro h
    obtain ⟨s,u',hs,he⟩ := progress n u
    by_cases ht : t≤s
    · rw [←show t+(s-t)=s by omega,run_add,h] at he
      contradiction
    · rw [←show s+(t-s)=t by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ _ h

theorem init : run 71 (A z z) = some (A (S 0 (word [false,true,true] z)) (R z)) := by
  let c10 := cfg .B (word [true] z) (word [true,false,true,true] z)
  let c20 := cfg .B (word [true,false,true] z) (word [true,false,true] z)
  let c26 := A (word [false,false,true,false,true] z) (R z)
  let c40 := cfg .F (word [true,true,true] z) (word [false,false,true,true,true] z)
  let c55 := cfg .E (word [false,false,false,true,true] z) (word [false,false,true,true] z)
  have h10 : run 10 (A z z) = some c10 := by
    simp [c10,A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h20 : run 10 c10 = some c20 := by
    simp [c10,c20,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h26 : run 6 c20 = some c26 := by
    simp [c20,c26,A,R,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h40 : run 14 c26 = some c40 := by
    simp [c26,c40,A,R,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h55 : run 15 c40 = some c55 := by
    simp [c40,c55,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  have h71 : run 16 c55 = some (A (S 0 (word [false,true,true] z)) (R z)) := by
    simp [c55,S,A,R,cfg,q,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
  rw [show 71=10+10+6+14+15+16 by decide,run_add (10+10+6+14+15) 16,run_add (10+10+6+14) 15,run_add (10+10+6) 14,run_add (10+10) 6,run_add 10 10,h10,Option.bind_some,h20,Option.bind_some,h26,Option.bind_some,h40,Option.bind_some,h55,Option.bind_some,h71]
theorem neverBlank (t : Nat) : run t (A z z) ≠ none := by
  intro h
  by_cases ht : t≤71
  · have he := init
    rw [←show t+(71-t)=71 by omega,run_add,h] at he
    contradiction
  · rw [←show 71+(t-71)=t by omega,run_add,init,Option.bind_some] at h
    exact neverPhase _ _ _ h
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,3,11,22,1,13,17,0,24,13,6,17]
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
end BB6.Agent13.Box33D17V24M5
