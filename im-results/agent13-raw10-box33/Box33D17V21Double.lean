import Box33D14Growth

namespace BB6.Agent13.Box33D17V21Double
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def step (b : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .A true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .B false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .B true c)
  | .E,false => some (left .F false c)
  | .E,true => none
  | .F,false => some (right .F true c)
  | .F,true => some (if b then left .A true c else right .A true c)

def run (b : Bool) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step b c).bind (run b n)

theorem run_add (b : Bool) (m n : Nat) (c : Config) :
    run b (m+n) c = (run b m c).bind (run b n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step b c <;> simp [ih]

theorem chain (b : Bool) {n m : Nat} {c d e : Config}
    (h : run b n c = some d) (j : run b m d = some e) :
    run b (n+m) c = some e := by
  rw [run_add,h,Option.bind_some,j]

abbrev zeros := rep [false]
abbrev A (l r : Stream) := cfg .A l r
abbrev B (l r : Stream) := cfg .B l r
abbrev L (l r : Stream) := A l (zeros 2 r)
def extra (b : Bool) : Nat := if b then 2 else 0
theorem ones_add (m n : Nat) (s : Stream) : ones (m+n) s = ones m (ones n s) := rep_add _ _ _ _
theorem zeros_add (m n : Nat) (s : Stream) : zeros (m+n) s = zeros m (zeros n s) := rep_add _ _ _ _
@[simp] theorem zeros_z (n : Nat) : zeros n z = z := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeros,rep,word,ih]

theorem lstep (b : Bool) (l r : Stream) :
    run b 8 (L (ones 2 l) r) = some (L l (ones 2 r)) := by
  cases b <;> simp [L,A,cfg,run,step,left,right,ones,zeros,rep,word]

theorem lsweep (b : Bool) (n : Nat) (l r : Stream) :
    run b (8*n) (L (ones (2*n) l) r) = some (L l (ones (2*n) r)) := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    rw [show 8*(n+1)=8+8*n by omega,show 2*(n+1)=2+2*n by omega,
      ones_add 2 (2*n) l,run_add,lstep,Option.bind_some,ih]
    rw [show 2+2*n=2*n+2 by omega,ones_add (2*n) 2 r]

theorem lsweepBlank (b : Bool) (n : Nat) (l : Stream) :
    run b (8*n) (A (ones (2*n) l) z) = some (L l (ones (2*n) z)) := by
  simpa only [L,zeros_z] using lsweep b n l z

theorem odd (b : Bool) (l r : Stream) :
    run b 6 (L (ones 1 (zeros 3 l)) r) = some (L l (word [true,true,false,true] r)) := by
  cases b <;> simp [L,A,cfg,run,step,left,right,ones,zeros,rep,word]

theorem turn3 (b : Bool) (l r : Stream) :
    run b (10+extra b) (L (zeros 3 l) r) = some (A (ones 5 l) r) := by
  cases b <;> simp [extra,L,A,cfg,run,step,left,right,ones,zeros,rep,word]

theorem turnBlank (b : Bool) (r : Stream) :
    run b (10+extra b) (L z r) = some (A (ones 5 z) r) := by
  simpa only [zeros_z] using turn3 b z r

theorem turn2 (b : Bool) (l r : Stream) :
    run b (6+extra b) (L (zeros 2 (ones 1 l)) r) =
    some (A (ones 1 l) (word [false,false,false,true] r)) := by
  cases b <;> simp [extra,L,A,cfg,run,step,left,right,ones,zeros,rep,word]

theorem astep (b : Bool) (l r : Stream) :
    run b 1 (A l (ones 1 r)) = some (A (ones 1 l) r) := by
  cases b <;> simp [A,cfg,run,step,right,ones,rep,word]

theorem asweep (b : Bool) (n : Nat) (l r : Stream) :
    run b n (A l (ones n r)) = some (A (ones n l) r) := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1=1+n by omega,ones_add 1 n r,run_add,astep,Option.bind_some,ih]
    rw [show 1+n=n+1 by omega,ones_add n 1 l]

theorem bstep (b : Bool) (l r : Stream) :
    run b 1 (B l (ones 1 r)) = some (B (zeros 1 l) r) := by
  cases b <;> simp [B,cfg,run,step,right,ones,zeros,rep,word]

theorem bsweep (b : Bool) (n : Nat) (l r : Stream) :
    run b n (B l (ones n r)) = some (B (zeros n l) r) := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1=1+n by omega,ones_add 1 n r,run_add,bstep,Option.bind_some,ih]
    rw [show 1+n=n+1 by omega,zeros_add n 1 l]

theorem enterB (b : Bool) (l r : Stream) :
    run b 1 (A l (zeros 1 r)) = some (B (ones 1 l) r) := by
  cases b <;> simp [A,B,cfg,run,step,right,ones,zeros,rep,word]

theorem exitB (b : Bool) (l r : Stream) :
    run b 2 (B (zeros 2 l) (zeros 1 r)) = some (L l (ones 1 r)) := by
  cases b <;> simp [L,A,B,cfg,run,step,left,right,ones,zeros,rep,word]

def phase (n : Nat) : Config := A (ones 11 (zeros 3 (ones (2*n) z))) z

theorem growth (b : Bool) (n : Nat) :
    run b (10*n+123+3*extra b) (phase n) = some (phase (n+4)) := by
  have h0 : run b 40 (phase n) =
      some (L (ones 1 (zeros 3 (ones (2*n) z))) (ones 10 z)) :=
    lsweepBlank b 5 _
  have h1 := chain b h0 (odd b (ones (2*n) z) (ones 10 z))
  have h2 := chain b h1 (lsweep b n z (ones 2 (zeros 1 (ones 11 z))))
  have h3 := chain b h2 (turnBlank b (ones (2*n) (ones 2 (zeros 1 (ones 11 z)))))
  have ha : run b (2*n+2) (A (ones 5 z) (ones (2*n) (ones 2 (zeros 1 (ones 11 z))))) =
      some (A (ones (2*n+2) (ones 5 z)) (zeros 1 (ones 11 z))) := by
    rw [←ones_add (2*n) 2 (zeros 1 (ones 11 z))]
    exact asweep b (2*n+2) _ _
  let s := ones 1 (ones (2*n+2) (ones 5 z))
  have h4 := chain b h3 ha
  have h5 := chain b h4 (enterB b _ (ones 11 z))
  have h6 := chain b h5 (bsweep b 11 s z)
  have hx : run b 2 (B (zeros 11 s) z) = some (L (zeros 9 s) (ones 1 z)) := by
    simpa only [zeros_z] using exitB b (zeros 9 s) z
  have h7 := chain b h6 hx
  have h8 := chain b h7 (turn3 b (zeros 6 s) (ones 1 z))
  have h9 := chain b h8 (asweep b 1 (ones 5 (zeros 6 s)) z)
  have h10 := chain b h9 (lsweepBlank b 3 (zeros 6 s))
  have h11 := chain b h10 (turn3 b (zeros 3 s) (ones 6 z))
  have h12 := chain b h11 (asweep b 6 (ones 5 (zeros 3 s)) z)
  have hs : s = ones (2*(n+4)) z := by
    dsimp [s]
    rw [←ones_add (2*n+2) 5 z,←ones_add 1 (2*n+2+5) z]
    congr 1
    omega
  have ht : 40+6+8*n+(10+extra b)+(2*n+2)+1+11+2+(10+extra b)+1+8*3+(10+extra b)+6 =
      10*n+123+3*extra b := by omega
  rw [ht] at h12
  rw [hs] at h12
  exact h12

theorem never_phase (b : Bool) (n k : Nat) : run b n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    let t := 10*k+123+3*extra b
    by_cases hn : n ≤ t
    · have he := growth b k
      change run b t (phase k) = _ at he
      rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,growth,Option.bind_some] at h
      exact ih _ (by dsimp [t] at *; omega) (k+4) h

#print axioms never_phase
end BB6.Agent13.Box33D17V21Double
