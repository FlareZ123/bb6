import DRegularShift

namespace BB6.DRegularFast
open DRegular BB6.DRegularShift

/-- Canonical representative of the input modulo `3^k`, preserving q and b. -/
def baseState (s : L) (k : Nat) : L :=
  {s with a := 2 + (s.a - 2) % 3^k}

/-- Quotient in the decomposition `s.a = baseState.a + 3^k * liftParam`. -/
def liftParam (s : L) (k : Nat) : Nat :=
  (s.a - 2) / 3^k

theorem base_canon (s : L) (k : Nat) (hs : Canon s) :
    Canon (baseState s k) := by
  rcases hs with ⟨ha,hq⟩
  constructor
  · simp [baseState]
  · simpa [baseState] using hq

theorem input_decomposition (s : L) (k : Nat) (hs : 2 ≤ s.a) :
    s = shiftNat (baseState s k) (3^k * liftParam s k) := by
  cases s with
  | mk a q b =>
    change 2 ≤ a at hs
    have hmod : (a-2) % 3^k + 3^k*((a-2)/3^k) = a-2 :=
      Nat.mod_add_div (a-2) (3^k)
    simp [baseState,liftParam,shiftNat]
    omega

theorem run_add (m n : Nat) : ∀ s : L,
    run (m+n) s = (run m s).bind (run n) := by
  induction m with
  | zero =>
    intro s
    simp [run]
  | succ m ih =>
    have hfun : run (m+n) = fun u => (run m u).bind (run n) := by
      funext u
      exact ih u
    intro s
    simp only [Nat.succ_add, run]
    simp [hfun, Option.bind_assoc]

theorem run_canon (n : Nat) : ∀ (s t : L), Canon s →
    run n s = some t → Canon t := by
  induction n with
  | zero =>
    intro s t hs hr
    simp [run] at hr
    cases hr
    exact hs
  | succ n ih =>
    intro s t hs hr
    cases hn : next s with
    | none => simp [run,hn] at hr
    | some u =>
      have hu : Canon u := next_canon s u hs hn
      have hrun : run n u = some t := by simpa [run,hn] using hr
      exact ih u t hu hrun

/-- One 3-adic block: evaluate the small residue representative and lift
    the result by the exact `8^k` offset. -/
theorem run_block (s : L) (k : Nat) (hs : Canon s) :
    run k s =
      (run k (baseState s k)).map
        (fun t => shiftNat t (8^k * liftParam s k)) := by
  have hdec := input_decomposition s k hs.1
  calc
    run k s = run k (shiftNat (baseState s k) (3^k*liftParam s k)) :=
      congrArg (fun x => run k x) hdec
    _ = (run k (baseState s k)).map
          (fun t => shiftNat t (8^k*liftParam s k)) := by
      simpa using (run_shift k (baseState s k) (liftParam s k)
        (base_canon s k hs))

/-- Number of regular sections computed in each residue-reduced block. -/
def blockSize : Nat := 512

/-- Run `n` full blocks, reducing the current unary parameter modulo
    `3^blockSize` before each block. -/
def fastRunBlocks : Nat → L → Option L
  | 0, s => some s
  | n+1, s =>
    match run blockSize (baseState s blockSize) with
    | none => none
    | some t => fastRunBlocks n (shiftNat t (8^blockSize * liftParam s blockSize))

theorem fastRunBlocks_correct (n : Nat) :
    ∀ (s : L), Canon s →
      run (blockSize*n) s = fastRunBlocks n s := by
  induction n with
  | zero =>
    intro s hs
    simp [fastRunBlocks,run]
  | succ n ih =>
    intro s hs
    let base := baseState s blockSize
    let p := liftParam s blockSize
    have hmul : blockSize*(n+1) = blockSize + blockSize*n := by
      calc
        blockSize*(n+1) = 512*n+512 := by simp [blockSize, Nat.mul_add]
        _ = 512+512*n := by omega
    have hblock := run_block s blockSize hs
    rw [hmul,run_add,hblock]
    cases hr : run blockSize base with
    | none =>
      simp [fastRunBlocks,base,hr]
    | some t =>
      let t' := shiftNat t (8^blockSize*p)
      have hb : run blockSize s = some t' := by
        rw [hblock,hr]
        rfl
      have ht' : Canon t' := run_canon blockSize s t' hs hb
      have hright : fastRunBlocks (n+1) s = fastRunBlocks n t' := by
        simp [fastRunBlocks,base,p,hr,t']
      rw [hright]
      simpa [t'] using (ih t' ht')

/-- Exact arbitrary-length evaluator: full residue-reduced blocks followed
    by the final remainder. -/
def fastRun (n : Nat) (s : L) : Option L :=
  (fastRunBlocks (n / blockSize) s).bind (run (n % blockSize))

theorem fastRun_correct (n : Nat) (s : L) (hs : Canon s) :
    run n s = fastRun n s := by
  have hdiv : n = blockSize*(n/blockSize)+n%blockSize := by
    calc
      n = n%blockSize + blockSize*(n/blockSize) :=
        (Nat.mod_add_div n blockSize).symm
      _ = blockSize*(n/blockSize)+n%blockSize := Nat.add_comm _ _
  calc
    run n s = run (blockSize*(n/blockSize)+n%blockSize) s :=
      congrArg (fun m => run m s) hdiv
    _ = (run (blockSize*(n/blockSize)) s).bind (run (n%blockSize)) :=
      run_add (blockSize*(n/blockSize)) (n%blockSize) s
    _ = (fastRunBlocks (n/blockSize) s).bind (run (n%blockSize)) := by
      rw [fastRunBlocks_correct (n/blockSize) s hs]
    _ = fastRun n s := rfl

end BB6.DRegularFast
