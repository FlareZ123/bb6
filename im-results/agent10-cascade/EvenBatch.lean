import ResetBlockCore
namespace CascadeResetShield

/-- Same-level even runs can be certified by the two endpoint equations and
    just the outer band inequalities. The intermediate states are recovered
    in the kernel by induction, with no individually checked witnesses. -/
theorem even_batch (k r h u d : Nat)
    (hstart : 4*2^k ≤ h+k+2)
    (hend : u≤8*2^k-3)
    (hd : h+2^r*d=8*2^k+k)
    (hu : u+d=8*2^k+k) : Path Edge h u := by
  induction r generalizing h with
  | zero =>
    simp only [Nat.pow_zero,Nat.one_mul] at hd
    have he : h=u := by omega
    subst u
    exact Path.refl _
  | succ r ih =>
    have hpow : 1≤2^r := Nat.one_le_pow r 2 (by decide)
    have hmul : d≤2^r*d := by
      simpa using Nat.mul_le_mul_right d hpow
    rw [Nat.pow_succ] at hd
    have hdouble : (2^r*2)*d = 2*(2^r*d) := by ac_rfl
    rw [hdouble] at hd
    let v := 8*2^k+k-2^r*d
    have hv : v+2^r*d=8*2^k+k := by dsimp [v]; omega
    have htwo : 2*v=8*2^k+h+k := by omega
    have hlo : 6*2^k-1≤v := by omega
    have hle : v≤u := by omega
    have hhi : v≤8*2^k-3 := by omega
    have he : Edge h v := Or.inl ⟨k,⟨hlo,hhi⟩,htwo⟩
    have hstart' : 4*2^k≤v+k+2 := by omega
    exact Path.step he (ih v hstart' hv)

/-- A positive length batch can be checked using a single power-of-two
    multiplication and the final deficit; all intermediate bounds follow. -/
def nextEvenBatch (h k r : Nat) : Option Nat :=
  let w := 8*2^k+k
  let d := (w-h)/2^r
  let u := w-d
  if 4*2^k≤h+k+2 ∧ u≤8*2^k-3 ∧ h+2^r*d=w ∧ u+d=w
  then some u else none

theorem nextEvenBatch_sound (h k r u : Nat)
    (hs : nextEvenBatch h k r=some u) : Path Edge h u := by
  unfold nextEvenBatch at hs
  dsimp only at hs
  split at hs
  · rename_i hc
    have he := Option.some.inj hs
    subst u
    exact even_batch _ _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  · contradiction

/-- One macro checks a whole even run, followed optionally by one reset.
    r=0 avoids checking an empty run's irrelevant endpoint constraints. -/
def nextMacro (h k r tCode : Nat) : Option Nat :=
  let v := if r=0 then some h else nextEvenBatch h k r
  match v with
  | none => none
  | some x => if tCode=0 then some x else nextAt x k (tCode-1)

theorem nextMacro_sound (h k r tCode u : Nat)
    (hs : nextMacro h k r tCode=some u) : Path Edge h u := by
  unfold nextMacro at hs
  dsimp only at hs
  have hv : ∀ x, (if r=0 then some h else nextEvenBatch h k r)=some x → Path Edge h x := by
    intro x hx
    split at hx
    · have he := Option.some.inj hx
      subst x
      exact Path.refl _
    · exact nextEvenBatch_sound _ _ _ _ hx
  split at hs
  · contradiction
  · rename_i x he
    have hp := hv x he
    split at hs
    · have hu := Option.some.inj hs
      subst u
      exact hp
    · exact path_trans hp (Path.step (nextAt_sound _ _ _ _ hs) (Path.refl _))

def runMacroBlock : Nat → List (Nat × Nat × Nat) → Option Nat
  | h, [] => some h
  | h, (k,r,tCode)::rest =>
    match nextMacro h k r tCode with
    | none => none
    | some u => runMacroBlock u rest

theorem runMacroBlock_sound (h u : Nat) (w : List (Nat × Nat × Nat))
    (hc : runMacroBlock h w = some u) : Path Edge h u := by
  induction w generalizing h with
  | nil =>
    simp [runMacroBlock] at hc
    subst u
    exact Path.refl _
  | cons a rest ih =>
    rcases a with ⟨k,r,tCode⟩
    cases he : nextMacro h k r tCode with
    | none => simp [runMacroBlock,he] at hc
    | some v =>
      have hs : runMacroBlock v rest=some u := by simpa [runMacroBlock,he] using hc
      exact path_trans (nextMacro_sound _ _ _ _ _ he) (ih _ hs)

/-- Shift-based implementation, definitionally reduced on arbitrary-size literals. -/
def nextAtFast (h k t : Nat) : Option Nat :=
  let p := 1 <<< k
  if (h+k)%2=0 then
    let u := 4*p+((h+k) >>> 1)
    if 6*p-1≤u ∧ u≤8*p-3 ∧ 2*u=8*p+h+k then some u else none
  else
    let d := (4*p+((h+k) >>> 1)+3) >>> t
    let u := (3^(t+1)*d-5) >>> 1
    let q := d <<< t
    if d%2=1 ∧ 6*p+1≤q ∧ q≤8*p-1 ∧
       2*u+5=3^(t+1)*d ∧ 2*q=8*p+h+k+5 then some u else none

theorem nextAtFast_eq (h k t : Nat) : nextAtFast h k t = nextAt h k t := by
  simp [nextAtFast,nextAt,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,Nat.mul_comm]

def nextEvenBatchFast (h k r : Nat) : Option Nat :=
  let p := 1 <<< k
  let w := 8*p+k
  let d := (w-h) >>> r
  let u := w-d
  if 4*p≤h+k+2 ∧ u≤8*p-3 ∧ h+(d <<< r)=w ∧ u+d=w
  then some u else none

theorem nextEvenBatchFast_eq (h k r : Nat) : nextEvenBatchFast h k r = nextEvenBatch h k r := by
  simp [nextEvenBatchFast,nextEvenBatch,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,Nat.mul_comm]

def nextMacroFast (h k r tCode : Nat) : Option Nat :=
  let v := if r=0 then some h else nextEvenBatchFast h k r
  match v with
  | none => none
  | some x => if tCode=0 then some x else nextAtFast x k (tCode-1)

theorem nextMacroFast_eq (h k r tCode : Nat) : nextMacroFast h k r tCode = nextMacro h k r tCode := by
  simp [nextMacroFast,nextMacro,nextEvenBatchFast_eq,nextAtFast_eq]

def runMacroBlockFast : Nat → List (Nat × Nat × Nat) → Option Nat
  | h, [] => some h
  | h, (k,r,tCode)::rest =>
    match nextMacroFast h k r tCode with
    | none => none
    | some u => runMacroBlockFast u rest

theorem runMacroBlockFast_eq (h : Nat) (w : List (Nat × Nat × Nat)) :
    runMacroBlockFast h w = runMacroBlock h w := by
  induction w generalizing h with
  | nil => rfl
  | cons a rest ih =>
    rcases a with ⟨k,r,tCode⟩
    simp only [runMacroBlockFast,runMacroBlock,nextMacroFast_eq]
    split <;> simp [ih]

theorem runMacroBlockFast_sound (h u : Nat) (w : List (Nat × Nat × Nat))
    (hc : runMacroBlockFast h w = some u) : Path Edge h u := by
  rw [runMacroBlockFast_eq] at hc
  exact runMacroBlock_sound _ _ _ hc

#print axioms runMacroBlockFast_sound
#print axioms nextMacro_sound
#print axioms runMacroBlock_sound
#print axioms even_batch
#print axioms nextEvenBatch_sound
end CascadeResetShield
