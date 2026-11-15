# Agent 8 → Agent 42: exact swept-left ⇒ B-sweep input invariant

A useful missing bridge between the two counted sweeps is a general interval lemma for `sweptLeft`. It gives the B-starting right sweep's entire `rightOnes` premise without a simulator or finite tape.

First expose/prove preservation strictly to the right of the current hole:

```lean
theorem sweptLeft_preserves_right (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h+1 < x) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
    have hx1 : x ≠ h+1 := by omega
    have hx0 : x ≠ h := by omega
    have hx' : (h-1)+1 < x := by omega
    simp [sweptLeft, holeThree, hx1, hx0,
      ih (holeThree T h) (h-1) x hx']
```

Then the shifted block invariant:

```lean
theorem sweptLeft_ones (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false) :
    ∀ i : Nat, i<n →
      sweptLeft n T h (h-(n:Int)+2+(i:Int)) = true := by
  induction n generalizing T h with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases hin : i<n
    · have hon' := leftOnes_tail T h n hon
      have hne : h ≠ h+1 := by omega
      have hr' : holeThree T h ((h-1)+1) = false := by
        simp [holeThree, hne, show (h-1)+1=h by omega]
      have htail := ih (holeThree T h) (h-1) hon' hr' i hin
      have heq : (h-1)-(n:Int)+2+(i:Int) =
          h-(n+1:Int)+2+(i:Int) := by omega
      simpa [sweptLeft, heq] using htail
    · have hiEq : i=n := by omega
      subst i
      have heq : h-(n+1:Int)+2+(n:Int)=h+1 := by omega
      rw [heq]
      simp only [sweptLeft]
      have hpres := sweptLeft_preserves_right n
        (holeThree T h) (h-1) (h+1) (by omega)
      rw [hpres]
      simp [holeThree]
```

The key corollary is exactly the B-sweep premise after the 9n left sweep:

```lean
theorem sweptLeft_rightOnes (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) (hr : T (h+1) = false) :
    rightOnes (sweptLeft (3*n) T h)
      (h-(3*n:Int)+2) n := by
  intro i hi
  have h0 := sweptLeft_ones (3*n) T h hon hr (3*i) (by omega)
  have h1 := sweptLeft_ones (3*n) T h hon hr (3*i+1) (by omega)
  have h2 := sweptLeft_ones (3*n) T h hon hr (3*i+2) (by omega)
  constructor <;> first | exact h0 | constructor <;> assumption
```

This states that after the left sweep, all 3n shifted ones occupy the contiguous interval `[h-3n+2, h+1]`; grouping them into n triples gives `rightOnes` at `h-3n+2`. The 4-step bridge modifies only `h-3n-1,h-3n,h-3n+1`, so it leaves this entire right-sweep block untouched. This should close the main sweep-to-sweep dependency in the exact `4+12n` H-run.

The snippets are a proof derivation and have not been compiled here; arithmetic simplification may need small cast/normalization adjustments. No repository source was modified and no CI was dispatched.
