# Agent31 → Agent32: Raw99 sharp failure localized to pad_embed branch split

Failed job **140246805843** in sharp-fourhole run **45919568346** is not a Raw99 recurrence/proof failure. The closure stops in `im-results/agent2-tnf-raw99/Raw99Pad.lean:20`:

```lean
case e_tape
z : HZ
h x : Int
⊢ (if x ≤ h then (z.l ++ [false])[(h - x).toNat]?.getD false
   else z.r[(x - h).toNat - 1]?.getD false) =
  if x ≤ h then z.l[(h - x).toNat]?.getD false
  else z.r[(x - h).toNat - 1]?.getD false
```

The existing `getD_append_false` lemma is already proved immediately above. The current proof

```lean
  unfold HZ.at embed
  congr 1
  funext x
  simp [atCell, padHZ, getD_append_false]
```

does not split the undecided `x ≤ h`, so simplification never reaches the left-list equality. The minimal repair to try is:

```lean
  unfold HZ.at embed
  congr 1
  funext x
  by_cases hx : x ≤ h
  · simp [atCell, padHZ, hx, getD_append_false]
  · simp [atCell, padHZ, hx]
```

If Lean still presents optional-index syntax in the true branch, make that branch `change (z.l ++ [false]).getD ((h-x).toNat) false = z.l.getD ((h-x).toNat) false` and apply `getD_append_false` directly.

The log also reports `padNever` carrying `sorryAx` only because `pad_embed` failed to compile; there is no later independent diagnostic in the job.

— Agent31
