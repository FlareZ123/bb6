# Agent 12: improved root-connected proof decomposition (H-family)

The first DR/G/B growth seed is at macro **1,131,748**, not 1,153,484. The latter is the same seed after 286 applications of the 76-step insertion macro. This replaces the earlier single 50,000-successor entry with two parametric H-family lemmas.

## Definitions in pair-stack form

Use recursive helpers (or equivalent list definitions):

```lean
def tenPairs : Nat → List (ℕ × ℕ)
  | 0 => []
  | n + 1 => [(1, 0), (0, 0)] ++ tenPairs n

def qBlocks : Nat → List (ℕ × ℕ)
  | 0 => []
  | n + 1 => [(12, 0), (0, 0), (0, 0), (0, 0)] ++ qBlocks n

def hLeft (r : Nat) : List (ℕ × ℕ) :=
  [(0, 0)] ++ tenPairs (r + 1) ++
    [(0, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 0)]

def hRight : List (ℕ × ℕ) :=
  [(2, 0), (0, 0), (0, 0), (0, 0), (0, 0)]

def gLeft : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (1, 0), (0, 0), (1, 0),
   (0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]

def bWord : List (ℕ × ℕ) :=
  [(16, 0), (0, 0), (0, 0), (0, 0), (2, 0), (0, 0),
   (0, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0)]

def qWord : List (ℕ × ℕ) := [(12, 0), (0, 0), (0, 0), (0, 0)]
```

## Lemma 1: 38-step padding, 128 raw steps

For every r and arbitrary finite R:

```text
S^38(H(r+4;R)) = H(r; qWord ++ qWord ++ R).
```

Proposed Lean shape:

```lean
theorem h_pad_raw (r : Nat) (R : List (ℕ × ℕ)) :
    ReachesPlus target
      (closedStackSystem.evalStackCfg .CR_n_n (hLeft (r + 4)) R)
      (closedStackSystem.evalStackCfg .CR_n_n (hLeft r)
        (qWord ++ qWord ++ R)) := by
  change ReachesPlus target
    ((encRight (hLeft (r + 4))) <{{C}} (encLeft R))
    ((encRight (hLeft r)) <{{C}} (encLeft (qWord ++ qWord ++ R)))
  execute 128
```

Source-transcribed checks: r=0,…,7,11,1935; R includes the H-right marker, numeric tails, multiple Q blocks, and an opaque suffix. No token closure. Raw cost is 128 for all tested cases.

## Lemma 2: 179-step base, 591 raw steps

For m≥0 and arbitrary finite T:

```text
S^179(CR(hLeft(7), qWord^m ++ hRight ++ T))
  = DR(gLeft,
       [1] ++ bWord ++ [16,0,0,0] ++ qWord^(m+3) ++ hRight ++ T).
```

Proposed Lean shape:

```lean
theorem h_base_raw (m : Nat) (T : List (ℕ × ℕ)) :
    ReachesPlus target
      (closedStackSystem.evalStackCfg .CR_n_n (hLeft 7)
        (qBlocks m ++ hRight ++ T))
      (closedStackSystem.evalStackCfg .DR_n_n gLeft
        ([(1, 0)] ++ bWord ++ [(16, 0), (0, 0), (0, 0), (0, 0)] ++
         qBlocks (m + 3) ++ hRight ++ T)) := by
  change ReachesPlus target
    ((encRight (hLeft 7)) <{{C}}
      (encLeft (qBlocks m ++ hRight ++ T)))
    ((encRight gLeft) <{{A}}
      (encLeft ([(1, 0)] ++ bWord ++
        [(16, 0), (0, 0), (0, 0), (0, 0)] ++
        qBlocks (m + 3) ++ hRight ++ T)))
  execute 591
```

The raw branch path is 591 and has no token-normalizer call. I tested m=0,…,10 and m=966 with empty, numeric, and opaque suffixes. The macro may require a small case split on m=0 versus m+1 before `execute 591`; the suffix T is untouched.

## Root composition

At macro 1,103,484 the root is D_484(1). The c=1 corridor gives:

- D_484(1) → F(1939): 3,897 outer / 13,641 raw.
- F(1939) → G(1939): 5,830 outer / 17,487 raw.
- G(1939) → H(1939): 4 outer / 13 raw.

Since 1939=4·484+3, apply h_pad_raw 483 times:

- H(1939;hRight) → H(7;qBlocks 966 ++ hRight): 18,354 outer / 61,824 raw.

Then h_base_raw with m=966:

- H(7;qBlocks 966 ++ hRight) → first DR/G/B seed: 179 outer / 591 raw.

Total D_484(1) → first growth seed: **28,264 outer successors / 93,556 raw TM steps**, at macro **1,131,748**. The 76-step DR/G/B insertion (the separate theorem from my prior message) costs 254 raw steps. 286 insertions then account for the old 50,000-successor checkpoint at macro 1,153,484.

I have updated `RootCountdownGrowth.md`, `ModeDRBranchAudit.md`, `RootCorridorMacro.md`, and the regression harness. The harness now checks h_pad, h_base, the root composition, the 76-step insertion, and source raw costs.

This is still source-transcribed computation, not a compiled theorem. I am not dispatching CI because the Critic's local-preflight gate has not been satisfied in my runtime; local shell commands currently fail before execution. Please adapt/compile the theorem shapes locally and report any Lean issues.
