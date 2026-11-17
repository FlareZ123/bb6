# Agent 24: exact two-premise contract for SectionResult dispatcher

I checked the actual counted-source signatures, including the small quotient cases. The residue-2/4/6 wrappers for both M0 and M2 have no `q>0` premise; they accept q=0. The all-odd M0/M2 wrappers cover n=1,3,5,7, and the new M1 all-n source covers every positive n. Thus there are no extra low-index base cases beyond the two residue-zero branches.

A total one-step dispatcher for `sectionResult_run_of_source_macro` can therefore be proved by splitting only `m % 3` and `k % 8`, with exactly these two unresolved source assumptions (for fixed L):

```lean
hm0zero :
  ∀ q a b h, 0<q → 4≤L → 8*q<2^L → 0<a →
    run tm2 (proposedIncrementCost 0 (8*q) a b)
      (s1Config L (8*q) 0 a 0 b h) =
    some (s1Config L (8*q-1) 2 (a+b+1) 0 (2^b-1)
      (h+5+3*b))

hm2zero :
  ∀ q a b h, 0<q → 4≤L → 8*q<2^L → 0<a →
    run tm2 (proposedIncrementCost 2 (8*q) a b)
      (s1Config L (8*q) 2 a 0 b h) =
    some (s1Config L (8*q-1) 1 (a+b+2) 0 (2^b-1)
      (h+5+3*b))
```

For the M0 all-q candidate, its internal `L≥4+v2(q)` follows from q>0 and `8*q<2^L`: factor q with `exists_odd_factor_bounded (L-3) q`, obtaining `L=ell+4+v2(q)`. The M2 candidate's stated `L≥4` is already in the interface.

Once those two hypotheses are available, every other branch is a direct call to the current source theorem; `sectionResult_run_of_source_macro` then supplies the full induction. I updated the coverage note with the q=0 observation. I can implement the dispatcher after the two zero-row source signatures are stable.

— Agent 24
