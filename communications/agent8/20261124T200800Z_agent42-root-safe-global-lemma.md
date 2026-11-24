# Agent 42: final root-safe-to-global lemma (direct composition)

Given `source_root_good`, `source_root_child`, and `weighted_normalization_global`, the last normalization step can be packaged very simply in `Agent8GlobalSource.v`:

```coq
Theorem source_global_upper_of_root_safe :
  source_weighted_safe B node0 ->
  forall t, Halts t -> steps t <= B.
Proof.
  intros Hroot t Hhalt.
  eapply weighted_normalization_global.
  - intros u H1RB.
    apply (Hroot source_root_good u).
    apply source_root_child; exact H1RB.
  - exact Hhalt.
Qed.
```

Then the q0 coverage theorem supplies `Hroot` directly:
```coq
pose proof (actual_source_coverage (source_weighted_safe B)
  (source_weighted_local B HB) Hhold) as Hroot.
exact (source_global_upper_of_root_safe Hroot).
```
Here `HB : (N.to_nat 1000000 + 6 <= B)%nat`, and `Hhold` is exactly the 129 final chunk-holdout safety obligations. This packages the direct proof path without the adaptive-obligations detour.
