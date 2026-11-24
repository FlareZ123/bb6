# Counted TM63 zipper itinerary (Agent 50)

Independent from the residue-specific source dispatcher: every finite frame is an arbitrary nearest-first list, and the zipper's state is Fin 6. The literal TM63 table is the published BusyCoq table, pinned at ccz181078/busycoq@3f302b87f5fb933c46e97672ffbb6907f373fb6e verify/SOBCv5.v, TM63. No admitted propositions or native_decide.

Local Lean 4.36.0-rc2 succeeded for all three modules with exported axiom sets contained in propext, Classical.choice, Quot.sound. Blob IDs match the locally compiled source bytes.

* CountedZipper.lean: lc_carry costs 4+12v, inc0_carry costs 48+12v+12b, reset_prefix costs 63+4m+12(a+v)+3b, reset_prime_prefix costs 97+12(L+a)+3b, terminal costs 59+12(L+a) successful moves. The arbitrary-frame outer carry is shared by all markers.
* CountedItinerary.lean: binary encoding and carry decomposition, counted inner drain, all-marker rst and rstPrime, haltFinal.
* ChampionItinerary.lean: section_run, marker and parity invariants, mod-3 arithmetic, complete_itinerary. This proves exact symbolic remainingCost from s1 3 7 2 6 0 63 h to a configuration with step = none for every h. The first choice-defined value is uniquely specified by first_eq; prevents accidental kernel evaluation of astronomically large recursive naturals.

To compile, set LEAN_PATH to this directory, lean -o CountedZipper.olean CountedZipper.lean, then CountedItinerary and ChampionItinerary likewise. No Mathlib or repository imports needed.

**Boundary:** this is a complete kernel-checked zipper itinerary from initial S1; blank-root and transport into the repository's original infinite-tape BB6Coverage.run and TM1 score still need the source adapter. The existing RootSourceBridge already proves the matching 27959-step blank-root configuration. Do not promote to accepted BB6 lower bound until source transport and score convention are checked. No universal upper bound.
