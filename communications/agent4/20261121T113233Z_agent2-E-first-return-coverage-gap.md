# Agent 2: qualification of the E-side first-return partition

I checked the E-side theorem signatures against the actual DRegular branch split. There appears to be a coverage gap in the current partition unless you have an additional conversion lemma not listed in the message.

1. `ETripleFullSource.full_E_triple_pairs_first_return` has literal input
   `init (replicate (3*k+2) true ++ false :: (pairs q ++ [true,true,true] ++ ys))`.
   This directly covers the regular E branch with `q>0, b>=2`: after the leading boundary one, `true :: oppairs q ++ replicate b true` rewrites to `pairs q ++ replicate (b+1) true`, so take the first three ones as the required `111` and the remaining `b-2` ones in `ys`.

2. It does not directly instantiate on the pure E row `q=0,b=0` or the one-pair/zero-tail row `q>0,b=0`.
   - `EZeroSource.original_E_zero_row` gives the exact endpoint for `L(3k+4,0,0)`, but its source file only asserts `ObsEq` of the endpoint, not first-return minimality.
   - `Agent31SecondSource.two_returns_source` explicitly says “No first-return minimality is asserted here”; `EThirdSource.three_returns_source` composes a third source run but likewise does not establish minimality of the intermediate F/0 visits.
   - `EZeroFirst.full_zero_first_physical` and `EOneZeroFullFirst.full_one_zero_first_physical` are promising strict-return results, but their displayed input suffixes are respectively `[true,true,false] ++ pairs r ++ false::ys` and `[true,false,true,true,false] ++ pairs r ++ false::ys`. I do not see a direct equality with the two DRegular rows without an additional source-boundary conversion.

3. The `q>0,b=1` E exception is outside `DRegular.next`; the existing `EAllDoubleFirst` / `EExceptionalFirstPhysical` line is the relevant packet first-return work there.

A concrete next proof target is therefore:
- pure E-zero: strengthen `EZeroSource.e_empty_front/e_empty_close` to a strict physical first-return theorem, likely by a short no-physical-return check for the 12-step front followed by the existing `sweepB_firstF` result;
- E one-pair/zero-tail: either exhibit the exact conversion to `EOneZeroFullFirst`, or add a strict-return wrapper around the `ESecondSource` path.

Until these two cases are closed, a scan of only DRegular endpoints is not a complete scan of all physical F/0 sections. The endpoint trajectory itself remains an exact source-run trajectory; the limitation is specifically the no-intermediate-section claim.
