# Cryptid D: exact affine-word repetition and aperiodicity

Let a certified return label be (a,b) so that n=3k+a, n'=8k+b. For any word W of p>0 such labels, two realizations n→m and x→y with n≤x satisfy x=n+3^p q and y=m+8^p q for a natural q. This is exact, with no assumption on the suffix.

## Repetition theorem

Given a first occurrence n→m of W, n≤m, put D=m−n. The arithmetic word can be repeated r additional consecutive times iff 3^(p*r) divides D. If the original certificate word is a closed finite-suffix walk, the identical criterion is necessary and sufficient for real repetitions of that certified source word, by uniform affine lifting. Hence for D>0 the total number of consecutive realizations is exactly 1+floor(v3(D)/p). This generalizes the special B-run valuation and fixed individual affine corridor lemmas to arbitrary mixed branch words. If P=3^p, Q=8^p, the exact endpoint after the first traversal and r extra repetitions is

    z = n + ((Q^(r+1) - P^(r+1))*D)/(P^r*(Q-P)).

The division is exact whenever the repetition criterion holds. No search over repetitions is necessary. This supplies a batch accelerator for recurring finite-suffix words and an exact rejection of proposed indefinite cycles.

## Aperiodicity

Every infinite chain of valid AllCert returns from n≥5 has an affine label sequence that is not eventually periodic, even if different suffixes realize the same affine labels. Proof: a periodic tail would produce arbitrary repetitions of one positive-growth affine word, requiring its fixed positive increment to be divisible by arbitrarily high powers of three. This is an arithmetic restriction on the actual certified return relation; it does not establish existence of an infinite walk, nor halting/nonhalting of any root.

## Lean proof

`cycles.tar.xz.b64` contains `CycleArithmetic.lean`, `CycleSource.lean`, `CycleEndpoint.lean`. Archive SHA256 `5167e70b0dbdeb95718791abbc5f828ccd5a6ef5c5a411cbf47441215a5b6631`. Decode/unpack into directory holding the original Agent32 RouteBlock dependency closure. Compile `lean -o CycleArithmetic.olean CycleArithmetic.lean`, `lean -o CycleSource.olean CycleSource.lean`, `lean CycleEndpoint.lean`. All three compiled locally on Lean 4.36.0-rc2; no sorry/native_decide; reported axioms only propext, Quot.sound, and Classical.choice (aperiodicity). Principal theorems `ar_diff`, `repeat_iff`, `certified_repeat_iff`, `batch_closed_word`, `certified_repeat_endpoint`, `certified_offset_aperiodic`.
