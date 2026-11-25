# Two-sided local-window nonhalting certificates

**Source-accepted reusable theorem and four pilot witnesses.** The checker is independent of the candidate search. In Lean 4.36.0-rc2, [run 45528132324](https://github.com/FlareZ123/bb6/actions/runs/45528132324), pinned 1e27440858824dc6e8217234c247bf3b22f9fa3c, verified the exact SweepPumping / SparseZipper source closure, four generated certificates and the standard-axiom guard. The remaining candidate certificates have not all been kernel checked.

## Mathematical invariant

Fix width k≥1. For each direction, a set E of allowed (k+1)-bit words constrains every consecutive block in the corresponding half-tape (including infinite blank padding). For the actual machine state q, scanned bit a, and the two k-bit head-adjacent windows l,r, a finite set S constrains the joint quadruple (q,a,l,r). Number windows little-endian from the head.

On a right move writing w and entering q', the new left window is w+2*(l mod 2^(k-1)), the written bit together with the old left window yields a new allowed gram, and the new scanned bit is r mod 2. For every allowed extension e of r, require the successor quadruple in S with new right window floor(r/2)+2^(k-1)*e. Left moves are symmetric. Also require both all-zero grams and the initial blank quadruple. No element of S may have an unassigned or halting transition. These finite tests suffice: pushing introduces only one new gram, popping retains the suffix grammar, and the true extension is one of the allowed extensions. Thus every actual successor still satisfies the invariant, and all finite blank-run prefixes exist. This proves nonhalting of every compatible total completion.

The Lean module `NGramCertificate.lean` formalizes this invariant with `TapeOK`, `Inv`, `inv_step`, `live`, and `never`, lifting through the repository's exact `run_project` and `zrun_sound`. The finite checker uses a low-bit trie for pairs of windows, bitsets for the permitted grams, and kernel reduction via `by decide`. The theorem does not assume the search is correct.

## Discovery and use

`ngram.cpp` computes the least closed abstract set from the initial blank configuration: push creates a gram, and pop follows all permitted extensions. A new gram wakes all prior states that pop from that window. It rejects immediately when an undefined or halting table row is reached. Failure means only that this abstraction is too coarse or the machine reaches a hole, not that the machine halts.

```sh
g++ -std=c++17 -O3 ngram.cpp -o /tmp/ngram
/tmp/ngram 10 < pilot.txt > /tmp/ngram-pilot.txt
python emit_ngram.py pilot.txt /tmp/ngram-pilot.txt NGramPilot.lean
```

From the repo root, after `python im-results/agent13-coverage/unpack.py`, compile the resulting module with `python tools/lean_compile_closure.py --workdir /tmp/ngram-pilot --jobs 2 im-results/agent1-ngram/NGramPilot.lean`. The manual shared workflow target is `weighted-tnf-ngram-pilot`. Inputs consist of integer identifiers and exact 36-character table strings, with optional underscore separators; undefined entries are `---`.

## Raw60 experiment

Of 12,556 raw60 residual open leaves, 832 remain after the pooled FAR bank and additional five-state FAR search. The local-window search on these 832 finds **332** candidates by width 7 and **423** by width 10; a further 9 at width 11–12 have substantially larger certificates. Four pilot cases (global IDs 2614, 49, 9210, 12426) are source accepted, at widths 3, 6, 7, 10. The 423 candidates must not all be counted as accepted before their exact individual checks pass. The next use is integrating these witnesses into the first-hole tree rather than reporting disconnected counts as a raw60 bound.

This is a new checker within this repository; no claim of priority for n-gram abstractions in the broader literature.
