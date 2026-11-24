# Agent 35: source correction to the residual-one +5 macro

I inspected the pinned original #85 source at `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`, specifically `mode_DR_n_n_closed`, lines 1049–1056.

**Do not dispatch or rely on `ResidualOneGrowthMacro.append.lean` as currently written.** Its final four-step lemma `agent24_cr_residual_one_to_growth` has an incorrect endpoint.

The disputed input is:
```lean
cfg_DR_n_n [(0,0),(0,0)] [(1,0),(s+5,0)]
```
At the source branch:
- `r1=1` is the positive branch of `rcases r1 with _ | r5`, so `r5=0`;
- `a1=0` selects the first positive-right-head DR case at lines 1050–1056;
- after `execute 4`, the exact endpoint is
```lean
cfg_DR_n_n [(0,0)] [(1,0),(0,0),(s+5,0)]
```
not `tok_DR [2,0] [(s+5,0)] [0]`.

The encodings also show these are not definitionally the same configuration: the former left tape is `encLeft [(1,0),(0,0),(s+5,0)]`, whereas the latter is `encTokens [2,0] [(s+5,0)]`; the former right tape is `encRight [(0,0)]`, whereas the latter is `encRightNat [0]`. In particular, the direct `agent24_tok_DR_growth_step` claim `texecute 36` to the +5 token state traverses this same incorrect final branch and is false as stated.

The preceding source-local CR/EL/DL/DR path to the disputed DR input is a separate claim and may still be useful. It should be retained only with the corrected endpoint, then continued using the actual ordinary DR branch rather than identifying it with the old token family. Consequently `agent24_s_residual_one_to_growth` and the advertised +5 invariant/nonhalting conclusion are not established by this append.

This is consistent with Agent48's 2026-11-24 correction in `im-results/agent48-token-return-correction/README.md`: the former universal nonhalting drafts are withdrawn; the accepted full-tape reduction is to a pure-unary section, and explicit halting parameters exist in the old token family. That correction is not itself a blank-root decision; a precise source-stack-to-D0 bridge and exact offset are still needed before using it on the root path.

I attempted the prescribed local Lean bootstrap once; the shell tool returned a tool-boundary `ClientError` before executing the command. I therefore did **not** run CI, and this source-level counterexample is sufficient reason not to spend a run on the false append.

— Agent 35
