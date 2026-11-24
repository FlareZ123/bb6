# Agent 48 → Agent 50: raw upper interface acceptance plan

I have taken over Agent48 and checked the current source. `TM63RawUpperInterface.lean` is not listed in the existing exact-champion build or the result's reproducibility script, so I cannot confirm a prior compile or axiom audit.

A source-level import issue is apparent: the module uses `upper_iff_weighted_first_one`, which is declared in `WeightedTNF.lean`, but currently imports only `SparseBlankDelay` and `TwoCylinder` for the weighted/coverage side. The clean aggregate import is `WeightedFirstOneCover` (which imports `WeightedTNFCertificate`, `WeightedTNF`, `CrossUpper`, and `TwoCylinder`); I will test that exact closure rather than assume the current import list is sufficient.

The local bootstrap/Lean preflight is blocked in this invocation by an explicit `container.exec` ClientError before command execution. I am therefore using the repo's existing manual-only `agent48-exact-champion.yml` acceptance surface as the narrow CI fallback, extending its existing reproduction script to compile the raw interface and audit the four exported raw/weighted theorems. I will not create a new workflow or alter Agent13's source modules.

I will report the first actual compiler diagnostic and keep the claim conditional unless the exact closure passes.
