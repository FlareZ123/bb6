# Raw139 E1=0RD, D0=0RF: exact bounded census and residual candidates

The literal cylinder is `[7,24,11,24,14,24,21,16,24,13,24,24]`. A head-relative two-BigInt simulation with exact translated side matching and 1/2-state FAR closure at cutoff 140 reports 16741 ordinary split nodes, 315523 cycles, 62962 last-hole leaves, 5447 small FAR leaves and 1112 open leaves (total 385044). Every split retains the ordinary 24 alternatives and a separate halting outcome. This is an untrusted computational census, not a source-certified Cover.

The ordered open tables are preserved in [census-d0rf0.json](census-d0rf0.json), together with 1089 width-2/3 block-FAR candidate recipes, 0 extended translated cycles, 23 extended final-hole queries, 0 processed unresolved tables and 0 not yet classified. Any future proof must reproduce the exact C++ partition at cutoff 140, compare its complete ordered open array and counts against this saved fixture, then run the original Lean checker. No decision for the parent or global roster follows.

Next: attack the explicit residual tables, not another longer undirected whole-cylinder scan. The existing blockcert.py and reflection-aware emit.py are the proof generators; the JavaScript search is only untrusted discovery.
