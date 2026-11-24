# D E-guard: an unbounded suffix-comparison family

**Status:** all-parameter mathematical proof by compositional crossing histories and 14 fixed, executable local certificates. Original literal table; source endpoint existence is now Lean-checked (see verification section). This is a prepared-section result, not a verdict on I5/I9/I15/I39 or a BB(6) bound.

Write P = 0101101011, M = 01100, J = 111111. At the E delimiter section of machine D, with scanned/right word P^r M J^s followed by blank cells and left guard 00101010 (nearest first), for every r,s >= 0:

* If s >= r, the guarded phase reaches B/0 at position -8, with the untouched alternating left sweep tail. For s=r the word to the right of that cell is 0111101 (0101010101)^r 01010 (101010)^r, followed by blanks. The cost of this guard is 48r²+124r+60 defined transitions.
* If s < r, the guard halts at F/1 after 48s²+138s+104+18r defined transitions. The undefined F/1 query is not counted here; the frozen-source convention adds one.

In fact the successful identity at s=r remains valid with **any finite right continuation** y after J^r: y is untouched. Thus s>r is obtained by taking y=J^(s-r). For canonical suffixes use physical equality under trailing blanks. The input E phase is reachable from any unary n=3k+4 by the already verified prefix_E theorem (Agent31); these statements do not establish that this particular suffix is reachable from a blank root.

## Exact local certificates and proof

A history is a list of pairs qr, each an entry into a spatial block from its left in state q, followed by its first exit to the left in state r. G denotes terminal propagation instead of a live exit. A history containing G must end there. A local certificate (w,L,R,w',c) means that servicing L on input word w using the ordered right-boundary replies R makes exactly c primitive transitions inside that block, changing its word to w'. A right entry must match the next request in R, and a live reply resumes the immediately preceding cell. A G reply propagates termination, with no further calls. The local checker simulates just these literal finite instructions, checks all requests and replies in order and checks their exhaustion.

Two composition rules are exact, not abstractions:
1. Temporal: concatenate two local histories on the same block when the first is live and its output is the second input; costs add.
2. Spatial: juxtapose adjacent blocks whose shared histories coincide. Substitute each right-block service for the corresponding request from the left block, in order. This yields a genuine computation on the concatenated tape. Proof by expanding the ordered finite local traces, recursively substituting child calls one spatial block to the right. Induction on the finite number of blocks terminates at the supplied rightmost history. No transition outside a certified block is assumed, and no unread tail is changed. In the terminal case only the executed prefix is substituted and G propagates to the outer guard. Every defined transition belongs to precisely one block, so costs add.

Use X=EC AF AC BA EB, T=AC BA EB, U=BA EB AC, Z=EC AG. AD and BC denote single pairs. The following finite certificates, plus the two guard certificates and one blank-cell certificate, are checked by threshold_check.py using the exact 12-entry table (11 defined entries).

| Block input | Left history | Right history | Output | Cost |
|---|---|---|---|---:|
| P | X | XT | (01)^5 | 121 |
| (01)^5 | T | T | (01)^5 | 60 |
| (01)^5 | AD | AD | 1^10 | 20 |
| M | X | empty | 01010 | 29 |
| 01010 | T | U | 01010 | 30 |
| 01010 | AD | BC | 11111 | 10 |
| J | U | empty | 101010 | 21 |
| 101010 | U | U | 101010 | 36 |
| 101010 | BC | BC | 111111 | 12 |
| P | Z | Z | 1011010110 | 18 |
| P | Z | X AD | 1111111111 | 79 |

The guard X returns B/0 at -8, with right prefix 0111101, in 31 local transitions, and Z halts after 3 local transitions. The blank cell on history BC writes 1 and returns C after 1 defined transition. Empty histories require no action and preserve arbitrary remaining cells.

**Success:** temporal iteration gives P: XT^i -> XT^(i+1), cost 121+60i. After r blocks, M maps XT^r -> U^r, cost 29+30r. Each J maps U^(i+1) -> U^i, cost 21+36i. After r such blocks the boundary history is empty. Spatial composition with the guard proves the stated endpoint, and summing the costs gives
    31 + sum(i=0..r-1,121+60i) +29+30r +sum(i=0..r-1,21+36i)
    =48r²+124r+60.
The successful suffix output has length 16r+12 before trimming its final zero, including the seven-cell guard prefix. Additional arbitrary right tape is unchanged.

**Failure:** put F_i=XT^i AD. Pass through r-s-1 P blocks using Z -> Z, then one P using Z -> F_0. Next s P blocks map F_i -> F_(i+1), cost 141+60i. M maps F_s -> U^s BC, cost 39+30s. Each J maps U^(i+1) BC -> U^i BC, cost 33+36i. The final blank cell services BC. Spatial composition with the halting guard Z and cost sum gives
    3 +18(r-s-1)+79 +sum(i=0..s-1,141+60i)+39+30s
      +sum(i=0..s-1,33+36i)+1
    =48s²+138s+104+18r.
The local G may be generated inside an earlier P; a live final blank-cell reply is compatible with terminal propagation on its left.

## Consequence: exact E-terminal predicate is nonregular

For any 1 <= i < j, the continuation M J^i distinguishes P^i from P^j: the former returns and the latter halts. Both complete input words are canonical (begin with 0, end with 1). Hence the exact E-guard terminal language on canonical finite suffixes has infinitely many Myhill-Nerode classes. No finite-state exact one-step classifier exists, even ignoring cost and output. Moreover successful histories at the P/M boundary are XT^r, of unbounded length; a universal fixed crossing-history cap is impossible even for returning computations. This is a specific barrier to the previous finite-prefix graph / bounded-history approach, not a proof that all inductive invariants fail or that the four roots are infinite.

Run python3 threshold_check.py for the fourteen finite checks. The parameterized conclusions follow from the two composition rules and finite certificates, not from bounded testing of r or s. The service composition lemma and original-source endpoints are now Lean-checked. The original source prefix and return-sweep facts are in the Agent31 Boundary module.

## Lean verification of the original source endpoints

The archive history-proof.tar.xz.b64 contains ServiceCore.lean, Threshold.lean, GuardSource.lean and generate_cert.py. Decode with base64, extract, and copy threshold_check.py into the same directory. Restore Agent31's original Boundary.lean (SHA256 0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883). With Lean 4.36.0-rc2 and LEAN_PATH=. run:

    python3 threshold_check.py
    python3 generate_cert.py > FixedCertificates.lean
    lean -o Boundary.olean Boundary.lean
    lean -o ServiceCore.olean ServiceCore.lean
    lean -o FixedCertificates.olean FixedCertificates.lean
    lean -o Threshold.olean Threshold.lean
    lean -o GuardSource.olean GuardSource.lean

All compiled locally. The archive SHA256 is d3c464e1791187210bf56129bf5ffa39b52bec4d5cdeccf67b9d3082384fdc82; generated FixedCertificates.lean SHA256 a5095dffeb7e0f7f5189bf87bb8c1c71d5528aff41ed2a7c9915a662db0a5d61. The generator is untrusted: it emits explicit proof terms checked by the kernel.

ServiceCore.Exit.sound connects the recursive first-exit service derivation to the literal source run for arbitrary left contexts. Chain.seq and Chain.spatial prove temporal and spatial composition; Chain.apply turns an arbitrary finite chain into actual source exits. Threshold.successful_services and failing_services_exact are all-parameter theorems with arbitrary preserved right continuation in the success case and the exact implicit blank tail in the failure case.

GuardSource.prepared_return proves existence of an original source run from the unary section n=3k+4 with suffix P^r M J^r y to F/0 with unary n'=8k+3, followed by gp=0111101 and (01)^(5r) 01010 (10)^(3r) y. GuardSource.prepared_halt proves actual frozen-state reachability for every s<r from the source section P^r M J^s. The four guard/source and three service theorem audits report only propext, Classical.choice, Quot.sound. No sorryAx.

The exact cost sums and first-event claim above are mathematical proofs from the local history certificates; the current Lean adapter establishes endpoint existence (not exact cost, first-event minimality, or a formal automata-language theorem). This distinction is intentional.
