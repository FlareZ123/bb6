# #693: all-depth inverse-ray sparsity
Status: rigorous arithmetic necessary condition, not a root decision. The core and root transport to an exact transcription of upstream highLevelNext are checked by Lean 4.36.0-rc2; the full upstream import is not compiled here.

## Source
Machine 1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD, [pinned upstream source](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean), isHalt_iff_highLevel_acceleration, highLevelStart = C 8 1. This uses the upstream certificate as an external premise. No new raw-machine certificate is claimed.

## Exact conjugacy
Use a=6u+3p-10, c=v-u, p in {0,1}, u>=2, v>=u. Start (u,v,p)=(3,4,0). Stop v=u. At v=u+1 reset to (4,3u-2,1) for p=0, (2,3u+1,0) for p=1. Otherwise H=(3u+p,v-u,p) if v>=4u+p; L=(v-u+p,3u+2p-1,1-p) otherwise. The invariant and conjugacy are checked for every valid state. The inverse regular formulas at target (U,V,p) are H: u=(U-p)/3, v=V+u; L: u=(V-(1-2p))/3, v=U+u-(1-p). Integrality and guard checks suffice for exact regular predecessors.

## Terminal-ray theorem
Fix terminal parity p and parameter t>=0, terminal ray (t+2,t+2,p). For a ray (A t+x,B t+y,p) with A,B>0 and neither divisible by 3, each inverse branch determines exactly one residue digit r modulo 3 from its integral division. Substitute t=3j+r. H gives positive direction (A,A+3B); L gives (B,B+3A). Both coordinates stay units modulo 3. Thus a word of k inverse regular branches covers only a single residue modulo 3^k, and lifts to a positive-direction affine ray in the remaining parameter. If a reset is encountered earlier its output u must be 2 or 4 according to output parity; because the direction coefficient is positive, each shorter word admits at most one exceptional terminal parameter. All paths from any admissible c=1 initial state to a terminal contain a reset. Hence for every m, every reachable terminal parameter belongs to at most 2^m residue classes modulo 3^m, plus at most 2^m-1 exceptional exact values. Guards omitted in the sieve only overapproximate. For 0<=t<N and m=ceil(log_3 N), each class contributes at most one value: <=2^(m+1)-1 per parity, O(N^(log_3 2)). This counting corollary is a paper argument from the kernel-checked cover, not a separate formal cardinality proof. Applies to all admissible reset seeds, including authentic root; it cannot exclude one specific orbit merely from density.

## Reproduce
Decode InverseRay.lean.xz.b64 with base64 then xz -d. SHA256 of decompressed Lean file a4330836a1b12adacb93a7b69a7fbea5a5db7b99ae5ac34174c9749211d64e3e. Run lean InverseRay.lean. The five audited theorems conjugacy, next_valid, back_sound, terminal_cover, authentic_root_terminal_cover use only propext, Classical.choice, Quot.sound. No sorry. The last theorem states that every reachable pair (a,0) in the exact arithmetic transcription has a nonnegative parameter and belongs to the cover for every depth m. The exact reset exceptions are defined by integer division; spurious exceptions may remain. No claim that the cover is sufficient.

## Next
Build stronger inverse guard pruning or an all-time invariant for this root, rather than replaying finite forward prefixes. Inverse mass x+c with x=3u+p strictly decreases along genuine predecessors, so any fixed terminal can be completely checked backwards; the problem is to cover the unbounded terminal ray.

## Stronger consequence
See [semilinear impossibility theorem](../../results/2026-11-24-693-semilinear-obstruction-agent3.md), with supporting Obstruction.lean.xz.b64. Do not search for Presburger invariants in these coordinates. The genuine root decision requires a nonsemilinear invariant or exact terminal reachability.
