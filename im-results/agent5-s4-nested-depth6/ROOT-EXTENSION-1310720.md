# Exact S4 root extension to the first-level macro boundary

**Status (16 November 2026):** finite exact-integer reduced-map replay from a source-certified root state. It extends the verified finite trajectory but is not itself a Lean-kernel theorem and does not decide S4 or BB(6).

## Starting point and result

The original-source Lean certificates establish the genuine S4 reduced root at return 5,457 with full stack

```text
[283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
 366446, 435688, 443554, 1702180, 1770018, 211301, 281569,
 35137, 35134]
```

The deterministic BigInt replay in [s5457_root_extension.mjs](s5457_root_extension.mjs) applies four blocks of 327,680 reduced P-returns, i.e. 1,310,720 P-returns and 3,932,160 source-aligned G applications. Every application succeeds. The final return is 1,316,177, and the complete 24-digit stack is exactly

```text
[283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
 366446, 435438, 366335, 527037, 2639156, 3037351, 3252483,
 6310511, 24221543, 24423525, 56750562, 67602890, 162126013,
 335820941, 659578070]
```

This is exactly the `blockRoot()` state hard-coded as the starting point of
`s4_suffix_macro.cpp). It therefore supplies a direct finite reduced-map
connection from the source-certified return-5457 root to the first-level
macro boundary.

## The only two full-suffix events

During the 1,310,720 returns, the stack length increases only twice. At each
event the carry consumes the entire current suffix, so the terminal quotient
is `q=(W(S)+c)/2^(length(S)-1)`. The source theorem says the gate halts iff
this quotient is a power of two.

| Relative P-return | Gate | Old length | New length | Terminal quotient q | v2(q) | Odd part |
|---:|---:|---:|---:|---:|---:|---:|
| 25,685 | G(219) | 18 | 22 | 6,578,056 | 3 | 822,257 |
| 929,375 | G(290) | 22 | 24 | 283,561,618 | 1 | 141,780,809 |

Both odd parts exceed one, so neither event halts. All other gates stop before consuming the entire current suffix. The script checks these exact quotients and the final full stack.

## Evidence boundary

- The return-5,457 starting state is source-certified by the original-source runs recorded in the [main S4 dossier](README.md).
- The replay is exact BigInt computation of the reduced `G(509);G(290);G(219)` map. It is not a Lean proof of the 3,932,160 source transitions or their primitive TM step count.
- The match to `blockRoot()` validates the starting full stack for the existing suffix-renormalization experiments. The 18-prefix 64-block cycle, extracted Q word, and deeper projected cycles remain computational premises rather than kernel-certified theorems.
- This finite continuation does not prove future survival. No conclusion about BB(6) follows.

The next useful step is to formalize the source-rooted block bridge or use the now-connected block root to attack a history-sensitive all-time invariant. Do not relabel the computational replay as a source proof.
