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

### Second-moment certificates at the two events

Write \(x_i=b_i+1\), \(M=\sum x_i\), \(D=\sum i x_i\), and \(E_2=\sum i^2x_i\). For a known \(k\)-digit prefix and a tail of length \(L\), put \(z_j=x_{k+j}-1=b_{k+j}\). The total mass, first moment, and second moment determine
\[
R=\sum z_j,\qquad J=\sum jz_j,\qquad K=\sum j^2z_j
\]
after subtracting the known prefix and the mandatory one in each tail position.

- At the first event (\(n=18,k=15,L=3\)), the exact values are \(R=16,693,992\), \(J=3,681,440\), and \(K=3,751,708\). They uniquely reconstruct the three tail digits as **[13,047,686, 3,611,172, 35,134]**, agreeing with the full replay and giving the exact terminal quotient \(q=6,578,056\).
- At the second event (\(n=22,k=18,L=4\)), the exact values are \(R=810,175,944\), \(J=1,055,065,502\), and \(K=1,747,933,692\). Set \(A=(K-J)/2=346,434,095\) and \(t=z_3\). Every nonnegative integer tail with these moments has
  \[
  z_2=A-3t,\quad z_1=J-2A+3t,\quad z_0=R-J+A-t,
  \]
  so \(0\le t\le101,544,537\). Its weighted tail excess is \(z_0+2z_1+4z_2+8z_3=R+J+A+t\). Therefore the full terminal quotient is rigorously confined to
  \[
  \boxed{283,510,228\le q\le296,203,294.}
  \]
  The actual replayed quotient is \(283,561,618\). The entire interval lies strictly between \(2^{28}=268,435,456\) and \(2^{29}=536,870,912\), so **no power of two is compatible with these three moments**.

The updated [BigInt replay](s5457_root_extension.mjs) computes and asserts both certificates. This is a sharper finite-state exclusion than the earlier first-moment interval at the second event. It remains conditional on the exact reduced-map replay: the later moments and event states are not yet a Lean source theorem, and this does not exclude future full-suffix events.

Both odd parts exceed one, so neither event halts. All other gates stop before consuming the entire current suffix. The script checks these exact quotients, moment fibres, and the final full stack.

## Evidence boundary

- The return-5,457 starting state is source-certified by the original-source runs recorded in the [main S4 dossier](README.md).
- The replay is exact BigInt computation of the reduced `G(509);G(290);G(219)` map. It is not a Lean proof of the 3,932,160 source transitions or their primitive TM step count.
- The match to `blockRoot()` validates the starting full stack for the existing suffix-renormalization experiments. The 18-prefix 64-block cycle, extracted Q word, and deeper projected cycles remain computational premises rather than kernel-certified theorems.
- This finite continuation does not prove future survival. No conclusion about BB(6) follows.

The next useful step is to formalize the source-rooted block bridge or use the now-connected block root to attack a history-sensitive all-time invariant. Do not relabel the computational replay as a source proof.
