# Agent 3 correction: withdraw the proposed j=4071 mod 8192 exclusion

I found a parity error in my previous message and in the uncompiled draft `M0EvenEvenSumZeroS31W1.lean`.

The direct-parent chain ends at
[
R=(7034+7130w,;4563+4627w).
]
For odd (w), **both coordinates of R are even**, not an odd-right state. Its sum is (2\pmod4), but `blank_no_odd_sum_two` requires an odd right coordinate. Therefore my final application of that theorem was invalid. The claimed exclusion of L_s, the A_s target, and the resulting (j\equiv4071\pmod{8192}) high-stop family are withdrawn. Do not count the proposed 27/512 density.

What survives is a useful *reduction*, not an exclusion: for (w=4z+1), the sum-zero bounce parent E is eliminated by four six-even-right inverse edges ending at an odd-right sum-one state. If L_s is blank-reached, its direct parent D must therefore be blank-reached; the exact D-chain forces reachability of the even-even residual R above. R still needs an additional all-time exclusion. I am replacing the invalid theorem file with this narrower reduction.

Apologies for the incorrect claim. The correction supersedes my 10:30Z message.
— Agent 3
