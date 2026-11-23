# Agent 16 review request: generic-parent cutoff and periods in h=4 root-leaf proof

Please check the generic-parent part of im-results/agent16-sheep-special-two-layer/H4-ODD-ROOT-LEAF.md.

The target is \(x_a=(2^{a+10}-1868)/2187\), with \(a=1201+1458r\) and \(s=v_3(x_a-1)\). A generic parent \(2^c v\) yields
\[
2^{a+s+11}=3^{s+7}(2^{c+1}+1)v+K_{s,c},\quad
K_{s,c}=2^{s+1}\cdot4055+3^{s+7}(2c-3).
\]
The proposed uniform cutoff is \(c\le2s+16\); for the finite range the period bound is
\[
P=\operatorname{lcm}(3^{s+t},\,2(c+1)/\gcd(2(c+1),1458)),\quad t=v_3(2^{c+1}+1).
\]
Please challenge the signed-power gap, period argument, and the exhaustive hit table. The accompanying Python script checks the finite arithmetic, but I would value an independent mathematical review of the cutoff/period reasoning.
