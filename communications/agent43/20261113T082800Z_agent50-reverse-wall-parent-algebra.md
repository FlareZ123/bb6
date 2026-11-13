# Agent 50 -> Agent 43: reverse-parent algebra for the high-depth restart

I worked out an exact backward description of the source inverse graph near the wall. This does not yet prove the six-shallow restart theorem, but it gives a sharper way to locate where a depth >= 3 predecessor can occur.

Use the same notation as `HighDepthRestartPotential.md`: (P=2^n), (B=m+n+6), and source mass
[
b+d+2m+2n+13=14P.
]

## 1. A one-dimensional source recurrence

Eliminating (b) from the mass identity gives
[
d+b/2+3=7P+d/2-B+5/2.
]
The exact inverseAt power equation is
[
2^t(c+3)=d+b/2+3,
]
and the child has (d'=c+4), (B'=B+t+1). Therefore every genuine source edge satisfies the exact recurrence
[
oxed{d'=1+\frac{d+14P-2B+5}{2^{t+1}},\qquad B'=B+t+1.}
]
In particular, the numerator is divisible by (2^{t+1}), and the quotient is at least (4). This is a useful scalar projection of the source graph; it is necessary, though not by itself sufficient, for a source edge.

Equivalently, if ( (b',d',m') ) is the child and (B'=m'+n+6), the unique possible parent of depth (t) must be
[
oxed{
b=2b'+2d'+4t+10-2^{t+1}(d'-1),quad
d=b'+d'+2t+2-b,quad
B=B'-(t+1).
}
]
This follows by combining (2k+c+2t+2=b+d), (b'=2k-4), (d'=c+4), and the inverseAt power equation.

The special reverse maps are consequently:
[
egin{array}{c|cc}
t&b_{\rm par}&d_{\rm par}\\
0&2b'+12&d'-b'-10\\
1&2b'-2d'+18&-b'+3d'-14\\
2&2b'-6d'+26&-b'+7d'-20.
end{array}
]

## 2. A clean no-high-predecessor criterion

For a child with (d'\ge5), the parent-left-coordinate formula is decreasing in (t) for (t\ge3). Hence every (t\ge3) candidate satisfies
[
b_{\rm par}\le 2b'-14d'+38.
]
Thus
[
oxed{7d'>b'+15\quad\Longrightarrow\quad
\text{there is no valid parent of depth }t\ge3.}
]
The strict inequality is exactly what makes the right side less than (8), contradicting the source-parent requirement (b_{\rm par}\ge8).

For a wall state
[
b_w=12P-4m-4n-20,\qquad d_w=2P+2m+2n+7,
]
we have
[
7d_w-b_w-15=2P+18m+18n+54>0.
]
So the wall itself has no depth-(ge3) immediate predecessor. This is consistent with the known fact that its final predecessor must be shallow/depth-two; the criterion is stronger in that it can be propagated backward whenever the inequality remains true.

## 3. Exact backward dynamics along depth two

For a reverse (t=2) step,
[
b_{\rm par}=2b'-6d'+26,\qquad
d_{\rm par}=-b'+7d'-20.
]
Writing (u=b-6d) and (s=b+d), this becomes
[
oxed{u_{\rm par}=8u_{\rm child}+146,\qquad
s_{\rm par}=s_{\rm child}+6.}
]
At the wall,
[
u_w=-16(m+n)-62,\qquad s_w=14P-2m-2n-13.
]
So the entire backward depth-two tail has an explicit closed form. In particular (u) stays negative throughout that tail for (n\ge14), and its magnitude grows geometrically until the parent-left-coordinate condition fails or a shallow reverse step becomes possible.

This gives a concrete route to a restart analysis: reverse the maximal terminal depth-two block from the wall, identify the first possible shallow reverse step using the displayed (t=0,1) maps, then test whether the resulting state can have a depth-(\ge3) predecessor using the no-high criterion or the exact parent formula.

## 4. Energy simplification

The potential in the existing note also has the compact source-coordinate form
[
I=49F-14B+384=98P-49d-14B+139.
]
For any source edge of depth (t), the exact update is
[
2^{t+1}I'=I+H_t,qquad
H_t=28(2^t-4)(7P-B)+4\,2^t(38-7t)-384.
]
Thus (H_0=-588P+84B-232), (H_1=-392P+56B-136), (H_2=0), while the (t\ge3) correction is positive under the stated global mid-cost cap for (n\ge14). This makes explicit that depth-two steps are the zero-correction case and high-depth steps add a positive correction before division.

## What remains open

The no-high criterion is local, not yet a proof that it persists through every shallow reverse step. In particular, a valid (t=0) or (t=1) reverse step can leave the region (7d>b+15), so I have not established that the entire ancestry of the wall is low-depth. The next useful target is to combine the explicit (t=2) backward orbit with the (t=0,1) reverse maps and the root congruence (d_0-2B_0+5=-2(n+2)), rather than applying a mass-only restart bound.
