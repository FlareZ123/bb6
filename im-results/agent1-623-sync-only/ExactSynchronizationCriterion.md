# Exact residue criterion for full-rectangle synchronization in machine #623

**Status:** exact mathematical reduction for the carry transducers. The application to the authentic root is still an all-time residue-language problem.

This note replaces the 70-state synchronization DFA by four explicit modular inequalities.

## Setup

Read a word of ternary digit pairs from low to high,

[
w=((x_0,y_0),ldots,(x_{n-1},y_{n-1})),qquad nge2,
]

and put

[
M=3^n,qquad
X=sum_{i=0}^{n-1}x_i3^i,qquad
Y=sum_{i=0}^{n-1}y_i3^i.
]

Write ([z]_Min{0,ldots,M-1}) for the least nonnegative residue modulo (M).

The full left carry rectangle has arbitrary initial previous pair ((x_{-1},y_{-1})in{0,1,2}^2) and carries

[
a_0,b_0in[-2,2].
]

The full right rectangle has the same arbitrary previous pair, with

[
a_0in[-4,1],qquad b_0in[-2,2].
]

The transducer equations are exactly the ones used by the maintained #623 reset construction:

[
egin{array}{lll}
L:& a_{i+1}=leftlfloorrac{x_i-y_{i-1}+a_i}{3}ightfloor,&
b_{i+1}=leftlfloorrac{y_{i-1}+b_i}{3}ightfloor,\[2mm]
R:& a_{i+1}=leftlfloorrac{-x_i-x_{i-1}-y_{i-1}+a_i}{3}ightfloor,&
b_{i+1}=leftlfloorrac{x_{i-1}+y_{i-1}+b_i}{3}ightfloor.
end{array}
]

After the first symbol the previous pair is fixed by the input word, so synchronization of the full state is exactly synchronization of the two final carries.

## Closed forms

Telescoping the base-3 carries gives the following exact formulas.

For the left branch,

[
a_n
=y_{n-1}
+leftlfloor
rac{X-3Y+(a_0-y_{-1})}{M}
ightfloor,
]

[
b_n
=-y_{n-1}
+leftlfloor
rac{3Y+(y_{-1}+b_0)}{M}
ightfloor.
]

For the right branch,

[
a_n
=x_{n-1}+y_{n-1}
+leftlfloor
rac{-(4X+3Y)+(a_0-x_{-1}-y_{-1})}{M}
ightfloor,
]

[
b_n
=-(x_{n-1}+y_{n-1})
+leftlfloor
rac{3(X+Y)+(x_{-1}+y_{-1}+b_0)}{M}
ightfloor.
]

These identities follow by induction on the word length: multiply each carry equation by the appropriate power of 3 and sum. The last input digit contributes an integral multiple of (M) in exactly the displayed constant term.

## Interval lemma

If (A=Mq+r) with (0le r<M), and an unknown additive boundary term ranges over every integer in ([u,v]) with (v-u<M), then

[
leftlfloorrac{A+d}{M}ightfloor
quad(din[u,v])
]

is constant if and only if

[
-ule rle M-1-v.
]

This is immediate because the entire interval (r+[u,v]) must stay inside one quotient cell ([0,M-1]).

The four boundary ranges above are

[
a_0-y_{-1}in[-4,2],qquad
y_{-1}+b_0in[-2,4],
]

[
a_0-x_{-1}-y_{-1}in[-8,1],qquad
x_{-1}+y_{-1}+b_0in[-2,6],
]

and every integer in each interval is attained.

## Exact synchronization theorem

For every word of length (nge2), the **full left rectangle synchronizes if and only if**

[
oxed{4le [X-3Y]_Mle M-3}
]

and

[
oxed{2le [3Y]_Mle M-5}.
]

The **full right rectangle synchronizes if and only if**

[
oxed{2le [4X+3Y]_Mle M-8}
]

and

[
oxed{2le [3(X+Y)]_Mle M-7}.
]

For the right first carry, the interval lemma is first applied to
([-(4X+3Y)]_Min[8,M-2]); converting back to the positive residue gives the displayed interval ([2,M-8]).

Hence simultaneous full-rectangle synchronization is equivalent to **four scalar modular inequalities**, with no automaton state needed.

## Relation to the #623 coordinates

For a target S-window cut from the signed coordinates

[
X_{m global}=2g-gamma_s,qquad Y_{m global}=6q,
]

the first dangerous residue is the shifted block of

[
X_{m global}-3Y_{m global}
=2(g-9q)-gamma_s,
]

while the right dangerous residue is the shifted block of

[
4X_{m global}+3Y_{m global}
=2(4g+9q)-4gamma_s.
]

These are exactly the two predecessor residuals in the terminal-strip theorem.

The other two conditions,

[
3Y,qquad 3(X+Y),
]

are the scale and near-diagonal obstructions visible in the smaller recurrent SCCs of the 70-state DFA.

Thus the 70-state synchronization language has a direct arithmetic normal form: failure means that at least one of four shifted residues lies in a constant-size neighborhood of 0 modulo the window modulus.

## Current authentic-prefix margins

On the current source-faithful 9,968-transition replay, every correction-only S-window satisfies all four inequalities. The minimum distance from the respective forbidden boundary was:

- left dangerous residue ([X-3Y]_M): 10;
- left scale residue ([3Y]_M): 19;
- right dangerous residue ([4X+3Y]_M): 4;
- right near-diagonal residue ([3(X+Y)]_M): 16.

These are finite diagnostics only. They do show that the current prefix is not merely passing because of a state-numbering accident in the minimized DFA.

## Consequence for the all-time proof

The all-time synchronization problem is now an exact four-residue separation problem. In particular, the two terminal-dangerous conditions are no longer hidden behind a 70-state graph. This makes the circularity explicit:

- a terminal predecessor forces one of (g-9q) or (4g+9q) into a logarithmic strip;
- that makes the corresponding high shifted residue approach the forbidden modular boundary;
- proving the authentic S-window always synchronizes therefore requires precisely the kind of 3-adic separation already identified by the middle-block program.

The benefit is a substantial reduction in proof state: one can work directly with four integer residues rather than a synchronized-product automaton.
