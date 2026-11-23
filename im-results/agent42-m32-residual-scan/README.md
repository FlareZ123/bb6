# M32 new-pair / six-forced normalizer scan (exploratory)

## Question

The existing M32EightCellStrictness.lean proves that the eight residue
families
(0,13), (4,25), (8,5), (12,17), (16,29), (20,9), (24,21), (28,1)
are admitted by the prior highAllowed sieve but rejected by the M32 mask.
Does the recursive sixForcedExcluded conjunct reject the other sixteen
members of CCert.newHighPairs?

## Reproducible finite scan

For each listed residue pair (j0,m0), take lifts
j=j0+32a, m=m0+32b for 0≤a,b<32, discarding j<3 or m<2.
Set
k=2^(2m+2)*(j+3)-(j+3m+5), x=2j+3, and evaluate the exact
six-branch sixForcedNormalize recurrence from
im-results/agent11-c-low58/SixForcedNormalize.lean.
The gate order and transformations below are copied from that definition.
In particular, evenOddFourGate is (x+y+1)%8=4, not
(x+3*y+1)%8=4.

~~~js
const mod = (a,n) => ((a%n)+n)%n;

function normalize(x,y) {
  const path = [];
  for (let i=0; i<10000; i++) {
    let nx, ny, gate;
    if (mod(x,2n)===1n && mod(y,2n)===1n && y>=5n &&
        mod(x+y,4n)===0n && mod(x+y,16n)!==0n && x+y>=24n) {
      gate="O"; nx=(x+y-4n)/2n; ny=(x+3n*y-10n)/4n;
    } else if (mod(x,2n)===0n && mod(y,2n)===1n && y>=5n &&
        mod(x+y+1n,16n)===8n && x+y>=23n) {
      gate="S"; nx=(x+y-5n)/2n; ny=(x+3n*y-9n)/4n;
    } else if (y>=4n && mod(y,2n)===0n && mod(x+y,4n)===1n) {
      gate="A"; nx=x+y-2n; ny=(y-2n)/2n;
    } else if (y>=6n && mod(y,2n)===0n &&
        mod(x+y,8n)!==0n && mod(x+y,8n)!==7n) {
      gate="R"; nx=x+y-2n; ny=(y-2n)/2n;
    } else if (mod(x,16n)===5n && mod(y,16n)===10n &&
        mod(x+y+1n,256n)===192n) {
      gate="V"; nx=x+y-2n; ny=(y-2n)/2n;
    } else if (mod(x,2n)===0n && mod(y,2n)===1n && y>=5n &&
        mod(x+y+1n,8n)===4n) {
      gate="F"; nx=(x+y-5n)/2n; ny=(x+3n*y-9n)/4n;
    } else {
      return {
        path: path.join("→"),
        excluded: y>=5n && mod(y,2n)===1n &&
          (mod(x+y,4n)===1n || mod(x+y,4n)===2n)
      };
    }
    path.push(gate);
    x=nx; y=ny;
  }
  throw new Error("normalizer did not terminate");
}

const newHighPairs = [
 [0,13],[0,25],[1,28],[4,25],[4,29],[5,16],
 [8,1],[8,5],[9,4],[12,5],[12,17],[13,24],
 [16,9],[16,29],[17,12],[20,9],[20,13],[21,0],
 [24,17],[24,21],[25,20],[28,1],[28,21],[29,8]
];

for (const [j0,m0] of newHighPairs) {
  const paths = new Map();
  let valid=0, excludedCount=0;
  for (let a=0; a<32; a++) for (let b=0; b<32; b++) {
    const j=BigInt(j0+32*a), m=BigInt(m0+32*b);
    if (j<3n || m<2n) continue;
    const k=(1n<<(2n*m+2n))*(j+3n)-(j+3n*m+5n);
    const r=normalize(2n*j+3n,k);
    valid++;
    if (r.excluded) excludedCount++;
    paths.set(r.path,(paths.get(r.path)||0)+1);
  }
  console.log([j0,m0], {valid, excludedCount, paths:[...paths]});
}
~~~

## Observed partition

Across all valid lifts in the 32×32 scan, each residue pair had exactly one
normalizer path:

| Class | Eight residue pairs | Path | sixForcedExcluded |
|---|---|---|---|
| Existing eight-cell frontier | (0,13), (4,25), (8,5), (12,17), (16,29), (20,9), (24,21), (28,1) | stop immediately | false |
| Other j%4=0,m%4=1 cells | (0,25), (4,29), (8,1), (12,5), (16,9), (20,13), (24,17), (28,21) | R → O | true |
| j%4=1,m%4=0 cells | (1,28), (5,16), (9,4), (13,24), (17,12), (21,0), (25,20), (29,8) | R → R → A | true |

Here R is sixEvenRightGate, O is oddLowGate, and A is
evenAffineGate. The eight existing survivor cells were all 992 or 1024
valid lifts with no normalization step; the other sixteen were all 992 or
1024 valid lifts with the displayed fixed path and terminal exclusion.

The same 24-element set has a compact affine description modulo 32:
- STOP: j≡0 (mod4), m≡3j+13 (mod32);
- R→O: j≡0 (mod4), m≡j+25 (mod32);
- R→R→A: j≡1 (mod4), m≡31-3j (mod32).

Each line gives exactly eight pairs. This representation is convenient for
splitting the finite certificate and deriving the corresponding k residues.

For a direct residue proof, write the first two families as j=4r (all m equalities below are modulo 32):
- STOP has m≡12r+13, so k≡-(40r+44) (mod32) and
  x+k≡23 (mod32).
- R→O has m≡4r+25, so k≡-(16r+80) (mod32), i.e. k≡16
  for even r and k≡0 for odd r. After R, the four possible
  (x1 mod32,y1 mod16) pairs are (17,7),(9,15),(1,7),(25,15);
  each has x1+y1≡8 (mod16), and the O step yields
  (x2 mod4,y2 mod4)=(2,3).
For the third family write j=4r+1, m≡28-12r (mod32). Then
k≡-(90-32r)≡6 (mod32), x≡8r+5 (mod32). After R the
(x1 mod32,y1 mod16) pair is (8r+9,2); after the second R it is
(x2 mod16,y2 mod8)=(8r+9 mod16,0); A then yields
(x3 mod4,y3 mod4)=(3,3).

The same residue calculation gives the following representative terminal
states modulo the coordinates needed by the exclusion predicate. The
(x mod 32, k mod 32) column is independent of the chosen lift because
32 divides 2^(2m+2).

| Path class | Initial (x mod 32, k mod 32) values | Final (x mod 4, y mod 2, x+y mod 4) |
|---|---|---|
| STOP | (3,20), (11,12), (19,4), (27,28) | (3,0,3) |
| R → O | (3,16), (11,0), (19,16), (27,0) | (2,1,1) |
| R → R → A | (5,6), (13,6), (21,6), (29,6) | (3,1,2) |

The final tuples make the terminal test transparent: STOP has even y and
sum residue 3; R → O has odd y and sum residue 1; R → R → A has odd y and
sum residue 2.

This strongly suggests that the current eight-cell theorem is the exact
intersection of CCert.newHighPairs with the prior highAllowed sieve,
not merely a lower bound on that intersection.

## Fixed-step residue derivation

For m≥2, 32 divides 2^(2m+2), hence
k ≡ -(j+3m+5) (mod 32). Thus the initial residues
(x mod32,k mod32), with x=2j+3, are exactly those tabulated above.
The transformations in sixForcedNormalize then give the following
intermediate residues.

- STOP cells: x+k ≡ 23 (mod32), so x+k ≡ 7 (mod8). Here x is odd
  and k is even; oddLow/evenSeven/evenOddFour are false by parity,
  evenAffine is false because x+k ≡ 3 (mod4), sixEvenRight is false
  because x+k ≡ 7 (mod8), and valSix is false because x ≡ 3 (mod8).
  The normalizer stops with even k, so sixForcedExcluded is false.
- R → O cells: the four distinct initial pairs are
  (x mod32,k mod32)=(3,16),(11,0),(19,16),(27,0). After R,
  (x1 mod32,y1 mod16)=(17,7),(9,15),(1,7),(25,15), respectively.
  In every case x1,y1 are odd, x1+y1 ≡ 8 (mod16), and the
  odd-low gate applies. After O, (x2 mod4,y2 mod4)=(2,3);
  hence y2 is odd and x2+y2 ≡ 1 (mod4), so the terminal exclusion
  predicate is true.
- R → R → A cells: the four distinct initial pairs are
  (x mod32,k mod32)=(5,6),(13,6),(21,6),(29,6). After the first R,
  (x1 mod32,y1 mod16)=(9,2),(17,2),(25,2),(1,2). The second R
  applies in every case. After the second R,
  (x2 mod16,y2 mod8)=(9,0),(1,0),(9,0),(1,0). Thus evenAffine
  applies; after A, (x3 mod4,y3 mod4)=(3,3), so y3 is odd and
  x3+y3 ≡ 2 (mod4), making the terminal exclusion predicate true.

Terminal stop checks are also simple. In the R→O class the final
coordinates satisfy x even, y odd, and x+y ≡ 1 (mod 4): oddLow is
false by x-parity; evenSeven and evenOddFour would require x+y ≡ 3
(mod 4); evenAffine, sixEvenRight, and valSix require y even. In the
R→R→A class x,y are both odd and x+y ≡ 2 (mod 4): oddLow requires
sum 0 mod 4, evenSeven/evenOddFour require x even, and all even-y gates
are false. Thus the displayed R→O and R→R→A paths really terminate at
the stated excluded pairs, rather than merely passing through them.

The gate order at each stage is also controlled by the listed residues.
In both non-STOP classes the initial x is odd, y=k is even, and
x+y ≡ 3 (mod 4), so oddLow, evenSeven, and evenAffine are false; the
six-even-right gate is the first applicable gate because x+y ≡ 3
(mod 8). In the R→R→A class, after the first R the new x1 is odd,
y1 is even, and x1+y1 ≡ 3 (mod 4) and 3 (mod 8), so the second R
is again the first applicable gate. After that second R, x2 is odd,
y2 is even, and x2+y2 ≡ 1 (mod 4), so evenAffine is the first
applicable gate. In the R→O class, after the first R both coordinates
are odd and x1+y1 ≡ 8 (mod 16), so oddLow is the first applicable
gate.

The size guards (y≥4, y≥5, y≥6, and x+y thresholds) follow from
j≥3,m≥2 and the stop-k formula; the smallest initial k is already
370. The modular residues above determine the branch tests, while
the lower bounds ensure that the corresponding guards are enabled.

A Lean complement to sixForced_not_excluded_eight should split
CCert.newHighPairs into these three eight-element sets, unfold
sixForcedNormalize for at most three steps, and discharge the residue
conditions with omega. If formalized, this would show that exactly the
existing eight cells survive the prior six-forced criterion.

## Evidence boundary

This is an exploratory executable scan, not a Lean theorem. The scan is
reproducible and its gate definitions were checked against the source, but
the all-lifts claims above remain conjectural until the fixed-step modular
proof is added and kernel-checked. It does not change the global BB(6)
status.
