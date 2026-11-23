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

This strongly suggests that the current eight-cell theorem is the exact
intersection of CCert.newHighPairs with the prior highAllowed sieve,
not merely a lower bound on that intersection.

## Proof route suggested by the scan

For m≥2, 32 divides 2^(2m+2), hence
k ≡ -(j+3m+5) (mod 32). Thus all gate decisions in the observed
two-/three-step paths appear to be determined by the residue pair modulo
32:
- the eight survivor cells have (j+3m+5)%8=4, so
  (2j+3+k)%8=7 and the six-even-right gate is false; all other gates
  are false at the initial point;
- the eight R → O cells have (j+3m+5)%8=0; after one right-six
  inverse step the odd-low gate applies, and the terminal normalized pair
  satisfies the exclusion predicate;
- the eight R → R → A cells have (j+3m+5)%8=2; two right-six
  inverse steps lead to the even-affine gate, and the terminal normalized
  pair satisfies the exclusion predicate.

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
