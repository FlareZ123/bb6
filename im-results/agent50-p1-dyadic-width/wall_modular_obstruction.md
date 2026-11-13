# Wall modular obstruction

**Agent 50 — 2026-11-13**

Status: the modular reduction and mod-16 restriction below are exact consequences of the source-wall identity. The stronger shallow-gap statement is an experimental conjecture, not a theorem.

## Exact reduction

Use the notation of [wall_cost_telescoping.md](wall_cost_telescoping.md). Let inverse-edge costs be e_i=t_i+1, with cumulative costs s_0=0, s_{i+1}=s_i+e_i, and terminal cost s_k=m. Put

- S = sum_{i<k} 2^{s_i},
- T = sum_{i<k} s_i 2^{s_i},
- P = 2^n.

The exact wall identity is

    P(7S - 2^m) = 2^m(m+n+3) + (n+3)S + T - 1.    (W)

Folding the terminal term into the sum gives

    sum_{i=0}^k (n+3+s_i) 2^{s_i} = 1  (mod 2^n).    (M)

This removes all machine/source details from the first 2-adic obstruction: only the cumulative edge costs remain.

## Proven consequence: n = 2 or 14 (mod 16)

Assume n>=14 and a source path reaches the wall. Write N=7S-2^m. By (W), N>0; also N=-2^m (mod 7), so N>=3. The case m=0 is immediately impossible from (W). For 1<=m<=3, S<=2^m-1 and T<=(m-1)S, hence

    P N < 2^m(2m+2n+5) <= 8(2n+11) < 3*2^n,

contradicting P N>=3P. Therefore m>=4.

Reduce (W) modulo 16. Since n>=14 and m>=4, both P and 2^m vanish modulo 16, leaving

    (n+3)S + T = 1  (mod 16).

Let x_j indicate whether j occurs among the cumulative costs, for j=1,2,3. All starts >=4 vanish modulo 16, so

    n+3 + 2(n+4)x_1 + 4(n+5)x_2 + 8(n+6)x_3 = 1  (mod 16).

Checking the 16 residues leaves exactly:

- n = 2 (mod 16), with (x_1,x_2)=(1,0) or (0,1);
- n = 14 (mod 16), with x_1=x_2.

All other residues are impossible. Thus a wall-reaching source path can exist only if n=2 or 14 (mod 16). This conclusion is independent of any depth cap. For n=2 (mod 16), the first edge is necessarily shallow (cost 1 or 2).

## Stronger target: an unrestricted six-shallow obstruction

Let A_n be the cumulative costs s_i that are below n. Equation (M) gives

    sum_{s in A_n} (n+3+s) 2^s = 1  (mod 2^n).    (C)

Every adjacent gap in the sorted set A_n is an actual inverse-edge cost. A gap of 1 or 2 is exactly a shallow edge (depth 0 or 1). The following purely combinatorial lemma would therefore imply that every source path to the wall has at least six shallow edges, without restricting intervening high-depth edges:

> For every n>=14, every finite A subset of {0,...,n-1} containing 0 and satisfying (C) has at least six adjacent gaps equal to 1 or 2.

I do not yet have an unbounded proof of this lemma.

### Exact carry dynamic programme (experimental evidence)

For x_s=1 iff s is in A, the congruence is

    sum_{s=0}^{n-1} x_s(n+3+s)2^s = 1  (mod 2^n), with x_0=1.

After processing bit j, let c be the carry and let a be the distance from the previous selected position minus one, capped at 2. Initially, for even n, (c,a)=((n+2)/2,0); odd n is immediately impossible. At bit j>=1, put C_j=n+3+j. The exact transitions are:

- omit j if c is even: (c,a) -> (c/2, min(2,a+1));
- select j if c+C_j is even: (c,a) -> ((c+C_j)/2,0), adding one to the short-gap count iff a<=1.

Keeping the minimum short-gap count for each state enumerates all subsets without storing them. The JavaScript implementation used for the scan is below.

The exact scan for 14<=n<=10000 found a nonempty terminal state only at:

| n | minimum adjacent gaps 1 or 2 |
|---:|---:|
| 30 | 8 |
| 286 | 88 |
| 350 | 112 |
| 1614 | 563 |
| 2990 | 1068 |
| 3342 | 1145 |

For all other tested n, the carry-state set became empty. This is computational evidence only, not a proof for all n. The strong gap counts make the unrestricted six-shallow lemma a promising target.

```javascript
function minimumShortGaps(n) {
  if (n % 2 !== 0) return null;
  // After the forced bit x_0=1, c=(n+2)/2 and a=0.
  let states = new Map([[String((n + 2) / 2) + ",0", 0]]);
  const putMin = (map, key, value) => {
    const old = map.get(key);
    if (old === undefined || value < old) map.set(key, value);
  };
  for (let j = 1; j < n; j++) {
    const C = n + 3 + j;
    const next = new Map();
    for (const [key, cost] of states) {
      const comma = key.indexOf(",");
      const c = Number(key.slice(0, comma));
      const a = Number(key.slice(comma + 1));
      if (c % 2 === 0) {
        putMin(next, String(c / 2) + "," + String(Math.min(2, a + 1)), cost);
      }
      if ((c + C) % 2 === 0) {
        const add = a <= 1 ? 1 : 0;
        putMin(next, String((c + C) / 2) + ",0", cost + add);
      }
    }
    states = next;
    if (states.size === 0) return null;
  }
  return Math.min(...states.values());
}

const hits = [];
for (let n = 14; n <= 10000; n++) {
  const minimum = minimumShortGaps(n);
  if (minimum !== null) hits.push({ n, minimum });
}
console.log(hits);
```

## Next mathematical step

Prove or refute the unrestricted six-shallow lemma. If true, formalize (M) and the carry invariant in Lean, then compose it with the existing source low-trace wall theorem. Do not promote the DP observation itself to results/.