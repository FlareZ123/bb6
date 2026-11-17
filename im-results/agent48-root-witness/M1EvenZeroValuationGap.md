# Next missing source row after the TM63 root middle-26 prefix

**Status:** root-path diagnosis plus finite-simulation hypothesis; not a proof and not Lean-compiled.

## Exact next state

The current root continuation TM63RootMiddle26.lean ends at
\[
s1Config\ L\ (16r-11)\ 0\ A\ 0\ B\ H,
\]
where \(r=tm63RootResidueSixK\). The root residue lemma
tm63_root_residue16_r_odd proves \(r\) odd.

The next five counted-increment source classes are already represented by existing theorems:

| Row | Input marker \(m\) | Input \(n\) | Source family |
|---:|---:|---:|---|
| 27 | 0 | \(16r-11=2(8r-6)+1\) | m0Odd_counted_increment_source_k |
| 28 | 2 | \(16r-12=8(2r-2)+4\) | m2Even_residue4_counted_increment_source |
| 29 | 1 | \(16r-13=8(2r-2)+3\) | m1OddResidueThree_counted_increment_source |
| 30 | 0 | \(16r-14=8(2r-2)+2\) | m0Even_residue2_counted_increment_source |
| 31 | 2 | \(16r-15\) (odd) | m2Odd_counted_increment_source |

After these rows the input is
\[
m=1,\qquad n=16r-16=32q,\qquad q=(r-1)/2.
\]
This is the first missing source class in the natural continuation. Existing M1-even sources cover residue \(8k+2\), \(8k+4\), and \(8k+6\) (the latter with \(v_2(n)=1\)); M1EvenQ4Prefix/Suffix is the base \(n=6\) case. There is no corresponding counted-increment theorem for \(m=1,n=32q\) in the current tree.

The required theorem has the shape
\[
\operatorname{run}\ tm2\ (\operatorname{proposedIncrementCost}\ 1\ n\ a\ b)\
(s1Config\ L\ n\ 1\ a\ 0\ b\ h)
=
\operatorname{some}(s1Config\ L\ (n-1)\ 0\ (a+b+2)\ 0\ (2^b-1)\ (h+5+3b)).
\]

## Finite-simulation hypothesis

Using the source transition table and S1 encoding, with \(a=1,b=0\), the deterministic simulator reached the same q4-prefix endpoint (state 4, head \(h+4\)) at the following times:

| \(n\) | \(v_2(n)\) | observed prefix length \(44+12a+12(v_2(n)-1)\) |
|---:|---:|---:|
| 6 | 1 | 56 |
| 32 | 5 | 104 |
| 64 | 6 | 116 |
| 96 | 5 | 104 |
| 128 | 7 | 128 |

For each tested \(n\), a further 35 steps (the \(b=0\) suffix) reached state 3 at head \(h+5\). This matches the \(b=0\) specialization of the proposed counted-increment cost. These are finite simulator observations only; they do not establish the arbitrary-\(q\), arbitrary-\(a,b\) theorem.

The likely proof target is a valuation-parametrized extension of the M1-even q4 prefix: the existing \(n=6\) prefix is followed by \(12(v_2(n)-1)\) additional steps before the same q4 suffix can be applied. The missing work is to identify and prove the reusable 12-step valuation bridge, with the unconsumed quotient tail treated parametrically. Do not infer that this bridge is already established merely from the sample runs.

## Root relevance

This row is a concrete blocker to extending the middle-26 source prefix through the next 16-row cycle. It is more directly root-relevant than adding another isolated residue theorem elsewhere. A successful general source theorem would also support a generic sectionResult composition rather than an ever-growing list of root wrappers.
