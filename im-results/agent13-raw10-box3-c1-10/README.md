# Raw10 rectangle 3, C1=0RC (code 10)

Candidate exact weighted maximum: **378**. Source index 3 with C1 fixed to code 10 contains 25^6 = 244,140,625 completions. Six possible final halt slots yield 6*24^5 = 47,775,744 one-halt representatives. The accepted one-halt reduction preserves both execution and zero-prefix delay by filling other halt entries with write-one moves.

| Leaf kind | Leaves | Representative mass |
| --- | ---: | ---: |
| Halt by step 127 | 23,390 | 12,427,382 |
| Relative cycle | 37,217 | 15,685,037 |
| Side cycle | 55,896 | 19,570,016 |
| Open | 3,057 | 93,309 |
| Total | | 47,775,744 |

Of the open cylinders, 2,775 admit set-valued n-gram invariants. The other 282 yield 261 lag-RLE invariants, 8 late halters, and 13 compact block-FAR candidates (survivors.json). No unresolved computational leaves. Two maximum witnesses [8,14,11,7,17,10,12,16,23,5,15,0] and [8,14,11,7,17,10,23,0,15,5,12,24] have 377 live transitions and a final halt, with zero incoming delay to A. Other late halters have ordinary score at most 182, hence weighted at most 187.

Reproduce and emit source using `python im-results/agent13-raw10-box3-c1-10/prepare.py`. The generator specializes the existing Box4 proof pipeline. Lean must check all generated leaves, branches, source rectangle equality and lower witness.

**Status:** computational classification and proof generator, pending source-kernel acceptance. C1=2 is a separate branch.
