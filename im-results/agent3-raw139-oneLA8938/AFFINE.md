# 8938: all-parameter growth recurrence (computational induction, not yet Lean-certified)

Exact table [7,8,11,21,14,13,17,16,2,11,19,24], slot F1 unknown. The final candidate-unclassified leaf of Agent48's E0=1LA parent. All-time nonhalting follows from the checked affine recurrence below, conditional only on correctness of the small Python/C++ verifier and mathematical interpretation; do not count this as an accepted Lean Cover yet.

At step 35,436,190 the machine is A scanning a blank at h=-5152 with entirely blank left ray. Right word starts with the six separator words in 8938-growth.json, interleaved with five powers of W=101110 of exponents (274,176,111,64,39). Each digit d in separator notation means 1^d 0. Include the scanned 0 before P0. The width-6 known prefix ends 4974 cells from h; width-18 ends 4986 cells from h. These lengths and the exact prefix were independently checked by primitive blank replay. Let F(n,t) denote this configuration with the five powers increased by n*(243,162,108,72,48) and arbitrary untouched right tail t.

**Result:** for every n>=0 and arbitrary tail, F(n,t) reaches F(n+1,t') after 76,853,158 + 42,613,560*n primitive transitions, without F1. Left ray remains blank; head moves left 4374 cells. The output tail t' consists of a fixed 576-cell word prepended to t. Thus induction on n proves nonhalting for every completion of F1.

Proof certificate: partition into tiles of width 6 (or independently 18) aligned at the current A scan. A tile transition exactly simulates within a tile until an exit, or A at offset zero, after at least one primitive step. Store known finite stacks as tile runs, each run length a+b*n. Left absent stack means infinite zeros; any read from the absent right stack is rejected. Each ordinary symbolic tile step uses a positive length for all n and either removes a constant unit run or subtracts 1 from a uniformly positive residual. A candidate pumping loop has identical control and run-label skeleton at both ends and constant per-run count differences delta. At loop iteration j all counts have form a+b*n+delta*j. For affine number of iterations M(n)=M0+M1*n, the minimum over n>=0 and 0<=j<M(n) is checked exactly by taking j=0 for delta>=0, and j=M(n)-1 for delta<0, then requiring nonnegative coefficient of n and appropriate constant. A removed run must have identically zero residual length throughout the domain. The verifier replays the entire finite loop with these guards and requires identical skeleton and exact delta update, establishing the loop by induction for every n. No sample or approximate guard is used. Tile transition costs sum exactly. A final exact prefix comparison proves the next family with arbitrary right extension. Tile orientation is physical left-to-right on both stacks; their order is nearest-first. The full symbolic traces completed with these statistics:

| Width | Ordinary symbolic steps | Inductively accelerated loops | Cost at n=0 | Coefficient |
| --- | ---: | ---: | ---: | ---: |
| 6 | 1,835,426 | 15,192 | 76,853,158 | 42,613,560 |
| 18 | 770,818 | 15,192 | 76,853,158 | 42,613,560 |

Reproduce (Python 3, C++17, no third-party dependencies):
```sh
python unpack_affine.py
g++ -O3 -std=c++17 seed8938.cpp -o /tmp/seed8938
/tmp/seed8938 >/tmp/seed8938.txt
python affine8938.py 6
python affine8938.py 18
python - 6 <<'PY'
import affine8938 as a
s=''.join(f'{v:0{a.W}b}'*n for v,n,b in a.initial())
assert open('/tmp/seed8938.txt').read().strip().startswith(s)
PY
```
Repeat last check with 18. Success prints SUCCESS and exact cost coefficients; check explicit successful output, not merely process exit status. Each trace is written as compressed JSON in /tmp/8938-affine-{width}.json.gz. These are deterministic generators, not an archive of the large traces. The seed checker scans the entire finite used left ray; the array bounds are checked during primitive replay. The arbitrary-tail recurrence needs no assumption about the right tail contents. No kernel claim until Lean replay/semantic transport accepted. Next: small verified block/run-length/affine guard checker and exact source Cover transport.
