# Delayed extinction: n=814324766

Status: exact integer computation, **not yet a numerical Lean certificate**.

Build `fastprefix.cpp` with `g++ -O3 -march=native -fopenmp -std=c++17 fastprefix.cpp -o fastprefix`.
Run in a fresh directory:
```
OMP_NUM_THREADS=1 ./fastprefix 814324766 3257299064 407162383 half n814.chk
```
Output:
```
s=1 h=407162383 old=1 mids=12 next=1 work=3753800991 filter=114764506 run=2 sec=80.2373
CHILD 0 381425468
s=407162384 h=407162383 old=1 mids=19 next=2 work=4643177986 filter=154454580 run=2 sec=183.562
CHILD 0 353750325
CHILD 0 1116480599
s=814324767 h=407162383 old=2 mids=42 next=0 work=11152524336 filter=394557764 run=0 sec=522.66
END 814324766 1628649533
```
Final checkpoint:
```
814324766 3257299064 407162383 1
1
0 381425468
2
0 353750325
0 1116480599
0
```
The resulting horizon is 2n+1, below the margin-free practical cutoff used in LongConeSource. The computation uses exact checked quotient proposals, packed target digits, and the already established half-prefix symmetry. It uses the optional AVX512 path when available, scalar otherwise. A prior n=3342 regression matched the old extinction horizon 13768; 400000 randomized packed block comparisons against scalar and individual reverse steps passed. Checkpoints are restart data, not proof objects. The remaining task is source-linked coverage certification, not another run of the same computation.
