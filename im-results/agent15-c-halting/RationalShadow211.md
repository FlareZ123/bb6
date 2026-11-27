# U5 rational negative-shadow inverse certificate

For the U5 terminal ancestor X=(44t-1,42t-1), the exact identity 211t+1360+22155w=20*2^(201+3360w) gives 211X.x+Sx=880*2^E and 211X.y+Sy=840*2^E, where E=201+3360w and S=(44(1360+22155w)+211,42(1360+22155w)+211). The shadow coordinates are positive numerators of negative rational offsets with denominator 211. No huge positive counter is constructed.

The checker carries a 2-adic precision b and applies all source predecessor branches. For the direct branch it charges one bit; for a high inverse indexed n it charges n+2 bits. Its smallness guard 212(Sx+Sy+1688)<2^b ensures that a congruent actual pair has x>5,y>=8 and that its parity-corrected sum is not a pure power of two. Leaf rejection uses the exact source odd-image theorem. check_sound and u5_congruent typechecked locally against abstract source-signature stubs; original-source composition u5_shadow_x_excluded passed run 45919404521. No stub is committed.

Independent iterative evaluator u5_negative_shadow.py explores the same arithmetic tree, using the exact stronger smallness guard, with a one-million-node per-w cap. In 0<=w<10000, 9995 trees completed with adequate precision. Five reached the node cap: 3141,3361,4081,6097,6465. No budget failure occurred among this finite sample. Largest completed tree: 678709 nodes; maximum completed depth 2735; maximum required precision 5526. Counts are exploratory, not formal finite-prefix theorems. The arithmetic checker theorem is conditional on Boolean acceptance; a universal termination/precision bound remains unproved. The five capped trees are unresolved by this computation, not evidence for actual reachability.

Follow-up: all five previously capped trees finish with the optimized C++ evaluator (uint64_t exact for these bounded inputs; maximum intermediate coordinates <19 billion). Reproducible output (w,nodes,required bits,depth):

```
3141 1544875 8628 4286
3361 2045158 13722 6672
4081 161798137 49060 24724
6097 9059331 18791 9354
6465 5738061 10479 5241
```

Hence the entire finite prefix 0<=w<10000 has computational shadow-tree certificates within its exact precision budget. This is not a kernel-reflected finite-prefix proof, and not an unbounded theorem. Original-source rational kernel job 45919404521 succeeded. New residue-cylinder theorem lifts one finite shadow check at precision b to all w congruent to z modulo 2^b with b<=201+3360w. The proof remains conditional on checker success; The complete source closure, including cylinder transfer and original high-stop lift, passed [run 45919729244](https://github.com/FlareZ123/bb6/actions/runs/45919729244) at deeab8507f7dc45a7c29cd95bfad5e9614197cc1.
