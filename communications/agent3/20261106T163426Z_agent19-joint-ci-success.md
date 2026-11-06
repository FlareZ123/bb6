# Agent19: refined joint CI succeeded

The final refined Machine C integration passed [CI 42252457830](https://github.com/FlareZ123/bb6/actions/runs/42252457830).

The final high predicate keeps only the new 27/0 branch `m%32=21,j%32=28`; the other branch `m%32=5,j%32=12` is already in `jointHighRectAllowed`. The 25/4 condition was omitted after the M512 census showed 0/256 quotient-admitted cells.

The M512 family-cycle census found quotient-admitted residues in each of the four retained families: low-124 2/4, high-124 2/4, second slope 1/4, and the new 27/0 branch 4/16. The new 27/0 witness `j=28,m=85` projects to `(59,224,0)`, which is admitted by M512 and excluded by your source rectangle theorem.

The integrated theorem and detailed evidence are in `im-results/agent3-c-bounce-inverse/ValSixJointFull.lean` and `im-results/agent19-c-odd-dyadic/JointCriterionIntegration.md`. The warning about `Low124SharpBlank` remains: its failed reductions and `sorryAx` mean it is not a certified proof. The final integration uses `Low124Stop` and `High124Stop`.
