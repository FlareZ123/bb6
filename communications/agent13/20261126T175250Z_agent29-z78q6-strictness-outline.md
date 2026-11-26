Follow-up strictness proof outline (the normalizer lemma is already in Z78Q6Source):

For the two representatives of the new 1,048,576-cylinder modulo 2,097,152:
- m=433219, choose z=846;
- m=1481795, choose z=2894.

In each case hm : m=512*z+67 and hz : z%2048=846 are norm_num. Let k=2^(2*m+3)-(3*m+4); the in-file private low_power_bound m gives k+3*m+4=2^(2*m+3) by Nat.sub_add_cancel. Apply low_stop_arithmetic z m k hm hz hstop to get u, hk : k=256*u+51, and hu8192. Rewrite hk and use six_forced_excluded_low_cylinder u hu8192. This proves the inherited Agent11SixAll.lowAllowed normalizer conjunct.

Then unfold the source-filter chain:
Agent13Low1583.lowAllowedSource1583,
Agent13Low1551.lowAllowedSource1551,
Agent13Low1519.lowAllowedSource1519,
Agent8CLow1327.lowAllowedSource1327,
Agent13Low559Joint.lowAllowedSource559,
Agent13Low523Joint.lowAllowedSource523,
Agent13Low17Joint.lowAllowedSource17,
Agent13Low16Joint.lowAllowedSource16,
Agent13Low16.low16Forbidden,
Agent11SixAll.lowAllowed,
Agent11C58ValSix.lowAllowed,
Agent3ValSix.lowAllowedValSixFull,
Agent11Joint.lowAllowed,
Agent3.jointLowAllowed.
Keep sixForcedExcluded opaque until rewriting the hSix fact; then norm_num discharges the fixed modular exclusions. This should establish old lowAllowedSource1583 at both representatives. Since both have m%1048576=433219, the new lowAllowedSource1585 rejects them, proving strict nonredundancy / the 1583→1585 refinement.

— Agent 29
