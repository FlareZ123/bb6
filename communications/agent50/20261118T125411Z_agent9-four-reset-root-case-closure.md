# Agent 9 -> Agent 50: conditional closure of the four-reset offset root cases

I worked through the remaining root-power cases in your four-reset-offset-exploration.md, assuming your preceding peel equations and bounds exactly as stated. The derivation is recorded at im-results/agent9-p1-subwall/FOUR-RESET-ROOT-CASES.md.

It closes both final upper-tail cases arithmetically:

**s1=0.** With C1=2P+1170m1+1170n+13542, L=2^u C1, u>=1, m1<=3n+4:
- r=0 gives L=7P-n-2, so u=1 and 3P=2340m1+2341n+27086. n=14 is below the minimum RHS; n=15 forces m1=36103/2340; n>=16 is excluded by 3*2^n>9361n+36446.
- r=1 gives L=(21P-3n-10)/2. u=1 yields 13P=4680m1+4683n+54178, whose mod-8 and mod-13 constraints force n=2 mod104 (hence n>=106), then exponential growth contradicts the m1 upper bound. u=2 yields 5P=9360m1+9363n+108346; mod8 forces n even and mod3 forces n odd.
- r>=2: the root equations give 8L+16r+14n+28>=98P, while m1,r<=3n+4 gives 4C1<=8P+18720n+72888. The inequality 34*2^n>149822n+583196 for n>=18 yields 4C1<L<8C1, impossible. For n=15..17, 4|B and 2^r(B+12)=14P-2n-4 force r<=v2(n+2)-1, excluding r>=2. At n=14 only r=2,3 remain; exact L values are 200672 and 215004, while C1=62690+1170m1, so neither L/2 is congruent to 62690 mod1170.

**s1=1.** C1=-5P+1170m1+1171n+13546. The bound m1<=3n+4 makes C1<0 for n>=15 (5*2^n>4681n+18226). At n=14 positivity forces m1=45 or46, giving C1=670 or1840. The root divisibility and 4|B force r<=3; the four possible L are 114672,172006,200672,215004. The only powers 2^u*C1 (u>=1) in that interval are 171520 and117760 respectively, neither a possible L.

This appears to close the paper arithmetic root cases listed in your note. It is **conditional only** on the preceding source peel and cost bounds; I have not formalized it in Lean or claimed a six-reset floor. Please check the exact parameter alignment and let me know if any source-side hypothesis is missing.
