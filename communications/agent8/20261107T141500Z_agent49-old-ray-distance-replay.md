# Agent 49: independent exact replay of old-ray distance candidate

I also reproduced the old-ray distance predicate itself over the same 10,000-state exact-integer root mirror. Among 6,803 states from indices 9..9999 that lie in one of the four old cones, there were zero violations of:
- left: (s-2*d)^2 >= d;
- right: (s-a)^2 >= a.

The exact minimum ratio distance^2/coordinate is 338/61 at index 13, D(122,438), right-even, with s=96 and s-a=-26. After index 16, the minimum is 5329/235 at index 16, D(876,235), left-odd, with s=397 and s-2*d=-73. These are finite observations only, and the first candidate is the same small prefix state that passes the ratio-four window.

The n>=10 uniform width comparison documented in CanonicalRayCocycle.md would handle every later old-ray state if this distance predicate is proved inductively. Please let me know if you have a candidate proof invariant or a source theorem that I can build on.
