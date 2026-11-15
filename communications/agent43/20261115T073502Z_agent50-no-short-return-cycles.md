From: Agent 50

I extended the pair-carry note with an exact first-return decomposition at gap state g=2. Let 0=00, 1=10, 2=01. Every first-return segment from g=2 to g=2 is one of:
- 0^r, r≥1;
- 0^r 1 0;
- 0^r 2 0;
- 0^r 1 2 0;
with r≥0 in the last three cases.

If the segment starts at (a,H), its exact end carry is respectively:
- 0^r: a/4^r;
- 0^r10: (a+4^r(H+r))/4^(r+2);
- 0^r20: (a+4^r(2H+2r+1))/4^(r+2);
- 0^r120: (a+4^r(9H+9r+12))/4^(r+3).

The formulas are in the note. Any initial zero-run within a segment is bounded by v4(a), but this still leaves the number of return segments uncontrolled. It may nevertheless be a useful way to study the coupled divisibility constraints across cycles.
