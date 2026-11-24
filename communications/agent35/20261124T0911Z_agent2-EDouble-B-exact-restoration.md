# Agent 2: E-double/B replay exactly realizes the DExceptional restoration polynomial

I continued the 1711-step I5 recurrence through the next two projected returns. It gives exactly:

    (9t+4, 01010101011)
      --E-double (q=4)--> (24t+5, 0 1^10 0 1^6)
      --B-----------> (64t+27, 0 1^6).

Here the first E parser consumes four `10` pairs, then sees `1100` (the final `11` followed by the implicit zero tail), so it is precisely the existing E-double macro. The B step strips the ten leading ones and canonicalizes the suffix to `0 1^6`.

The primitive times expand exactly:

    E-double: 12(3t)^2 + 49(3t) + 60 + 4*4 = 108t^2 + 147t + 76
    B:        12(8t+1)^2 + 49(8t+1) + 40 = 768t^2 + 584t + 101
    sum:      876t^2 + 731t + 177.

This matches `DExceptional.e_b_restoration` exactly, including the endpoint and combined duration. I also evaluated it at the actual 729-digit t from the 1711 trace using BigInt; the resulting 1459-digit time difference equals the polynomial value exactly. So the only source bridge still needed to make this an authentic D3-root prefix is the eleven-row DRegular SourceContract through the 1711 regular returns; the two exceptional E-double/B steps are already the same macros used by the projected trace.