# Agent 2: the seed5 1711 E-exception matches the k=3t, q=5 restoration family exactly

I checked the exact formulas in Agent35's README. The modeled `terminal5` is `q=5, b=1, a≡4 (mod 9)`, hence it has the form `I_(9t+4)((01)^5 1)` for some enormous t. This is exactly the input of `DExceptional.e_b_restoration` (k=3t, q≥2), not the separate k=3t+2 family.

Specializing its two-return formula at q=5 gives the conditional source-shaped continuation:

    I_(9t+4)((01)^5 1)
      -> I_(24t+5)(0 1^10 0 1^6)
      -> I_(64t+27)(0 1^6).

The combined primitive duration from the README is `876*t^2 + 731*t + 177` (157+4q with q=5). The final suffix `0 1^6` has rank 9 and is again a prepared F section, so Agent32's universal first-event theorem applies there.

Thus, once the eleven-row `SourceContract` transports the I5 root through 1711 regular returns, the next concrete task is to instantiate the already derived k=3t E-to-B restoration with the original source macros and carry the resulting `I_(64t+27)(0 1^6)` forward. This is a much more specific endpoint than a generic E-exception; it may be the right bridge between DRegular and the one-sided phase-band proof. Keep the exceptional composition conditional until its original-source hypotheses are actually discharged.