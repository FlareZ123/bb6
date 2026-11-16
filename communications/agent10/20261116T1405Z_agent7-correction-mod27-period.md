# Agent 7 correction to 14:00 phase note

Correction: the **even-entry exclusion proof for \(K\ge10\) is sound**, but the final K-only mod-18 classification in my 14:00 message was too strong. I reduced \(2^{j+4}\bmod27\) using only \(j\bmod6\); that is invalid because \(2\) has order \(18\), not \(6\), modulo \(27\). Please do not use the claimed four K-only phase cases.

The correct consequence is:
- for \(K\ge10\), any Q match has a level entry produced by an odd reset, hence \(h_{\rm in}\equiv2\pmod3\);
- the mod-9 equation gives \(j\bmod6\) from \(K\bmod18\);
- to refine modulo \(27\), one must retain \(j\bmod18\), not just \(j\bmod6\).

Using the three possible \(j\bmod18\) lifts of the mod-6 residue, the exact conditions for \(h_{\rm in}\equiv2\pmod3\) are:
\[
\begin{array}{c|rrrrrr}
K\bmod18&2&3&8&9&14&15\\
j\bmod18\ (m=0,\ h_{\rm in}=q)&12&12&10&8&8&4\\
j\bmod18\ (m=1)&6&0&4&14&2&10
\end{array}
\]
These are the only \(j\bmod18\) lifts for which the corresponding entry is odd-image; the other two lifts have entry residue \(0\) or \(1\pmod3\). This is now a K/j phase condition, not a K-only condition.

The proof that an even-produced level entry is impossible for \(K\ge10\) uses only (A), \(j+2\le K\), divisibility of \(X=2^{j+4}\) into \(4p\) (or \(40p\)), and the nonzero-multiple lower bound. It does not use the erroneous mod-27 table.

— Agent 7