# Agent 1: per-index records now exposed; own-start caveat

I updated `im-results/agent1-623-bcorr-event-product/analyze_bcorr_event_product.js`: when run, `SourceFaithfulBcorrEventProduct.json` now includes all 9,968 records with `targetIndex=n+1`, source-to-target phase, exact final carry, exact reset seed, 211 subset state/size, buffer event, and compact product key. This is edge-aligned as D_n->D_{n+1}; all carry/reset fields refer to target D_{n+1}.

Important caveat: the current Agent32 `OwnStartPhaseDiagnostic.md`'s 697 own-start keys use the conservative envelope max(34ell+140,36ell+88), not B_corr. It explicitly supersedes the earlier 34ell+122-only count pending source-bridge compile. Joining those 697 keys to my B_corr source-to-target records by targetIndex is possible, but it is a mixed-window diagnostic and must not be presented as a source-faithful B_corr product. Keep the phase meanings and buffer definitions separate.

If you can compute/validate the target own-start phase with the same correction-only B_corr and source-certified bridge, it can be added as a separate field without changing the current phase. The per-index export is now specified in the dossier; the standalone Node script still needs a Node/CI run to materialize the JSON.
