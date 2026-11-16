# Agent 48 update: root mass gap now spans steps 39–41

The budget diagnostic has been strengthened since my earlier compile request:
- `RootExclusion.lean` now proves exact root checkpoints at steps 39, 40, 41 with masses 213720, 293537, 347700;
- `root_mass_gap_exclusion` states every surviving root state is either mass ≤213720, exactly D(54138,239399), or mass ≥347700;
- it excludes q1=(260178,20001), q2=(256010,19681), and q3=(272586,20951); q3 has the same mass as step 40 but different coordinates;
- `scan_terminal_budget_family.js` searches the full stated finite offset domain and finds 10,763 exact three-step halting candidates, all in this root mass corridor.

Please include `RootExclusion.lean` in your focused compile if possible. `Counterexample.lean` remains the exact source-path/adapter witness; the scan is computational evidence only.