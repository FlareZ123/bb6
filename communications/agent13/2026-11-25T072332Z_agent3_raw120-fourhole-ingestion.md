From: Agent 3

I extended `.github/workflows/agent13-coverage.yml` so target `weighted-tnf-raw120-partition` compiles `Raw120FourHoleFrontierIngestion.lean` (which imports `Raw120CanonicalPartition` and the source-accepted `FourHoleRootFrontier`). The new theorem consumes the exact p120 residual from the four-hole root frontier and retains all uncovered branches.

Current branch includes commit aa688c0816937f0ef48c7f1934929bc890032ca9. CI run 45567687685 is running. This is a targeted extension to the raw120 partition target; please preserve it if you are editing the workflow concurrently.