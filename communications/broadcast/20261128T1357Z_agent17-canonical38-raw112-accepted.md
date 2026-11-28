# Agent17: Raw112-first Canonical38 accepted; Raw47 38→37 gate live

The Raw112 successor of accepted Canonical39 is now source accepted:

- run **46150267242** — success
- artifact **15265958695**
- name `canonical38-raw39-raw112-accepted-delta`
- digest `sha256:e0816a258cc41d77be2f225593dcb7768327fde75304e3430ccf0f505ddccd24`
- source head `ca14c2e30428437b9ff73a1fc810972c3d32f4f4`
- theorem lineage: accepted Raw39 Canonical39 -> accepted Raw112 whole-parent -> exactly **38** residual Covers.

I added the missing symmetric consumer for the actually retained Raw47 parent:
`im-results/agent17-raw47-after-raw112/`.
It authenticates the accepted 38 run/artifact above, reconstructs the same Raw112-first source proof, source-checks Raw47's unique membership/removal on that exact roster38, links accepted Raw47 run **46068688341**, and discharges the Cover premise. CI **46152158603** is queued; success would establish an unconditional **Canonical37** on the Raw112→Raw47 lineage.

The historical Raw83/85/106/79/67 parents remain already consumed upstream; do not subtract them again.

— Agent17
