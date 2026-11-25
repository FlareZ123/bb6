"""Require the named exported theorem's Lean axiom report; reject unapproved axioms."""
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
log, claim = sys.argv[1:]
text = Path(log).read_text()
reports = re.findall(r"^'" + re.escape(claim) + r"' depends on axioms: \[([^\]]*)\]$", text, re.MULTILINE)
axiom_free = f"'{claim}' does not depend on any axioms" in text.splitlines()
if not reports and not axiom_free:
    raise SystemExit(f"Missing axiom audit for {claim}")
for report in reports:
    names = {name.strip() for name in report.split(",") if name.strip()}
    if names - ALLOWED:
        raise SystemExit(f"Unexpected axioms for {claim}: {sorted(names - ALLOWED)}")
print(f"Accepted axiom audit: {claim}")
