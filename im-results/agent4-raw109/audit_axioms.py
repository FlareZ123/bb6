#!/usr/bin/env python3
"""Require named theorem axiom profiles and disallow unapproved assumptions."""
from pathlib import Path
import re
import sys

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
log = Path(sys.argv[1]).read_text()
profiles = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    profiles[name] = {a.strip() for a in axioms.split(',') if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    profiles[name] = set()
if re.search(r'\bsorryAx\b|\bnative_decide\b', log):
    raise SystemExit("Forbidden axiom/oracle in source audit")
for name, axioms in profiles.items():
    if axioms - allowed:
        raise SystemExit(f"{name}: unapproved axioms {sorted(axioms - allowed)}")
for name in sys.argv[2:]:
    if name not in profiles:
        raise SystemExit(f"Missing axiom profile: {name}")
    print(f"{name}: {sorted(profiles[name])}")
