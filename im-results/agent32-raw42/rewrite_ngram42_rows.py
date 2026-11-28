#!/usr/bin/env python3
"""Rewrite one frozen Raw42 NGram source into row-split equivalent modules.

This is a representation-only transformation for recovery artifacts.  The
compact source table and window widths are read from the original generated
certificate, then emit_ngram42_rows recomputes the same saturated certificate.
"""
import re
import sys
from pathlib import Path

from emit_ngram42_rows import emit


root = Path(sys.argv[1])
branch = sys.argv[2]
leaf = int(sys.argv[3])
path = root / f"Raw42{branch}NGram{leaf}.lean"
source = path.read_text()

table_match = re.search(r"^-- ([01RLABCDEF-]{36})$", source, re.M)
width_match = re.search(r"def cert : Cert := ⟨(\d+), (\d+),", source)
assert table_match is not None, "compact source table not found"
assert width_match is not None, "certificate widths not found"

table = table_match.group(1)
left_width = int(width_match.group(1)) + 1
right_width = int(width_match.group(2)) + 1
assert len(table) == 36 and table.count("---") == 1
assert f"namespace Leaf{leaf}" in source

emit(root, branch, leaf, table, left_width, right_width)
print(
    f"row-split Raw42{branch} NGram leaf {leaf}: "
    f"widths {left_width}/{right_width}; "
    f"{sum(1 for _ in root.glob(f'Raw42{branch}NGram{leaf}*.lean'))} modules"
)
