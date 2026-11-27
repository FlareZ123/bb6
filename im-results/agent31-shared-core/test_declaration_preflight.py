"""Actual Lean fixtures; run with the pinned lean on PATH."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from declaration_preflight import audit_linked_roots

LEAN = os.environ.get("LEAN", "lean")


class DeclarationPreflightTest(unittest.TestCase):
    def test_actual_module_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixtures = {
                "A": "namespace Shared\ndef witness : Nat := 1\ntheorem eq0 : 0 = 0 := rfl\nend Shared\n",
                "B": "namespace Shared\ndef witness : Nat := 2\ntheorem eq0 : 0 = 0 := rfl\nend Shared\n",
                "C": "namespace Shared\ntheorem eq0 : 0 = 0 := rfl\nend Shared\n",
                "D": "namespace Shared\ntheorem eq0 : 1 = 1 := rfl\nend Shared\n",
                "Transitive": "import B\n",
            }
            for name, text in fixtures.items():
                (root / f"{name}.lean").write_text(text)
                subprocess.run([LEAN, "-o", f"{name}.olean", f"{name}.lean"], cwd=root,
                               env=dict(os.environ, LEAN_PATH=str(root)), check=True)
            def audit(*roots):
                # Tiny limit exercises cross-batch declaration tracking.
                return audit_linked_roots(root, roots, lean=LEAN, batch_bytes=1)
            compatible = audit("A", "C")
            self.assertEqual(compatible["status"], "import_passed")
            self.assertEqual(compatible["module_count"], 2)  # B exists but is unreachable.
            self.assertEqual(compatible["requires_import_check_count"], 1)
            collision = audit("A", "B")
            self.assertEqual(collision["status"], "definite_conflict")
            self.assertEqual(collision["definite_conflict_count"], 1)
            self.assertEqual(collision["smoke"]["status"], "not_run")
            differing_type = audit("A", "D")
            self.assertEqual(differing_type["status"], "import_failed")
            self.assertIn("Shared.eq0", differing_type["smoke"]["output"])
            transitive = audit("A", "Transitive")
            self.assertEqual(transitive["status"], "definite_conflict")
            row = next(r for r in transitive["overlaps"] if r["name"] == "Shared.witness")
            self.assertEqual([o["module"] for o in row["owners"]], ["A.olean", "B.olean"])
            self.assertEqual(row["owners"][1]["families"], [{"label": "Transitive", "roots": ["Transitive"]}])
            repeated = audit("A", "A")
            self.assertEqual(repeated["status"], "import_passed")
            self.assertEqual(repeated["module_count"], 1)
            self.assertEqual(repeated["overlaps"], [])


if __name__ == "__main__":
    unittest.main()
