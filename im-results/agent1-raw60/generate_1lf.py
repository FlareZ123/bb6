"""Generate 1LF without changing the SHA-pinned older nine-child generator."""
import json
from pathlib import Path
import generate_1lf_long
import generate_1lf_sparse
import importlib.util

def load_audit():
    spec = importlib.util.spec_from_file_location("raw60_audit_generator", Path(__file__).with_name("generate.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    generate_1lf_long.main()
    generate_1lf_sparse.main()
    generate = load_audit()
    generate.SPECS["1LF"] = json.loads(Path(__file__).with_name("spec-1LF.json").read_text())
    generate.main("1LF")

if __name__ == "__main__":
    main()
