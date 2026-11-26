"""Convert generated raw120 certificates to the verified sparse audit format.

Usage: python sparsify_generated.py SOURCE DEST PREFIX
Example: python sparsify_generated.py 1lb 1lb-sparse Raw120OneLB

Discovery is unchanged. Reuse the original generated Lean modules without
re-running enumerators, bank searches, or growth witness generation.
"""
import argparse
import ast
from pathlib import Path
import re
import shutil

FAR = re.compile(r"\.far (true|false) (\d+) ⟨0,(\[[\d, ]*\]),(\[[\d, ]*\]),(\[[\d, ]*\]),(\d+)⟩")
LATE = re.compile(r"(?m)^(\s*)exact (\S+\.lateChecked) (\d+) \(by decide\)$")

def codes(mask):
    return [i for i in range(mask.bit_length()) if mask & (1 << i)]

def sparse_far(match):
    _, _, _, left, right, _ = match.groups()
    lrows = [codes(x) for x in ast.literal_eval(left)]
    rrows = [codes(x) for x in ast.literal_eval(right)]
    return f"{match.group(0)} ⟨{lrows},{rrows}⟩"

def convert(text, checker):
    text, n = FAR.subn(sparse_far, text)
    assert len(re.findall(r"\.far (?:true|false) \d+ ", text)) == n, "unrecognized FAR literal"
    for old, new in [
        ("zipCheck", "sparseCheck"), ("zipQueryOK", "packedQueryOK"),
        ("certifiedZip", "certifiedSparse"), (": Audit", ": SparseAudit"),
        ("→ Audit", "→ SparseAudit"), ("byMove ", "byMoveS "),
    ]:
        text = text.replace(old, new)
    text = LATE.sub(lambda m: (
        f"{m[1]}exact lateZip_sparse _ _ _ _ ({m[2]} {m[3]} (by decide))"
    ), text)
    imports = "import SparseLateBridge\n"
    if checker != "sparse":
        namespace, theorem = (
            ("DirectAudit", "directCheck_sparse") if checker == "direct"
            else ("PrefixAudit", "prefixRoot_sparse")
        )
        imports += f"import {namespace}\n"
        text = re.sub(
            r"(?m)^(theorem \w+ : sparseCheck (\d+) (\w+) (\w+) = true :=) by decide$",
            lambda m: f"{m[1]}\n  BB6.Agent3{namespace}.{theorem} {m[2]} {m[3]} {m[4]} (by decide)",
            text,
        )
    text = imports + text
    text = re.sub(r"(?m)^(namespace [^\n]+)$",
                  r"\1\nopen BB6.Agent3SparseAudit BB6Coverage.Agent13PackedZipper", text, count=1)
    return text, n

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source", type=Path)
    ap.add_argument("dest", type=Path)
    ap.add_argument("prefix")
    ap.add_argument("--checker", choices=["sparse", "direct", "prefix"], default="prefix")
    args = ap.parse_args()
    src, dst, prefix = args.source, args.dest, args.prefix
    assert src.resolve() != dst.resolve()
    assert not dst.exists(), "destination must be new"
    roots = {prefix + "Base.lean", prefix + "Data.lean"}
    roots.update(prefix + f"Kid{i:02d}.lean" for i in range(24))
    assert roots <= {p.name for p in src.glob("*.lean")}, "missing generated root/child modules"
    dst.mkdir(parents=True)
    count = 0
    for p in src.glob("*.lean"):
        if p.name in roots:
            out, n = convert(p.read_text(encoding="utf-8"), args.checker)
            (dst / p.name).write_text(out, encoding="utf-8")
            count += n
        else:
            shutil.copyfile(p, dst / p.name)
    print(f"Converted {len(roots)} audit modules and {count} FAR literals")

if __name__ == "__main__":
    main()
