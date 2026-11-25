"""Replace the 1LF bulk dense n-gram proof by separately checked compact summaries.

Use the exact original dense search output, same indices and partial tables.
No changes to generate.py or its earlier source-pinned consumers.
"""
from pathlib import Path
import tempfile

import generate_compact as base
import generate_greedy_compact as greedy
import generate_1lf

ROOT = Path(__file__).resolve().parent

def main():
    imports = []
    original_load = generate_1lf.load_audit

    def emit_compact(i, table, cert):
        k,n,L,R,S = cert.split()
        # Convert original dense edge masks to sparse encoding for wide_cert.
        edges = lambda v: "".join(f"{j}:{x}," for j,x in enumerate(v) if x!="0")
        d, original, projected = base.compress(f"{i} {k} {n} {edges(L)} {edges(R)} {S}")
        assert original[0] == int(n)
        old = f"Raw118Wide{i}"
        module = f"Raw60A1LFNGramM{i}"
        old_ns = f"BB6Coverage.Agent1BiDFAWide.M{i}"
        new_ns = f"BB6.Agent1Raw60A1LFNGramCompact.M{i}"
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            states, nedges = base.emit(i, table, *d, tmp)
            assert states <= projected
            for f in tmp.glob("*.lean"):
                source = f.read_text().replace(old_ns,new_ns).replace(old,module)
                (ROOT/f.name.replace(old,module)).write_text(source)
        imports.append(module)
        print("1LF-NGRAM",i,k,original,"compact",states,len(d[0])//2,len(d[1])//2,nedges,flush=True)
        return (f"abbrev p{i} : PartialMachine := {new_ns}.table\n"
                f"theorem never{i} (m : Machine) (hm : compatible p{i} m) : NeverHalts m := "
                f"{new_ns}.never m hm\n#print axioms never{i}")

    def load():
        audit = original_load()
        audit.emit_ngram = emit_compact
        return audit

    generate_1lf.load_audit = load
    base.generate = greedy.generate
    base.full_child("1LF")
    assert len(imports) == 17
    p = ROOT/"Raw60A1LFNGram.lean"
    p.write_text("".join(f"import {x}\n" for x in imports)+p.read_text())

if __name__ == "__main__":
    main()
