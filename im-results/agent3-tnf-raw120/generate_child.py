"""Generate precisely one raw120 proof closure and print its root path.

The generator output goes to stderr; stdout is the Lean root path.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def run(path, *args, stdout=None):
    subprocess.run([sys.executable, str(ROOT / path), *args],
                   cwd=ROOT, check=True, stdout=stdout or sys.stderr)

def generate(child):
    direct = {"0RF": ("generate.py", "rf", "RF"), "0RB": ("generate_rb.py", "rb", "RB"),
              "0RC": ("generate_rc.py", "rc", "RC"), "0LA": ("generate_la.py", "la", "LA")}
    tags = {"0LB":"ZeroLB","0LF":"ZeroLF","0RA":"RA","1LA":"OneLA","1LB":"OneLB",
            "1LF":"OneLF","1RA":"OneRA","1RB":"OneRB","1RC":"OneRC","1RF":"OneRF"}
    base = HERE.relative_to(ROOT)
    if child in direct:
        script, folder, tag = direct[child]
        run(base / script)
    else:
        tag = tags[child]
        folder = child.lower()
        if child == "0RA":
            run(base / "make_ra_phases.py", str(base / "Raw120RAPhases.lean"))
            run(base / "make_ra_bidfa.py")
            run(base / "make_ra423_block.py")
        if child == "1LB":
            run("im-results/agent13-raw120-late1341/generate.py")
            run("im-results/agent13-raw120-late1341/generate_fast.py")
            with (ROOT / "im-results/agent1-bidfa-sat/Raw120LBSat.lean").open("w") as out:
                run("im-results/agent1-bidfa-sat/emit_raw120.py", stdout=out)
        run(base / "generate_sibling.py", child)
    target = base / folder / ("Raw120" + tag + "Data.lean")
    assert (ROOT / target).is_file(), target
    return target

if __name__ == "__main__":
    assert len(sys.argv) == 2
    print(generate(sys.argv[1]))
