"""Run exact eight-hole D1 sibling scans and cross-parent DFA portfolio.
Candidate discovery only; Lean proof generation is a separate stage."""
import pathlib, subprocess, sys, concurrent.futures

D=pathlib.Path(__file__).resolve().parent

def run(mv,out):
    return subprocess.run(
        ["node",str(D/"discoverCoupled8Node.js"),mv,str(out)],
        timeout=1200,check=False).returncode

def main():
    out=pathlib.Path(sys.argv[1]); out.mkdir(parents=True,exist_ok=True)
    moves=sys.argv[2:]
    assert moves and len(moves)<=8 and len(set(moves))==len(moves)
    for m in moves:
        assert len(m)==3 and m[0] in "01" and m[1] in "LR" and m[2] in "ABCDE"
        assert m!="0LA"
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        status=list(pool.map(lambda m:run(m,out),moves))
    print(dict(zip(moves,status)),flush=True)
    if any(status): raise SystemExit(1)

if __name__=="__main__":
    main()
