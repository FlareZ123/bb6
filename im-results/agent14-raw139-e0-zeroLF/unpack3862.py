#!/usr/bin/env python3
"""Reproduce the 3862 Lean sources; Python only generates untrusted witnesses."""
import base64, hashlib, io, pathlib, shutil, subprocess, sys, tarfile, tempfile
here=pathlib.Path(__file__).resolve().parent
out=pathlib.Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
raw=base64.b64decode("".join((here/f"3862-source.b64.{i}").read_text().strip() for i in (1,2,3)),validate=True)
assert hashlib.sha256(raw).hexdigest()=="d07ed63e04e65d73d60bc75fc70e0ef2bf1ad60ce62398cc59ab0321aa3fe08c"
with tempfile.TemporaryDirectory() as tmp:
    root=pathlib.Path(tmp)
    with tarfile.open(fileobj=io.BytesIO(raw),mode="r:gz") as tf:
        tf.extractall(root,filter="data")
    with (root/"Rec3862Trace.lean").open("w") as f:
        subprocess.run([sys.executable,"gen3862.py"],cwd=root,stdout=f,check=True)
    for cmd in (["shardrec3862.py"],["seed3862.py"],["genseed3862.py","128"]):
        subprocess.run([sys.executable,*cmd],cwd=root,check=True)
    for f in [root/"Rec3862Base.lean",root/"Rec3862SeedBase.lean",*sorted((root/"recshards").glob("*.lean")),*sorted((root/"seedshards").glob("*.lean"))]:
        shutil.copyfile(f,out/f.name)
print("3862: generated exact proof sources",out)
