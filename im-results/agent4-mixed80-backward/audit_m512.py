"""Reproduce M512 overlap against Agent41's unchanged finite graph.

This is an independent audit of prior computational results, not a formal
Lean proof of the 52M-state closure. Linux CI script, run only manually.
"""
from pathlib import Path
import fcntl
import os
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
original = root / "im-results/agent41-c-quotient512/validate_bits.cpp"
text = original.read_text(encoding="utf-8")
mark = " munmap(queue,(size_t)count*4);"
assert text.count(mark) == 1, "Unexpected upstream C++ source layout"
extra = r"""
 if(m==512) {
  auto lift=[=](int r)->int{return 8+((r-8+512)%512);};
  int first=0,secondA=0,secondB=0;
  for(int i=0;i<32;i++) {
   int k=(71+80*i)%512;
   first+=contains(code(1,lift(k),0));
  }
  for(int i=0;i<32;i++)for(int j=0;j<32;j++) {
   int u=60+80*i,depth=11+80*j;
   int a=(2*u+1)%512,k=(512-(u+3*depth+4)%512)%512;
   secondA+=contains(code(lift(a),lift(k),0));
   u=20+80*i;depth=51+80*j;
   a=(2*u+1)%512;k=(512-(u+3*depth+4)%512)%512;
   secondB+=contains(code(lift(a),lift(k),0));
  }
  printf("A4 M512 lift audit: first=%d/32 secondA=%d/1024 secondB=%d/1024 (present)\\n",
    first,secondA,secondB);
  if(first || secondA || secondB)abort();
 }
"""
source = text.replace(mark, extra + mark)
with tempfile.TemporaryDirectory(prefix="a4-m512-") as folder:
    folder = Path(folder)
    lockpath = folder / "audit.lock"
    with lockpath.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        handle = tempfile.NamedTemporaryFile(mode="w", dir=folder, delete=False, encoding="utf-8")
        try:
            handle.write(source)
            handle.close()
            os.replace(handle.name, folder / "audit.cpp")
        finally:
            if not handle.file.closed:
                handle.close()
        subprocess.run(["g++", "-std=c++17", "-O3", "-Wall", "-Wextra",
                        str(folder / "audit.cpp"), "-o", str(folder / "audit")],
                       check=True)
        result = subprocess.run([str(folder / "audit"), "512"],
                                capture_output=True, text=True, check=True)
        output = result.stdout
        assert "M=512 reached=52736417 edges=413022600" in output
        assert "A4 M512 lift audit: first=0/32 secondA=0/1024 secondB=0/1024 (present)" in output
        print("\n".join(line for line in output.splitlines()
                        if line.startswith(("M=512", "A4 M512 lift audit:"))))
