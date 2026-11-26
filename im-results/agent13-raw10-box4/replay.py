"""Reproduce discovery and emit the exact proof source. Scratch files stay outside the repo."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess,sys,os
HERE=Path(__file__).resolve().parent
def main():
    work=Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/a13-box4-replay').resolve()
    work.mkdir(parents=True,exist_ok=True)
    os.chdir(work)
    def call(*args):subprocess.run([str(x) for x in args],check=True)
    for name in ('scan','classify','treegen'):
        call('g++','-O3','-std=c++17',HERE/(name+'.cpp'),'-o',work/name)
    jobs=[]
    for t in range(6,12):
        call(work/'scan',t)
        call(work/'classify',t)
        n=sum(1 for _ in open(f'hard{t}.txt'))
        jobs.extend((t,i) for i in range((n+29)//30))
    def finish(job):call(sys.executable,HERE/'finish.py',*job)
    with ThreadPoolExecutor(max_workers=4) as pool:list(pool.map(finish,jobs))
    call(sys.executable,HERE/'greedy.py')
    for t in range(6,12):call(work/'treegen',t)
    call(sys.executable,HERE/'emit_proof.py',HERE/'generated')
if __name__=='__main__':main()
