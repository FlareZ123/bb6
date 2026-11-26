"""Reproduce discovery and emit the exact proof source. Scratch files stay outside the repo."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse,subprocess,sys,os

HERE=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('work',nargs='?',default='/tmp/a13-box4-replay')
    parser.add_argument('--target',type=int,choices=range(6,12),
                        help='build only the selected final-halt slice (6 through 11)')
    args=parser.parse_args()
    targets=[args.target] if args.target is not None else list(range(6,12))
    work=Path(args.work).resolve()
    work.mkdir(parents=True,exist_ok=True)
    os.chdir(work)
    # A replay must not silently consume stale partial outputs from an earlier run.
    for pattern in ('open*.txt','ngram*.txt','hard*.txt','long*.json','tree*.txt',
                    'greedyboxes.json','greedyboxes.txt'):
        for stale in work.glob(pattern):
            stale.unlink()
    def call(*args):subprocess.run([str(x) for x in args],check=True)
    for name in ('scan','classify','treegen'):
        call('g++','-O3','-std=c++17',HERE/(name+'.cpp'),'-o',work/name)
    jobs=[]
    for t in targets:
        call(work/'scan',t)
        call(work/'classify',t)
        n=sum(1 for _ in open(f'hard{t}.txt'))
        jobs.extend((t,i) for i in range((n+29)//30))
    def finish(job):call(sys.executable,HERE/'finish.py',*job)
    with ThreadPoolExecutor(max_workers=4) as pool:list(pool.map(finish,jobs))
    greedy_args=[sys.executable,HERE/'greedy.py']
    if args.target is not None:greedy_args.append(args.target)
    call(*greedy_args)
    for t in targets:call(work/'treegen',t)
    emit_args=[sys.executable,HERE/'emit_proof.py',HERE/'generated']
    if args.target is not None:emit_args.append(args.target)
    call(*emit_args)

if __name__=='__main__':main()
