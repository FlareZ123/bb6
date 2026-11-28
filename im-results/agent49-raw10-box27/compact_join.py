"""Replace repeated finite case tactics by the checked, generic join rule.
Usage: python compact_join.py DIRECTORY/Box27...Source.lean [...]
"""
import re,sys
from pathlib import Path
def compact(p):
    p=Path(p);s=p.read_text()
    if s.startswith('import Box27Join\n'):return
    pat=r'theorem (g\d+) : Good (\d+) (.*?) := by\n  apply split_good \2 \3 (\d+)\n  intro v\n  have hv : [^\n]*\n  rcases hv with [^\n]*\n((?:  · exact g\d+\n){25})'
    def f(m):return f'theorem {m[1]} : Good {m[2]} {m[3]} :=\n  BB6.Agent49.Box27Join.split25 {m[2]} {m[3]} {m[4]} '+' '.join(re.findall(r'exact (g\d+)',m[5]))+'\n'
    s,n=re.subn(pat,f,s)
    pat=r'theorem (g\d+) : Good (\d+) (.*?) := by\n  apply split_ef_good \2 \3 (\d+) \(by decide\)\n  intro v hr\n  have hle[^\n]*\n  have hv : [^\n]*\n  rcases hv with [^\n]*\n((?:  · exact g\d+\n){21})'
    def f(m):return f'theorem {m[1]} : Good {m[2]} {m[3]} :=\n  BB6.Agent49.Box27Join.split21 {m[2]} {m[3]} {m[4]} (by decide) '+' '.join(re.findall(r'exact (g\d+)',m[5]))+'\n'
    s,k=re.subn(pat,f,s)
    if n+k==0:raise ValueError(f'No recognized joins in {p}')
    p.write_text('import Box27Join\n'+s);print(p,n,k)
if __name__=='__main__':
    for p in sys.argv[1:]:compact(p)
