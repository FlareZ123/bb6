"""Convert generated BiDFA list certificates to independently checked trie certificates."""
import re, ast, sys
from pathlib import Path

def trie(xs):
    if not xs:return '.empty'
    if xs=={0}:return '.leaf'
    return '(.branch '+trie({x//2 for x in xs if x%2==0})+' '+trie({x//2 for x in xs if x%2==1})+')'
def arr(xs):return '#['+','.join(map(trie,xs))+']'
def convert(s):
    m=re.search(r'def cert : Cert := ⟨(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\]),\s*(\[[^\]]*\])⟩',s)
    if m is None:raise ValueError('unsupported certificate syntax')
    dl,dr=map(ast.literal_eval,m.groups()[:2])
    el,er,states=[ast.literal_eval(x.replace('⟨','(').replace('⟩',')').replace('true','1').replace('false','0')) for x in m.groups()[2:]]
    def edges(es):
        rows=[set() for _ in range(max(x[0] for x in es)+1)]
        for d,b,t in es:rows[d].add(2*t+b)
        return rows
    nr=max(x[3] for x in states)+1
    rows=[set() for _ in range(12)]
    for q,a,l,r in states:rows[2*q+a].add(r+nr*l)
    cert=f'def cert : FastCert := ⟨{dl},{dr},{arr(edges(el))},{arr(edges(er))},{nr},{arr(rows)}⟩'
    s=s[:m.start()]+cert+s[m.end():]
    return s.replace('import BiDFA','import FastBiDFA').replace('open BB6Coverage BB6Coverage.Agent16BiDFA','open BB6Coverage BB6.Agent32FastBiDFA')
if __name__=='__main__':
    for path in map(Path,sys.argv[1:]):
        path.write_text(convert(path.read_text()))
