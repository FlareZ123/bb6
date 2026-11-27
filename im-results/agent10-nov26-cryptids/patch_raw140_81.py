"""Specialize the shared sibling-86 affine proof to the odd-rank sibling 81.

All generated theorems are subsequently checked by Lean.  The only reachable
terminal ranks are 1, 3, 5.  The three changed terminal endpoints are encoded
in the new arithmetic and checked against the variant-specific local rules.
"""
from pathlib import Path
import re
p=Path(__file__).resolve().parent
N='Raw14081'; A=N+'Arithmetic'
s=(p/'Raw14086Arithmetic.lean').read_text().replace('Raw14086Arithmetic',A).replace('| _ => (.a2,p+4)','| _ => (.a0,p+7)').replace('| 3 => (.b0,p+6) | 4 => (.a0,p+6)','| 3 => (.a2,p+6) | 4 => (.a0,p+6)').replace('| _ => (.a0,p+7)\ndef ret','| _ => (.b0,p+10)\ndef ret')
(p/(A+'.lean')).write_text(s)
for suf,term,rank in [('D','B','Raw140Double.rank'),('C','C','crank'),('B','A','arank')]:
 f=p/(N+suf+'.lean');s=f.read_text().replace('Raw14086Arithmetic',A)
 for name in ['terminal'+term,'drain'+term]:
  pattern=r'(theorem '+name+r' \([^\n]*\) \(hp : 24 ≤ p\)) :'
  s,n=re.subn(pattern,r'\1 (hodd : '+rank+' s % 2 = 1) :',s);assert n==1,(name,n)
 start=s.index('theorem terminal'+term);end=s.index('\ntheorem drain'+term,start)
 t=s[start:end];a,b=t.split('  cases s\n');cases=re.split(r'^  · ',b,flags=re.M);assert len(cases)==7
 for i in (0,2,4):cases[i+1]=f'simp [{rank}] at hodd\n'
 if term=='B':cases[6]=cases[6].replace('cfg,A2','cfg,A0').replace('p-24+28=p+4','p-24+31=p+7')
 if term=='A':cases[4]=cases[4].replace('cfg,B0','cfg,A2')
 if term=='C':cases[6]=cases[6].replace('cfg,A0','cfg,B0').replace('p-24+31=p+7','p-24+34=p+10')
 s=s[:start]+a+'  cases s\n'+'  · '.join(cases)+s[end:]
 s=s.replace('(terminal'+term+' _ s (by omega))','(terminal'+term+' _ s (by omega) hodd)')
 if term=='B':
  s=s.replace('(ho : h%2=1) :','(ho : h%2=1) (hr : Raw140Double.rank s % 2 = 1) :').replace('(hn : 3 ≤ n) :','(hn : 3 ≤ n) (hr : Raw140Double.rank (Raw140Double.rho s) % 2 = 1) :')
  s=s.replace('(drainB _ n s (by omega))','(drainB _ n s (by omega) hr)').replace('(drainB _ z _ (by omega))','(drainB _ z _ (by omega) hr)')
  s=s.replace('n t (by omega) hpar','n t (by omega) hpar (by omega)').replace('n t (by omega) (by omega) hn3','n t (by omega) (by omega) hn3 (by rw [rank_rho,hs]; unfold next; omega)')
 if term=='C':
  s=s.replace('n t (by omega)\n    simpa only [ret','n t (by omega) (by omega)\n    simpa only [ret').replace('(cn t) (by omega)\n    have h :=','(cn t) (by omega) (by rw [crank_next,hs]; unfold next; omega)\n    have h :=')
 if term=='A':
  s=s.replace('z t (by omega)\n    have h\'','z t (by omega) (by dsimp only [t]; rw [arank_next,hs]; unfold next; omega)\n    have h\'').replace('(an t) (by omega)\n    simp only','(an t) (by omega) (by dsimp only [t]; rw [arank_next,arank_next,hs]; unfold next; omega)\n    simp only')
 f.write_text(s)
f=p/(N+'Cover.lean');f.write_text(f.read_text().replace('Raw14086Arithmetic',A))
