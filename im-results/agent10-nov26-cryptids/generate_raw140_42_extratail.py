from pathlib import Path
s=Path(__file__).with_name('generate_raw140_42_mixed.py').read_text().split("print('import Raw14042Counter")[0]
s=s.replace("st=R if d else L;b=st[0]",'st=R if d else L;b=st[:1] or "0"').replace("Bool.false_eq_true] using","Bool.false_eq_true,Szero,left_zero,right_zero] using").replace("L,R=(v+l0,r0) if z else (l0,v+r0)","L,R=(v+l0,r0) if z else (l0,v+r0)\n  if L=='0': L=''\n  if R=='0': R=''")
exec(s)
print('import Raw14042Bank\nnamespace Raw14042ExtraTailLocal\nopen BB6BlockFAR Raw140Orbit')
print(gen(('prep11',4,1,'18','11',4,0,'38','542')))
print('end Raw14042ExtraTailLocal')
