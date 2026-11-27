from pathlib import Path
s=Path(__file__).with_name('generate_raw140_42_mixed.py').read_text().split("print('import Raw14042Counter")[0]
s=s.replace("st=R if d else L;b=st[0]",'st=R if d else L;b=st[:1] or "0"').replace("Bool.false_eq_true] using","Bool.false_eq_true,Szero,left_zero,right_zero] using").replace("L,R=(v+l0,r0) if z else (l0,v+r0)","L,R=(v+l0,r0) if z else (l0,v+r0)\n  if L=='0': L=''\n  if R=='0': R=''")
exec(s)
print('import Raw140ERSuffix\nnamespace Raw14042AWordLocal\nopen BB6BlockFAR Raw140Orbit\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n')
S=['542','152','1121','5215','1155','11511']
for i,t in enumerate(S):print(gen(('tail'+t,4,1,'18',t,4,0,'8','1'+('115' if i==5 else '')+S[(i+1)%6])))
for spec in [('back5',4,0,'18','19',4,0,'8','159'),('front',2,1,'48','4059',4,1,'12558','9'),('finish',4,0,'2558','9',3,0,'58','219'),('first',2,1,'48','4219',3,0,'558','059')]:print(gen(spec))
print('end Raw14042AWordLocal')
