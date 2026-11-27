from pathlib import Path
s=Path(__file__).with_name('generate_raw140_42_mixed.py').read_text().split("print('import Raw14042Counter")[0]
s=s.replace("st=R if d else L;b=st[0]",'st=R if d else L;b=st[:1] or "0"').replace("Bool.false_eq_true] using","Bool.false_eq_true,Szero,left_zero,right_zero] using").replace("L,R=(v+l0,r0) if z else (l0,v+r0)","L,R=(v+l0,r0) if z else (l0,v+r0)\n  if L=='0': L=''\n  if R=='0': R=''")
exec(s)
print('import Raw14042DMixed\nnamespace Raw14042DExitLocal\nopen BB6BlockFAR Raw140Orbit')
for spec in [('drop115',4,0,'1158','19',4,1,'18','1559'),('b05',1,1,'58','059',4,1,'1118','9'),('prep5',4,1,'18','5',4,0,'8','111')]:print(gen(spec))
print('end Raw14042DExitLocal')
