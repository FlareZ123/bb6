from pathlib import Path
s = Path(__file__).with_name('generate_raw140_42_mixed.py').read_text().split("print('import Raw14042Counter")[0]
s = s.replace("st=R if d else L;b=st[0]", 'st=R if d else L;b=st[:1] or "0"').replace("Bool.false_eq_true] using", "Bool.false_eq_true,Szero,left_zero,right_zero] using").replace("L,R=(v+l0,r0) if z else (l0,v+r0)", "L,R=(v+l0,r0) if z else (l0,v+r0)\n  if L=='0': L=''\n  if R=='0': R=''")
exec(s)
print('import Raw140VariantTransfer\nnamespace Raw14042MixedFrontLocal\nopen BB6BlockFAR Raw140Orbit\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nattribute [local irreducible] run boundary')
for spec in [
 ('cSeed1',3,0,'68','4215542',3,0,'8','44055542'),
 ('cSeed2',3,0,'68','44055542',3,0,'8','442115152'),
 ('cSeed3',3,0,'68','442115152',3,0,'8','4440515152'),
 ('cSeed4',3,0,'68','4440515152',3,0,'8','444211151121'),
 ('bSeed',4,1,'1358','1123315',4,1,'18','115222325')
]:
 print(gen(spec).replace('(X Y : List Sym)', '(X : List Sym)'))
print('end Raw14042MixedFrontLocal')
