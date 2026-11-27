from pathlib import Path
s=Path(__file__).with_name('generate_raw140_42_mixed.py').read_text().split("print('import Raw14042Counter")[0]
exec(s)
print('import Raw14042Counter\nnamespace Raw14042BMixedLocal\nopen BB6BlockFAR Raw140Orbit\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n')
for spec in [('h1',4,1,'118','229',4,0,'38','1239'),('h2',4,1,'18','239',4,1,'258','39'),('h3',1,0,'538','9',4,0,'8','529')]:print(gen(spec))
print('end Raw14042BMixedLocal')
