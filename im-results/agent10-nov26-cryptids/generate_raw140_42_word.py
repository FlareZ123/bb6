from pathlib import Path
s=Path(__file__).with_name('generate_raw140_42_mixed.py').read_text().split("print('import Raw14042Counter")[0]
exec(s)
print('import Raw14042Counter\nnamespace Raw14042WordLocal\nopen BB6BlockFAR Raw140Orbit\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n')
for spec in [('forward3',4,1,'28','339',4,1,'228','39'),('back3',1,0,'28','229',1,0,'8','2239')]:print(gen(spec))
print('end Raw14042WordLocal')
