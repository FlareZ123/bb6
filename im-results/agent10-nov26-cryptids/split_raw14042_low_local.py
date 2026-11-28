from pathlib import Path
import re
p=Path('Raw14042LowLocal.lean')
s=p.read_text()
start=s.index('\ntheorem ')
end=s.rindex('\nend Raw14042LowLocal')
header=s[:start]
parts=[x for x in re.split(r'(?=\ntheorem )',s[start:end]) if x]
mods=[]
for i,part in enumerate(parts):
    mod=f'Raw14042LowLocal{i:02d}'
    Path(mod+'.lean').write_text(header+part+'\nend Raw14042LowLocal\n')
    mods.append(mod)
p.write_text(''.join('import '+mod+'\n' for mod in mods))
