import json,re,sys,pathlib
from emit_lean import emit
root=pathlib.Path(sys.argv[1]);ns=sys.argv[2];batch=int(sys.argv[3]) if len(sys.argv)>3 else 8
assert batch>0
for l in open(root/'alt.jsonl'):
 c=json.loads(l);i=c['id'];file=root/'src'/f'{ns}Bank{(i-1)//batch:03d}.lean';s=file.read_text();s,n=re.subn(rf'namespace H{i}\n.*?\nend H{i}\n',lambda m:emit(c),s,flags=re.S);assert n==1;file.write_text(s)
 print(ns,i,'block',c['w'],c['D'],c['N'])
