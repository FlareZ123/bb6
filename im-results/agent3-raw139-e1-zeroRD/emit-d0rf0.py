"""Reconcile the independent D0=0RF JavaScript discovery with original replay."""
import json,pathlib,sys,emit
part=pathlib.Path(sys.argv[1])
out=pathlib.Path(sys.argv[2])
fixture=json.loads(pathlib.Path(__file__).with_name('census-d0rf0.json').read_text())
data=json.loads(part.read_text())
assert fixture['parent']==[7,24,11,24,14,24,21,16,24,13,24,24]
assert fixture['limit']==140 and fixture['maxd']==2
assert data['counts']==fixture['counts'],(data['counts'],fixture['counts'])
assert data['open']==fixture['open'],'ordered original open table mismatch'
assert fixture['processed']==len(data['open']) and fixture['residual']==[]
recipes=fixture['recipes']
assert set(map(int,recipes))==set(range(len(data['open'])))
assert max([data['counts']['maxquery']]+[v[1][0] for v in recipes.values() if v[0]=='last'])+6==394
rp=part.with_name('recipes-d0rf0.json')
rp.write_text(json.dumps(recipes,separators=(',',':'))+'\n')
emit.PARENT=fixture['parent']
emit.NS='BB6.Agent3Raw139E1ZeroRDD0ZeroRF'
emit.PREFIX='A3E1ZeroRDD0ZeroRF'
emit.main(part,rp,out,int(sys.argv[3]) if len(sys.argv)>3 else 600)
