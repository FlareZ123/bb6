"""Reuse the seven accepted exact exceptional proof cuts; no discovery rerun."""
import hashlib, json, pathlib, shutil, subprocess, sys, zipfile
CUTS = [
  [
    15171375225,
    "45935354840",
    "ad895e85ae2954cd4fab92df445c47e9b820a5b8",
    "OLFSparseWidth1352",
    "1c94c98f493a25aba317014fe01a32944abf9e46b6361047b975e8624e3cacb2"
  ],
  [
    15170932852,
    "45934313826",
    "23e8026d1e61e54968f9de307675dcb02608ed3f",
    "OLFWidth17162",
    "9c8932b5647c0ea0cc34c1cd0c4ca50f3fc3ad42f448eba41fe7ff079ca9e8d0"
  ],
  [
    15170131992,
    "45934015716",
    "fcccf81eee571893e8ed2fe7370187880b5fd80f",
    "Sweep9135",
    "e75d5577848ded1703e6e9b0c6e9c2e37507a9410d8b48d3aea8a4ce0318ca0d"
  ],
  [
    15169563256,
    "45933068248",
    "1260c11adaa4996d573755440700db255c924400",
    "LongCycle",
    "ef5122b2dc257583b935640a34bc99b900114d054e83d1dff9a5ac40edf3157b"
  ],
  [
    15171026496,
    "45934313826",
    "23e8026d1e61e54968f9de307675dcb02608ed3f",
    "OLFWidth5952",
    "37f37c3777014bb16ed7afa6d29dc28b12f3a62004ae974961799d482ce223ad"
  ],
  [
    15169578643,
    "45934309359",
    "23e8026d1e61e54968f9de307675dcb02608ed3f",
    "Sweep14327",
    "b747c01f806bd72ef64a4158b389cd7dc0c2d016744984ae2c0a192be9ab439f"
  ],
  [
    15169216916,
    "45933535891",
    "738f93b7702f8d4e009c3bfe026bf59155d97349",
    "TripleSweep",
    "d088f266aea878e011e807fdc6b11e1b80d369ba9aa81efa8c2581676871e89e"
  ]
]
work=pathlib.Path(sys.argv[1]).resolve()
imports=pathlib.Path(sys.argv[2]).resolve()
work.mkdir(parents=True,exist_ok=True)
imports.mkdir(parents=True,exist_ok=True)
out=work/'merged'
out.mkdir(exist_ok=True)
digest=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
entries={}
base=None
revisions=set()
for aid,run,rev,root,sha in CUTS:
    archive=work/f'{aid}.zip'
    if not archive.exists():
        with archive.open('wb') as f:
            subprocess.run(['gh','api',f'repos/FlareZ123/bb6/actions/artifacts/{aid}/zip'],stdout=f,check=True)
    assert digest(archive)==sha,aid
    folder=work/str(aid)
    folder.mkdir(exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        z.extractall(folder)
    m=json.loads((folder/'manifest.json').read_text())
    assert m['workflow']['run_id']==run and m['proof_source_revision']==rev,aid
    assert [r['module'] for r in m['roots']]==[root],aid
    revisions.add(rev)
    if base is None: base=m
    assert m['lean_version']==base['lean_version'] and m['lean_binary']['sha256']==base['lean_binary']['sha256']
    for e in m['modules']:
        name=e['module']
        obj=folder/'build'/e['olean_path']
        assert digest(obj)==e['olean_sha256'],name
        if name in entries:
            assert entries[name]['module_identity_sha256']==e['module_identity_sha256'],name
        else:
            entries[name]=e
            target=out/e['olean_path']
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(obj,target)
        source=folder/'imports'/f'{name}.lean'
        if source.exists():
            assert digest(source)==e['source_sha256'],name
            target=imports/source.name
            if target.exists(): assert digest(target)==e['source_sha256'],name
            else: shutil.copy2(source,target)
    assert root in entries,root
for name,e in entries.items():
    assert all(dep in entries for dep in e['project_imports']),name
manifest=dict(base,modules=list(entries.values()),module_count=len(entries),source_revisions=sorted(revisions))
(work/'merged.json').write_text(json.dumps(manifest,indent=2))
print('Merged',len(entries),'checked module identities from',len(CUTS),'accepted exceptional cuts')
