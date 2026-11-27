import base64,gzip,hashlib,pathlib
p=pathlib.Path(__file__).parent
for name,sha in [
 ("affine8938.py","2e816a424f363851ffe92806821e29dd445fceb585348d1318785c5b2583a608"),
 ("8938-growth.json","ac81f3de0bc242cae7f1c79cca29bac540104c52372c1cdc198b66da5a950c6e"),
 ("seed8938.cpp","2a3e0aee13af55a949049b9af2b2f99d4ee4d36b81cb2599868001c8191318ac")]:
    raw=gzip.decompress(base64.b64decode((p/(name+".gz.b64")).read_text()))
    assert hashlib.sha256(raw).hexdigest()==sha
    (p/name).write_bytes(raw)
