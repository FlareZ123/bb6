"""Read compressed, exact-keyed discovery fixtures."""
import base64,gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
SHA={
'new_winners':'4d3156de330ddb843dd0ad1f8ea35b8708252af99c918c3717dd6e4b466cec59',
'rle':'707e1bf1fdcefcdc969aaa76f067158c2bf39596ce98e17c57126a842c8925bd',
'blocks':'80f1aeff252bbb91e4789a8bce1ca34cfeaa637c6a16ea41102e26e87e9f8d32',
'late':'33990e933be65f9d1a08148c3c1bf84f549727ea07ee6c25f280a2dcda03a6c5',
'remaining':'a3a83ac9d218c4a92da881f18803f0b87b745ab3d2f94e372e6c738cf3f0aeb9',
'sweeps':'9d33689e0415cd974be7356c541ca30e7d15cd3d11c303a899a4a411fcded547'}
def load(key):
    raw=gzip.decompress(base64.b64decode((D/(key+'.b64')).read_text()))
    assert hashlib.sha256(raw).hexdigest()==SHA[key],key
    return json.loads(raw)
if __name__=='__main__':
    import sys
    for x in load(sys.argv[1]):
        print(x if isinstance(x,str) else json.dumps(x))
