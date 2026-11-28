# Raw36 D1=0LB accepted Cover and six-live reduction

The exact Raw36 direct child
`1RB---_1RC---_0RD---_0LD0LB_------_------` (D1=0LB / D101) now has a
source-accepted `Cover (WeightedBound 450)`.

The accepted producer is workflow run **46154682785**, artifact
**15268397082** (`raw36-direct01-original-cover450`).  Its authenticated
archive SHA256 is
`6a902934fd4a9632d76c45352a9d20934d021c9900c628e12dc2ef680079ff64`;
the root module identity is
`55cbdb098e1a3c84066a6ea4bb96fd144a1f4a24ef412a075f46c19bc0d4acbe`.
The producer theorem is `BB6.Agent29Raw36D101.cover`.

The blocking issue was a Lean module-identity collision: already accepted
children depended on the legacy `Raw36D101Automata*` family, while the
corrected common generation needed different contents under the same module
names.  `generate_direct.py` now permits an automata suffix; fresh children
use `Raw36D101FreshAutomata*`, while accepted children retain and
hash-authenticate their exact legacy automata objects.

The accepted D101 object was then composed with the already accepted D102
(D1=0LC) and D114 (D1=1LC) parents.  Workflow run **46159409037** succeeded;
evidence artifact **15269357386** contains the authenticated source receipt.
The source-checked theorem is

`BB6.Agent18Raw36.parent_cover_from_live6_after01_02_14`

and reduces the Raw36 parent to exactly six direct D1 Cover premises at
weighted bound B≥1152:

`0LA, 1LA, 0LE, 0RE, 1LE, 1RE`.

The theorem's source SHA256 is
`1a7a8036c59873044147eddf157c4f55204e4220cdd13466ef2ef7a8681a02be`;
root olean SHA256 is
`d56c6c4512444345d09dc1b1a17c9c07b93f2c401a22701b6b6a7ba4e52fc213`.
The printed axiom set is only
`[propext, Classical.choice, Quot.sound]` (with `propext` alone on the
definitional/count lemmas).

This is a strict reduction of the accepted Raw36 universal-cover interface
from seven to six direct D1 premises.  It does not by itself close Raw36.
