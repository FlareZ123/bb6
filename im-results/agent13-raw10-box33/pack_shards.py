"""Pack postorder proof shards by dependency height, never across heights."""
from collections import defaultdict
from dataclasses import dataclass


@dataclass(frozen=True)
class Shard:
    token: str
    nodes: int
    body: str
    imports: frozenset[str]


def pack_shards(shards: list[Shard], family: str, max_nodes: int = 3000,
                max_decls: int = 32):
    ranks = {}
    levels = defaultdict(list)
    for shard in shards:
        assert shard.token.startswith('@') and shard.token not in ranks
        assert 0 < shard.nodes <= max_nodes
        dependencies = [ranks[d] for d in shard.imports if d.startswith('@')]
        rank = 1 + max(dependencies, default=-1)
        ranks[shard.token] = rank
        levels[rank].append(shard)

    assignments = {}
    groups = []
    for rank in sorted(levels):
        group = []
        size = 0

        def flush():
            nonlocal group, size
            if not group:
                return
            module = f'{family}DG{len(groups):04d}'
            for shard in group:
                assignments[shard.token] = module
            imports = frozenset(assignments.get(dep, dep)
                                for shard in group for dep in shard.imports)
            assert module not in imports and not any(d.startswith('@') for d in imports)
            groups.append((module, imports, tuple(s.body for s in group)))
            group = []
            size = 0

        for shard in levels[rank]:
            if size + shard.nodes > max_nodes or len(group) >= max_decls:
                flush()
            group.append(shard)
            size += shard.nodes
        flush()
    return assignments, groups
