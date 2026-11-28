import random
import unittest
from pack_shards import Shard, pack_shards


class PackingTests(unittest.TestCase):
    def test_interleaved_postorder(self):
        def s(name, *deps):
            return Shard('@'+name, 100, name, frozenset(deps))
        shards = [s('a','Common'), s('b','@a'), s('c','@b'),
                  s('d','Common'), s('e','@d'), s('f','@c','@e')]
        assign, groups = pack_shards(shards, 'Fixture')
        self.assertEqual(assign['@a'], assign['@d'])
        self.assertEqual(assign['@b'], assign['@e'])
        self.assertEqual(len(groups), 4)
        self.assertEqual(groups[-1][1], {assign['@c'], assign['@e']})

    def test_random_postorder_dags(self):
        rng = random.Random(33)
        for _ in range(20):
            shards = []
            rank = {}
            for i in range(1000):
                deps = rng.sample(range(i), min(i, rng.randrange(4)))
                token = f'@{i}'
                rank[token] = 1+max((rank[f'@{j}'] for j in deps), default=-1)
                shards.append(Shard(token, rng.randrange(1,385),token,
                                    frozenset([f'@{j}' for j in deps]+['External'])))
            assign, groups = pack_shards(shards, 'Fixture', 1500, 12)
            self.assertEqual(len(assign), len(shards))
            module_rank = {}
            counts = {s.token:s.nodes for s in shards}
            for module, imports, bodies in groups:
                self.assertEqual(len({rank[b] for b in bodies}), 1)
                self.assertLessEqual(sum(counts[b] for b in bodies),1500)
                self.assertLessEqual(len(bodies),12)
                module_rank[module] = rank[bodies[0]]
                self.assertTrue(all(d == 'External' or module_rank[d] < module_rank[module] for d in imports))
            for s in shards:
                self.assertIn(s.token,next(b for m,_,b in groups if m==assign[s.token]))
                self.assertTrue(all(assign[d] != assign[s.token] for d in s.imports if d.startswith('@')))


if __name__ == '__main__':
    unittest.main()
