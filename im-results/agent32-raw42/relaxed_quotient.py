#!/usr/bin/env python3
"""Search safe quotient witnesses by relaxing equality of relation labels.

Every candidate is re-saturated from blank. The resulting source must still
pass the unchanged FastBiDFA Lean theorem; the search is untrusted.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations
import argparse
from partial_ngram_quotient import (load, close, prune, stats, partial_merge,
                                    exact_quotient, relation_labels, render)


def cost(D, E, S):
    # Prefer smaller joint state obligations, then smaller edge and DFA sets.
    return len(S), sum(map(len, E)), sum(map(len, D))


def candidate_pairs(labels):
    # Overlap is a search heuristic only. Exact safety follows from closure.
    buckets = defaultdict(list)
    for i, label in enumerate(labels):
        for key in label:
            buckets[key].append(i)
    overlap = defaultdict(int)
    for bucket in buckets.values():
        for i, j in combinations(bucket, 2):
            overlap[i, j] += 1
    return sorted(overlap, key=lambda p: (
        len(labels[p[0]]) + len(labels[p[1]]) - 2*overlap[p],
        -overlap[p], p))


def relaxed_quotient(trans, D, E, S, attempts):
    remaining = attempts
    while remaining:
        improved = False
        for k in (0, 1):
            labels = relation_labels(D, S, k)
            for i, j in candidate_pairs(labels):
                if not remaining:
                    break
                remaining -= 1
                # A constant label makes only the observed-push congruence
                # mandatory. Different state rows can now be joined.
                merged, _ = partial_merge(D[k], E[k], [None]*len(labels), [(i,j)])
                trial = D.copy()
                trial[k] = merged
                out = close(trans, trial, cap=len(S))
                if out is None:
                    continue
                trial, edges, states = prune(trial, *out)
                if close(trans, trial, cap=len(states)) != (edges, states):
                    continue
                if cost(trial, edges, states) >= cost(D, E, S):
                    continue
                trial, edges, states = exact_quotient(trans, trial, edges, states)
                if cost(trial, edges, states) >= cost(D, E, S):
                    continue
                D, E, S = trial, edges, states
                improved = True
                break
            if improved or not remaining:
                break
        if not improved:
            break
    return D, E, S, attempts - remaining


def transform(source, attempts=500):
    if attempts < 0:
        raise ValueError("attempts must be nonnegative")
    match, trans, D, E, S = load(source)
    before = stats(D,E,S)
    out = close(trans,D,cap=len(S))
    assert out is not None
    assert out[1] <= S and all(e <= old for e,old in zip(out[0],E))
    D,E,S = prune(D,*out)
    assert close(trans,D,cap=len(S)) == (E,S)
    D,E,S = exact_quotient(trans,D,E,S)
    baseline = stats(D,E,S)
    D,E,S,n = relaxed_quotient(trans,D,E,S,attempts)
    assert close(trans,D,cap=len(S)) == (E,S)
    return render(source,match,D,E,S),before,baseline,stats(D,E,S),n


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('source',type=Path)
    p.add_argument('target',type=Path)
    p.add_argument('--attempts',type=int,default=500)
    a=p.parse_args()
    source,before,baseline,after,n=transform(a.source.read_text(),a.attempts)
    a.target.write_text(source)
    print(a.source.name,before,'->',baseline,'->',after,'attempts',n,flush=True)
