"""Inclusion-chain witnesses for symbolic prefix products."""
from itertools import combinations


def minimal(terms):
    return frozenset(t for t in terms if not any(u != t and u & t == u for u in terms))


def chain_cover(terms):
    """Maximum matching in the strict-subset bipartite graph gives a minimum chain cover."""
    parent = {}

    def augment(t, seen):
        for u in terms:
            if t == u or t & u != t or u in seen:
                continue
            seen.add(u)
            if u not in parent or augment(parent[u], seen):
                parent[u] = t
                return True
        return False

    for t in terms:
        augment(t, set())
    child = {t: u for u, t in parent.items()}
    chains = []
    for t in sorted(set(terms) - parent.keys()):
        chain = [t]
        while chain[-1] in child:
            chain.append(child[chain[-1]])
        chains.append(chain)
    assert sorted(t for chain in chains for t in chain) == sorted(terms)
    assert all(a & b == a for chain in chains for a, b in zip(chain, chain[1:]))
    # Independent lower bound on chain count by exhaustive antichain search.
    assert any(all(a & b not in (a, b) for a, b in combinations(group, 2))
               for group in combinations(terms, len(chains)))
    return chains


def prefix_chains(gates):
    """Return an explicit chain partition of every nonsingleton prime DNF term."""
    pool = [frozenset([1 << k]) for k in range(32)]
    terms = set()
    for is_and, left, right in gates:
        x, y = pool[left], pool[right]
        z = minimal({u | v for u in x for v in y} if is_and else x | y)
        terms.update(t for t in z if t.bit_count() > 1)
        pool.append(z)
    return chain_cover(sorted(terms))
