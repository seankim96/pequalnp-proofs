"""Replay first OR choices after the exceptional OR(14,18), AND(1,43) order."""
from order3_case35_h19_second_product import read_ledger
from order3_case35_point_seven_or_order import dominates, guard_unions, one_preload
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_case35_star_preloads import eight_paid_floor
from order3_prefix_search import test_rows


def replay():
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    union = base[14] | base[18]
    product = base[1] & union
    pool = [*base, union, product]
    # Replacing a candidate by a starting wire (possibly guard-masked)
    # with more positive and fewer negative ones saves this OR.
    if one_preload(base, union, product) <= 18:
        raise ValueError("deleting the first suffix OR must violate its budget")
    free = set(pool) | {v & pool[32] for v in pool}
    domain = set(guard_unions(pool))
    dominated = {v for v in domain if any(dominates(w, v) for w in free)}
    certified = set()
    for word, tests, guard_off, recorded in read_ledger("or-floors"):
        value = int(word, 16)
        if value not in domain or value in dominated or value in certified:
            raise ValueError("unexpected or repeated candidate OR")
        rows = [j for j, flags in tests]
        floor = eight_paid_floor(pool, value, rows, guard_off, dict(tests),
                                 unique_paid_outputs=True)
        if floor != recorded or floor <= 18:
            raise ValueError("preloaded OR still fits the budget")
        certified.add(value)
    # A separating continuation with v also works with any w dominating v
    # if w is available at exactly the same one-OR cost.
    excluded = dominated | {v for v in domain if any(dominates(w, v) for w in certified)}
    subgroup = {a | b for a in (product, product & pool[32]) for b in free}
    print("distinct ORs",len(domain),"free-wire exclusions",len(dominated),
          "eight-AND certificates",len(certified),"excluded",len(excluded))
    print("remaining ORs",len(domain-excluded),"wire-44 unions",len(subgroup),
          "wire-44 remaining",len(subgroup-excluded))
    print("OR(0,44) excluded", (pool[0] | product) in excluded)
    return domain - excluded


if __name__ == "__main__":
    replay()
