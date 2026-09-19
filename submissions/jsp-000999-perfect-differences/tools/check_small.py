"""Exact supplemental checks; neither this program nor finite tests prove the theorems."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def differences(a):
    return {max(u-v, 0) for u, v in product(a, repeat=2)}


def positive_representations(a):
    pairs = {}
    for u, v in product(a, repeat=2):
        if u > v:
            pairs.setdefault(u-v, []).append((u, v))
    return pairs


def sidon_sums(a):
    counts = Counter(u+v for u, v in combinations_with_replacement(sorted(a), 2))
    return all(c == 1 for c in counts.values())


def bad(a, d):
    one = {max(u+v-w-e*d, 0) for u, v, w in product(a, repeat=3) for e in range(2)}
    two = {max(u+v-e*d, 0)//2 for u, v in product(a, repeat=2) for e in range(3)}
    shift = {max(u+j*d-i*d, 0) for u in a for i in range(3) for j in range(2)}
    return one | two | shift


def first_missing(f):
    n = 1
    while n in f:
        n += 1
    assert n <= len(f)+1
    return n


def extend(a):
    d = first_missing(differences(a))
    forbidden = bad(a, d)
    k = len(a)
    assert len(forbidden) <= 2*k**3+3*k**2+6*k
    x = first_missing(forbidden)
    assert d <= k*k+1
    assert x+d <= 2*(k+1)**3
    assert x not in a and x+d not in a and x != x+d
    return a | {x, x+d}


def stages(seed, length):
    a = set(seed)
    result = []
    for _ in range(length):
        result.append(a)
        a = extend(a)
    return result


def parse_outputs():
    text = (ROOT/'verification/evaluation.log').read_text()
    decoder = json.JSONDecoder()
    values = []
    while text.strip():
        text = text.lstrip()
        item, end = decoder.raw_decode(text)
        values.append(item)
        text = text[end:]
    return values


def main():
    seeds = [set(c) for k in range(10) for c in combinations(range(1, 10), k)]
    valid = []
    for a in seeds:
        sum_test = sidon_sums(a)
        difference_test = all(len(v) == 1 for v in positive_representations(a).values())
        assert sum_test == difference_test
        if sum_test:
            valid.append(a)
    extra = [{1,2,4,8}, {100,101,104}, {3,7,15}, {1000000}, set()]
    for a in extra:
        assert sidon_sums(a)
    chains = valid + extra
    checks = 0
    for seed in chains:
        old = set()
        for n, a in enumerate(stages(seed, 9)):
            reps = positive_representations(a)
            assert seed <= a and old <= a
            assert len(a) == len(seed)+2*n
            assert all(x > 0 for x in a)
            assert sidon_sums(a) and all(len(v) == 1 for v in reps.values())
            assert all(d in reps for d in range(1, n+1))
            bound = max(seed, default=0)+2*(len(seed)+2*n+1)**3
            assert all(x <= bound for x in a)
            # Later stages retain the unique pair for each earlier difference.
            for d in range(1, n+1):
                top = reps[d][0][0]
                assert top <= max(seed, default=0)+2*(len(seed)+2*d+1)**3
            old = a
            checks += 1
    pair_tests = 0
    for seed in valid:
        if not seed <= set(range(1, 8)):
            continue
        for d in range(1, 11):
            if d in differences(seed):
                continue
            forbidden = bad(seed, d)
            for x in range(1, 31):
                if x not in forbidden:
                    b = seed | {x, x+d}
                    assert sidon_sums(b)
                    assert positive_representations(b)[d] == [(x+d, x)]
                    pair_tests += 1
    # Negative controls: uniqueness hypotheses are essential.
    assert not sidon_sums({1,2,3})
    assert len(positive_representations({1,2,3})[1]) == 2
    # Existing difference + another pair necessarily violates uniqueness.
    assert not sidon_sums({1,2,100,101})
    # A forbidden location can create a collision: 1+3 = 2+2.
    assert 1 in bad({1,2}, 2)
    assert not sidon_sums({1,2,3})
    empty = stages(set(), 7)
    seeded = stages({1,2,4,8}, 6)
    expected = [[sorted(a) for a in empty], [first_missing(differences(a)) for a in empty],
                [sorted(a) for a in seeded], [first_missing(differences(a)) for a in seeded]]
    assert parse_outputs() == expected, 'Lean/Python executable outputs disagree'
    report = {'all_seed_subsets_checked': len(seeds), 'sidon_seeds': len(valid),
              'additional_seed_chains': len(extra), 'verified_stages': checks,
              'nonforbidden_pair_tests': pair_tests, 'negative_controls': 3,
              'lean_outputs_matched': expected}
    (ROOT/'verification/small-cases.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
