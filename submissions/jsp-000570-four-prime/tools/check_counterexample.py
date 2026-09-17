"""Certify a fixed R=0 counterexample to the proposed weaker criterion.

Run: python check_counterexample.py
Only Python's standard library is used. The four fixed integers are verified
prime by exhaustive trial division.
The gcd at the displayed index is derived via exact Lucas digit comparisons,
not by constructing the enormous binomial coefficient. This is not a Lean proof.
"""
from hashlib import sha256
from math import isqrt, prod
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent.parent / "verification"


def digits(n, base):
    result = []
    while n:
        n, r = divmod(n, base)
        result.append(r)
    return result or [0]


def lucas_nonzero(N, k, p):
    nd, kd = digits(N, p), digits(k, p)
    width = max(len(nd), len(kd))
    nd += [0] * (width-len(nd))
    kd += [0] * (width-len(kd))
    violations = [i for i, (ni, ki) in enumerate(zip(nd, kd)) if ki > ni]
    return {"prime":p,"N_digits_low_first":nd,"k_digits_low_first":kd,
        "violating_digit_positions":violations,
        "prime_divides_binomial_by_Lucas":bool(violations)}


def trial_certificate(n):
    assert 2 < n < 2**64 and n % 2 != 0
    limit = isqrt(n)
    assert all(n % d for d in range(3, limit+1, 2)), n
    return {"n":n,"isqrt":limit,
        "divisors_tested":1+len(range(3,limit+1,2)),
        "method":"Exact trial division by 2 and every odd integer through isqrt(n).",
        "prime":True}


def main():
    a, b, c, u = 6, 18, 48, 19
    threshold = 100*c**5
    P = 25480409371
    ps = [P, P+a, P+b, P+c]
    prime_certificates = [trial_certificate(p) for p in ps]
    N = prod(ps)
    k = u*P*P*(P+b)
    assert a >= 1 and b >= 3*a and c == 3*b-a
    assert P >= threshold and 2 <= k <= N//2
    checks = [lucas_nonzero(N,k,p) for p in ps]
    assert [item['prime_divides_binomial_by_Lucas'] for item in checks] == [False,True,False,True]
    gcd_at_k = prod(item['prime'] for item in checks if item['prime_divides_binomial_by_Lucas'])
    proposed_minimum = prod(ps[:3])
    assert gcd_at_k == (P+a)*(P+c) < proposed_minimum
    assert digits(N//P,P) == [5184,1260,72,1]
    assert digits(k//P,P) == [0,342,19]
    q = P+b
    assert digits(N//q,q) == [6480,q-684,q-1]
    assert digits(k//q,q) == [6156,q-684,18]
    result = {
        "P":P,"a":a,"b":b,"c":c,"R":a+c-3*b,
        "P_threshold":threshold,"primes":ps,
        "prime_certificates":prime_certificates,
        "N":N,"k":k,"k_formula":"19*P^2*(P+18)",
        "k_in_minimum_range":True,"N_half_floor":N//2,
        "lucas_checks":checks,
        "quotient_digit_certificates":[
            {"base":P,"N_over_base":[5184,1260,72,1],"k_over_base":[0,342,19]},
            {"base":q,"N_over_base":[6480,q-684,q-1],"k_over_base":[6156,q-684,18]}],
        "gcd_at_k_by_Lucas":gcd_at_k,
        "proposed_minimum_value":proposed_minimum,
        "strictly_below_proposed_minimum":True,
        "conclusion":"The proposed extension c>=3b-a is false. f(N)<=gcd(N,choose(N,k))=(P+6)*(P+48)<P*(P+6)*(P+18).",
        "scope":"Four primes verified by exhaustive exact trial division; exact full base digits verify the displayed gcd via Lucas. No computation of the full minimum f(N), no Lean verification, and no claim that the existing v4 theorem fails.",
        "script":"check_counterexample.py",
        "script_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    OUT.mkdir(exist_ok=True)
    (OUT/'counterexample.json').write_text(json.dumps(result,indent=2)+"\n",encoding='utf-8',newline='\n')
    print("Verified primes:", ps)
    print("N =",N)
    print("k =",k)
    print("gcd at k by Lucas =",gcd_at_k)
    print("proposed minimum =",proposed_minimum)
    print("Strict counterexample to the proposed R>=0 extension; existing v4 is unaffected.")


if __name__ == '__main__':
    main()
