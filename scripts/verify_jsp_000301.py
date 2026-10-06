"""Check the complete counterexample to the local JSP-000301 proposition."""

from math import isqrt, prod


def factorize(n):
    """Exact trial division for positive integers, including the empty case 1."""
    if n < 1:
        raise ValueError("Expected a positive integer")
    factors = {}
    divisor = 2
    remainder = n
    while divisor * divisor <= remainder:
        while remainder % divisor == 0:
            factors[divisor] = factors.get(divisor, 0) + 1
            remainder //= divisor
        divisor += 1
    if remainder > 1:
        factors[remainder] = factors.get(remainder, 0) + 1
    return factors


def is_powerful(n):
    return all(exponent >= 2 for exponent in factorize(n).values())


def main():
    assert factorize(1) == {}
    assert is_powerful(1)
    assert is_powerful(8) and is_powerful(9)
    assert not is_powerful(12)
    assert isqrt(9) ** 2 == 9
    assert isqrt(8) ** 2 != 8

    first, second = 12167, 12168
    assert first > 0 and second - first == 1
    expected = ({23: 3}, {2: 3, 3: 2, 13: 2})
    for number, expected_factors in zip((first, second), expected):
        factors = factorize(number)
        assert factors == expected_factors
        assert prod(p ** exponent for p, exponent in factors.items()) == number
        assert all(number % (p * p) == 0 for p in factors)
        powerful = is_powerful(number)
        root = isqrt(number)
        square = root * root == number
        assert powerful and not square
        assert root == 110 and root * root < number < (root + 1) ** 2
        print(f"{number}: factors={factors}, powerful={powerful}, "
              f"isqrt={root}, square={square}")
    print("PASS: consecutive powerful positive integers, neither a square")


if __name__ == "__main__":
    main()
