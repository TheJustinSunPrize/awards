#!/usr/bin/env python3
"""Exact finite checks for the JSP-000904 counting identities.

All ordinary test sets use integer Cartesian coordinates and squared Euclidean
distance.  The sharpness example uses coordinates (x, sqrt(3) y), represented
exactly by the quadratic form dx^2 + 3 dy^2.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import combinations
import random
from typing import Callable, Iterable, Sequence

Point = tuple[int, int]
Distance = Callable[[Point, Point], int]


def squared_distance(left: Point, right: Point) -> int:
    dx = left[0] - right[0]
    dy = left[1] - right[1]
    return dx * dx + dy * dy


def triangular_lattice_squared_distance(left: Point, right: Point) -> int:
    """Squared distance after mapping (x, y) to (x, sqrt(3) y)."""

    dx = left[0] - right[0]
    dy = left[1] - right[1]
    return dx * dx + 3 * dy * dy


@dataclass(frozen=True)
class Counts:
    n: int
    bad_four_sets: int
    weighted_four_sets: int
    isosceles: int
    disjoint_equal_edges: int
    distance_quadruples: int
    maximum_local_weight: int


def count_objects(
    points: Sequence[Point], distance: Distance = squared_distance
) -> Counts:
    if len(set(points)) != len(points):
        raise ValueError("points must be distinct")
    if len(points) < 4:
        raise ValueError("at least four points are required")

    n = len(points)
    edges = list(combinations(range(n), 2))
    edge_distance = {
        edge: distance(points[edge[0]], points[edge[1]]) for edge in edges
    }
    if any(value <= 0 for value in edge_distance.values()):
        raise AssertionError("distinct points must have positive distance")

    distance_classes = Counter(edge_distance.values())
    grouped_q = sum(
        (2 * multiplicity) ** 2 for multiplicity in distance_classes.values()
    )

    brute_q = 0
    for first_start in range(n):
        for first_end in range(n):
            if first_start == first_end:
                continue
            first_length = distance(points[first_start], points[first_end])
            for second_start in range(n):
                for second_end in range(n):
                    if second_start == second_end:
                        continue
                    if first_length == distance(points[second_start], points[second_end]):
                        brute_q += 1
    assert grouped_q == brute_q

    isosceles = 0
    for apex in range(n):
        others = [index for index in range(n) if index != apex]
        for left, right in combinations(others, 2):
            if distance(points[apex], points[left]) == distance(
                points[apex], points[right]
            ):
                isosceles += 1

    disjoint_equal_edges = 0
    for first, second in combinations(edges, 2):
        if (
            set(first).isdisjoint(second)
            and edge_distance[first] == edge_distance[second]
        ):
            disjoint_equal_edges += 1

    bad_four_sets = 0
    weighted_four_sets = 0
    maximum_local_weight = 0
    for vertex_set in combinations(range(n), 4):
        local_edges = list(combinations(vertex_set, 2))
        local_weight = sum(
            edge_distance[first] == edge_distance[second]
            for first, second in combinations(local_edges, 2)
        )
        if local_weight:
            bad_four_sets += 1
        weighted_four_sets += local_weight
        maximum_local_weight = max(maximum_local_weight, local_weight)

    counts = Counts(
        n=n,
        bad_four_sets=bad_four_sets,
        weighted_four_sets=weighted_four_sets,
        isosceles=isosceles,
        disjoint_equal_edges=disjoint_equal_edges,
        distance_quadruples=brute_q,
        maximum_local_weight=maximum_local_weight,
    )
    verify_identities(counts)
    return counts


def verify_identities(counts: Counts) -> None:
    n = counts.n
    f_count = counts.bad_four_sets
    w_count = counts.weighted_four_sets
    t_count = counts.isosceles
    b_count = counts.disjoint_equal_edges
    q_count = counts.distance_quadruples

    assert q_count == 2 * n * (n - 1) + 8 * (t_count + b_count)
    assert w_count == b_count + (n - 3) * t_count

    numerator = q_count - 2 * n * (n - 1)
    assert numerator % 8 == 0
    assert w_count == numerator // 8 + (n - 4) * t_count

    assert f_count <= w_count <= 10 * f_count
    assert counts.maximum_local_weight <= 10


def all_grid_subsets() -> Iterable[tuple[Point, ...]]:
    grid = tuple((x, y) for x in range(3) for y in range(3))
    for size in range(4, len(grid) + 1):
        yield from combinations(grid, size)


def random_point_sets(count: int, seed: int) -> Iterable[tuple[Point, ...]]:
    generator = random.Random(seed)
    for _ in range(count):
        size = generator.randint(4, 9)
        points: set[Point] = set()
        while len(points) < size:
            points.add((generator.randint(-8, 8), generator.randint(-8, 8)))
        yield tuple(sorted(points))


def main() -> None:
    exhaustive_count = 0
    for points in all_grid_subsets():
        count_objects(points)
        exhaustive_count += 1

    random_count = 0
    for points in random_point_sets(count=200, seed=904):
        count_objects(points)
        random_count += 1

    sharp_rhombus = ((0, 0), (2, 0), (3, 1), (1, 1))
    sharp_counts = count_objects(
        sharp_rhombus, distance=triangular_lattice_squared_distance
    )
    assert sharp_counts.bad_four_sets == 1
    assert sharp_counts.weighted_four_sets == 10
    assert sharp_counts.maximum_local_weight == 10

    print(f"exhaustive 3x3-grid subsets checked: {exhaustive_count}")
    print(f"deterministic random point sets checked: {random_count}")
    print("sharp five-equal-edge rhombus checked: 1")
    print("all JSP-000904 counting checks passed")


if __name__ == "__main__":
    main()
