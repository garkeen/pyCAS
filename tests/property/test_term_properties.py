"""Randomized structural properties of pure terms."""

import random

from generators import fresh_copy, random_term

SEED = 20261023
ROUNDS = 120


def pool(size: int = 60) -> list:
    rng = random.Random(SEED)
    return [random_term(rng) for _ in range(size)]


def test_equal_terms_always_have_equal_hashes():
    terms = pool()
    for left in terms:
        for right in terms:
            if left == right:
                assert hash(left) == hash(right)


def test_a_freshly_rebuilt_term_is_equal_but_not_shared():
    for term in pool():
        copy = fresh_copy(term)
        assert copy is not term
        assert copy == term
        assert hash(copy) == hash(term)
        assert not copy < term
        assert not term < copy


def test_order_is_a_total_trichotomy():
    rng = random.Random(SEED + 1)
    terms = pool()
    for _ in range(ROUNDS * 4):
        left = rng.choice(terms)
        right = rng.choice(terms)
        assert (left < right) + (right < left) + (left == right) == 1


def test_order_is_transitive():
    rng = random.Random(SEED + 2)
    terms = pool()
    for _ in range(ROUNDS * 3):
        first = rng.choice(terms)
        second = rng.choice(terms)
        third = rng.choice(terms)
        if first < second and second < third:
            assert first < third


def test_sorting_is_independent_of_input_order():
    terms = pool()
    assert sorted(terms) == sorted(reversed(terms))
    assert sorted(terms) == sorted(terms, key=lambda term: term)


def test_equal_terms_collapse_to_one_dictionary_slot():
    for term in pool():
        copy = fresh_copy(term)
        table = {term: "first", copy: "second"}
        assert len(table) == 1
        assert table[term] == "second"
