"""Domain catalogs are explicit immutable values, never module-global state."""

import subprocess
import sys

import cas.math.domains.base as base
from cas.math.domains.base import Domain, DomainCapabilities, DomainCatalog
from cas.syntax.term import S


def _catalog():
    from cas.runtime import bootstrap
    return bootstrap().math.domains


def test_domain_registry_globals_are_absent():
    assert not hasattr(base, "_DOMAINS")
    assert not hasattr(base, "_SCOPES")
    assert not hasattr(base, "register")
    assert not hasattr(base, "domain_scope")


def test_import_has_no_registration_side_effect():
    code = (
        "import cas.math.domains.base as base; "
        "print(hasattr(base, '_DOMAINS'), hasattr(base, '_SCOPES'))"
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, cwd="."
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "False False"


def test_bootstrap_builds_three_base_domains():
    catalog = _catalog()
    assert tuple(domain.name for domain in catalog.resident) == ("Z", "Q", "Q(i)")


def test_two_runs_have_independent_catalogs():
    first = _catalog()
    second = _catalog()
    assert first is not second
    assert tuple(domain.name for domain in first.resident) == tuple(
        domain.name for domain in second.resident)
    assert tuple(type(domain) for domain in first.resident) == tuple(
        type(domain) for domain in second.resident)


def test_parameterized_domains_do_not_enter_resident_catalog():
    from cas.math.domains.poly import poly_domain
    from cas.math.domains.ratfunc import ratfunc_domain

    catalog = _catalog()
    ring = catalog.require_unique(
        lambda domain: (
            domain.is_field and domain.is_ordered and domain.is_euclidean
            and domain.ring is not None
        ),
        "test field",
    ).ring
    assert ring is not None
    for variable in (S("x"), S("y"), S("unique_variable")):
        poly_domain(variable, ring=ring)
        ratfunc_domain(variable, ring=ring)
    assert tuple(domain.name for domain in catalog.resident) == ("Z", "Q", "Q(i)")


def test_projection_catalog_lookup():
    catalog = _catalog()
    for name, class_name in (("Z", "ZDomain"), ("Q", "QDomain"), ("Q(i)", "QIDomain")):
        domain = catalog.lookup(name)
        assert domain is not None
        assert type(domain).__name__ == class_name


def test_factory_cache_reuses_same_variable_set():
    from cas.math.domains.poly import poly_domain
    from cas.math.domains.ratfunc import ratfunc_domain

    catalog = _catalog()
    field = catalog.require_unique(
        lambda domain: domain.is_field and domain.is_ordered and domain.ring is not None,
        "test field",
    )
    assert field.ring is not None
    ring = field.ring
    assert poly_domain(S("x"), ring=ring) is poly_domain(S("x"), ring=ring)
    assert ratfunc_domain(S("x"), ring=ring) is ratfunc_domain(S("x"), ring=ring)
    assert poly_domain(S("x"), ring=ring) is not poly_domain(S("y"), ring=ring)


def test_scoped_domain_is_an_explicit_catalog_value():
    class ScopedDomain(Domain):
        name = "ScopedTest"
        capabilities = DomainCapabilities(scoped=True)

        def member(self, term):
            return True

        def normalize(self, term):
            return term

        def equal(self, left, right):
            return left is right

    catalog = _catalog()
    scoped = ScopedDomain()
    scoped_catalog = catalog.with_scoped(scoped)
    assert scoped_catalog.lookup(scoped.name) is scoped
    assert catalog.lookup(scoped.name) is None


def test_scoped_domain_cannot_be_resident():
    class ScopedDomain(Domain):
        name = "ScopedResident"
        capabilities = DomainCapabilities(scoped=True)

        def member(self, term):
            return True

        def normalize(self, term):
            return term

        def equal(self, left, right):
            return left is right

    try:
        DomainCatalog(resident=(ScopedDomain(),))
    except ValueError as error:
        assert "scoped" in str(error)
    else:
        raise AssertionError("a scoped domain entered the resident catalog")
