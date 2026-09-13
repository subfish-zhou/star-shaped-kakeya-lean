#!/usr/bin/env python3
"""Fail-closed Arb interval certificate for the joint inner/outer lower bound.

Run with the python-flint interpreter::

    /home/argustest/research/star-shaped-kakeya/.venv/bin/python \
        spikes/001-joint-inner-outer/certify.py

Evidence level.  This script proves Hypothesis B (parameter domain) and
Hypothesis C (four numerical gates) of ``PROOF.md`` for one fixed rational
parameter tuple, using Arb/FLINT outward-rounded interval arithmetic.  It
proves nothing about star-shaped Kakeya sets; the bridge from Hypothesis C to
the geometric statement is the paper proof in ``PROOF.md``, which is not
machine checked.

Soundness discipline.

*   Every primary input is an exact ``fractions.Fraction``.  The fixed
    certificate path never converts a binary float, and a static AST and
    call-graph regression guard (``fixed_path_guard``) fails the run if a
    float/complex literal, an exact integer true division such as ``1/2``, an
    alias of ``float``/``complex``/``round``, a dynamic escape (``eval``,
    ``exec``, ``compile``, ``getattr``, ``__import__``), a dunder access, an
    import, a lambda or a call to an uninspected helper appears on that path.
    The guard is fail-closed -- an unrecognised call target is a rejection --
    and is exercised by executable negative controls in ``run_guard_controls``.
    It is a regression guard, **not** a proof: bytecode rewriting, C-extension
    inexactness and a compromised ``flint`` build are outside its reach.
*   Every radical, denominator, arcsine argument and order relation is checked
    as a strict interval sign before it is used.  A box that cannot be decided
    raises, and a raise is a rejection, never a pass.
*   The radial integral is bounded from below by an exact-rational partition
    with an Arb-native per-cell hull of the three branches of ``g``; only the
    lower endpoint of the resulting sum is used.
*   Gate comparisons use Arb's certified strict comparisons, which are true
    only when the relation holds for every point of the enclosure.
"""
from __future__ import annotations

import ast
import builtins
import hashlib
import inspect
import json
import sys
import textwrap
import time
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

PRECISION_BITS = 256
ctx.prec = PRECISION_BITS

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "certificate.json"

INTEGRAL_CELLS = 1 << 16

#: Primary fixed parameters of the candidate witness.  Exact rationals only.
PRODUCTION_PARAMETERS: dict[str, Fraction] = {
    "h0": Fraction(13177, 100000),
    "r_lambda": Fraction(10227, 50000),
    "r0": Fraction(999, 2000),
    "eps_del": Fraction(1, 10 ** 10),
    "target": Fraction(131, 6250),
    "exterior_divisor": Fraction(4),
}

#: Gates that the production checker requires to be present and passing.
MANDATORY_GATES: tuple[str, ...] = (
    "domain_h0_positive",
    "domain_order_h0_rlambda",
    "domain_order_rlambda_r0",
    "domain_r0_below_half",
    "domain_r0_at_least_three_twentieths",
    "domain_lambda_in_unit_interval",
    "domain_lambda_interpolation_exact",
    "domain_Q_nonnegative",
    "domain_Q_below_one",
    "domain_d_positive",
    "domain_d_below_half_h0",
    "domain_rlambda_sq_minus_d_sq_positive",
    "domain_R1_denominator_positive",
    "domain_R1_above_one",
    "domain_rho_above_r0",
    "domain_h0_below_m_rho",
    "domain_asin_arg_rho_positive",
    "domain_asin_arg_rho_below_one",
    "domain_asin_arg_m_rho_positive",
    "domain_asin_arg_m_rho_below_one",
    "C_ext_positive",
    "gate_C1_high_above_target",
    "gate_C2_integral_above_target",
    "gate_C3_exterior_above_target",
    "gate_C4_fan_above_target",
)


# ---------------------------------------------------------------------------
# Fixed certificate path.  Everything below up to `run_certificate` is covered
# by `fixed_path_guard` and must stay free of binary-float arithmetic.
# ---------------------------------------------------------------------------

def arb_frac(q: Fraction) -> arb:
    """Enclose an exact rational; no binary-float endpoint is constructed."""
    q = Fraction(q)
    return arb(q.numerator) / arb(q.denominator)


def iv_frac(left: Fraction, right: Fraction) -> arb:
    """Outward hull of two exact rational endpoints."""
    return arb_frac(left).union(arb_frac(right))


def certainly_gt(x: arb, y: arb) -> bool:
    """True only when every point of `x` exceeds every point of `y`."""
    return bool(x > y)


def certainly_lt(x: arb, y: arb) -> bool:
    """True only when every point of `x` is below every point of `y`."""
    return bool(x < y)


def require_gt(x: arb, y: arb, what: str) -> None:
    if not certainly_gt(x, y):
        raise ValueError("undecided or false strict lower sign: " + what)


def geometry_intervals(h0: Fraction, r_lambda: Fraction) -> dict[str, arb]:
    """Derived radii, with every radical and denominator sign-checked first."""
    a = arb_frac(h0)
    rl = arb_frac(r_lambda)
    zero = arb(0)
    one = arb(1)
    radicand = 4 * rl * rl * (one + a * a) - a * a
    require_gt(radicand, zero, "Q must be strictly positive before sqrt")
    require_gt(one, radicand, "Q must be strictly below one")
    d = a * (one - radicand.sqrt()) / (2 * (one + a * a))
    require_gt(d, zero, "d must be strictly positive")
    inner = rl * rl - d * d
    require_gt(inner, zero, "r_lambda^2 - d^2 must be strictly positive")
    denominator = one - 2 * inner.sqrt()
    require_gt(denominator, zero, "R1 denominator must be strictly positive")
    R1 = (one + 4 * d * d).sqrt() / denominator
    require_gt(R1, one, "R1 must exceed one")
    rho = R1 - one
    return {
        "radicand": radicand,
        "d": d,
        "inner": inner,
        "denominator": denominator,
        "R1": R1,
        "rho": rho,
    }


def integrand_cell(r: arb, frozen_branch: arb) -> tuple[arb, arb]:
    """Two enclosures of `r / g(r)` on a radial cell.

    The first uses the Arb-native hull of the three branches of `g`; its lower
    endpoint is a valid lower bound of the integrand on the cell, because the
    hull's upper endpoint dominates the cellwise maximum of `g`.  The second
    divides by the exact greatest branch lower endpoint, which is a valid lower
    bound of `g` on the cell, so its upper endpoint dominates the integrand.
    """
    one = arb(1)
    zero = arb(0)
    interior_denominator = one - 2 * r
    require_gt(interior_denominator, zero, "interior branch denominator")
    interior = (one + 2 * r) / interior_denominator
    angle_denominator = arb.pi() / 2 - (2 * r).atan()
    require_gt(angle_denominator, zero, "angle branch denominator")
    angle = arb.pi() / angle_denominator
    hull = interior.union(frozen_branch).union(angle)
    require_gt(hull, one, "g hull must exceed one on the cell")
    greatest = interior.lower()
    for candidate in (frozen_branch.lower(), angle.lower()):
        if bool(candidate > greatest):
            greatest = candidate
    require_gt(greatest, one, "greatest branch minorant must exceed one")
    return r / hull, r / greatest


def integral_bounds(h0: Fraction, r_lambda: Fraction, r0: Fraction,
                    cells: int) -> tuple[arb, arb]:
    """Outward enclosure of the raw radial integral over an exact partition."""
    one = arb(1)
    zero = arb(0)
    rl = arb_frac(r_lambda)
    frozen_denominator = one - 2 * rl
    require_gt(frozen_denominator, zero, "frozen branch denominator")
    frozen_branch = (one + 2 * rl) / frozen_denominator
    step = (Fraction(r0) - Fraction(h0)) / cells
    step_enclosure = arb_frac(step)
    lower_total = arb(0)
    upper_total = arb(0)
    left = Fraction(h0)
    for _ in range(cells):
        right = left + step
        low, high = integrand_cell(iv_frac(left, right), frozen_branch)
        lower_total = lower_total + low * step_enclosure
        upper_total = upper_total + high * step_enclosure
        left = right
    return lower_total.lower(), upper_total.upper()


def coefficient_intervals(h0: Fraction, r0: Fraction, eps_del: Fraction,
                          exterior_divisor: Fraction,
                          rho: arb) -> dict[str, arb]:
    """The four gate quantities plus the arcsine arguments they depend on."""
    a = arb_frac(h0)
    radius = arb_frac(r0)
    m = arb_frac(Fraction(1) - Fraction(eps_del))
    zero = arb(0)
    one = arb(1)
    arg_rho = a / rho
    arg_m_rho = a / (m * rho)
    require_gt(arg_rho, zero, "h0/rho positive")
    require_gt(one, arg_rho, "h0/rho below one")
    require_gt(arg_m_rho, zero, "h0/(m rho) positive")
    require_gt(one, arg_m_rho, "h0/(m rho) below one")
    half_width = arg_m_rho.asin()
    require_gt(half_width, zero, "H(h0) positive")
    C_ext = a / (2 * half_width) - m * radius * radius / 2
    return {
        "m": m,
        "arg_rho": arg_rho,
        "arg_m_rho": arg_m_rho,
        "H_h0": half_width,
        "C_ext": C_ext,
        "exterior_rate": C_ext / arb_frac(exterior_divisor),
        "C_fan": (rho * rho - radius * radius) / 2,
        "high": a / (2 * arb.pi()),
    }


def _decimal(x: arb) -> str:
    return x.str(30, radius=False)


def _gate(name: str, kind: str, passed: bool, left: arb, right: arb) -> dict:
    margin = left - right if kind == "gt" else right - left
    return {
        "name": name,
        "kind": kind,
        "passed": bool(passed),
        "left_interval": str(left),
        "right_interval": str(right),
        "left_lower": _decimal(left.lower()),
        "left_upper": _decimal(left.upper()),
        "margin_lower": _decimal(margin.lower()),
    }


def gate_gt(name: str, left: arb, right: arb) -> dict:
    return _gate(name, "gt", certainly_gt(left, right), left, right)


def gate_lt(name: str, left: arb, right: arb) -> dict:
    return _gate(name, "lt", certainly_lt(left, right), left, right)


def gate_exact(name: str, passed: bool, detail: str) -> dict:
    return {
        "name": name,
        "kind": "exact-rational",
        "passed": bool(passed),
        "detail": detail,
    }


def run_certificate(parameters: dict[str, Fraction],
                    cells: int = INTEGRAL_CELLS) -> dict:
    """Evaluate every gate for one exact rational parameter tuple."""
    for key, value in parameters.items():
        if not isinstance(value, Fraction):
            raise TypeError("non-exact parameter on certificate path: " + key)
    h0 = parameters["h0"]
    r_lambda = parameters["r_lambda"]
    r0 = parameters["r0"]
    eps_del = parameters["eps_del"]
    target = parameters["target"]
    exterior_divisor = parameters["exterior_divisor"]
    report: dict = {
        "parameters": {k: [v.numerator, v.denominator]
                       for k, v in parameters.items()},
        "precision_bits": PRECISION_BITS,
        "integral_cells": cells,
        "gates": [],
    }
    gates: list[dict] = report["gates"]
    zero = arb(0)
    one = arb(1)
    half = one / 2
    a = arb_frac(h0)
    rl = arb_frac(r_lambda)
    radius = arb_frac(r0)
    threshold = arb_frac(target)

    gates.append(gate_gt("domain_h0_positive", a, zero))
    gates.append(gate_gt("domain_order_h0_rlambda", rl, a))
    gates.append(gate_gt("domain_order_rlambda_r0", radius, rl))
    gates.append(gate_lt("domain_r0_below_half", radius, half))
    gates.append(gate_gt("domain_r0_at_least_three_twentieths",
                         radius, arb_frac(Fraction(3, 20))))
    if r0 == h0:
        lam = None
        lam_ok = False
        lam_detail = "r0 == h0, interpolation undefined"
    else:
        lam = (Fraction(r0) - Fraction(r_lambda)) / (Fraction(r0) - Fraction(h0))
        lam_ok = Fraction(0) < lam < Fraction(1)
        lam_detail = "lambda = " + str(lam.numerator) + "/" + str(lam.denominator)
    gates.append(gate_exact("domain_lambda_in_unit_interval", lam_ok, lam_detail))
    if lam is None:
        interp_ok = False
        interp_detail = "not evaluated"
    else:
        interp = lam * Fraction(h0) + (Fraction(1) - lam) * Fraction(r0)
        interp_ok = interp == Fraction(r_lambda)
        interp_detail = ("lambda*h0 + (1-lambda)*r0 = "
                         + str(interp.numerator) + "/" + str(interp.denominator))
    gates.append(gate_exact("domain_lambda_interpolation_exact",
                            interp_ok, interp_detail))

    try:
        geometry = geometry_intervals(h0, r_lambda)
    except ValueError as exc:
        report["status"] = "domain-abort"
        report["abort_reason"] = str(exc)
        gates.append(gate_exact("evaluation_completed", False, str(exc)))
        return report

    radicand = geometry["radicand"]
    d = geometry["d"]
    inner = geometry["inner"]
    denominator = geometry["denominator"]
    R1 = geometry["R1"]
    rho = geometry["rho"]
    gates.append(gate_gt("domain_Q_nonnegative", radicand, zero))
    gates.append(gate_lt("domain_Q_below_one", radicand, one))
    gates.append(gate_gt("domain_d_positive", d, zero))
    gates.append(gate_lt("domain_d_below_half_h0", d, a / 2))
    gates.append(gate_gt("domain_rlambda_sq_minus_d_sq_positive", inner, zero))
    gates.append(gate_gt("domain_R1_denominator_positive", denominator, zero))
    gates.append(gate_gt("domain_R1_above_one", R1, one))
    gates.append(gate_gt("domain_rho_above_r0", rho, radius))

    m = arb_frac(Fraction(1) - Fraction(eps_del))
    gates.append(gate_lt("domain_h0_below_m_rho", a, m * rho))

    try:
        coefficients = coefficient_intervals(h0, r0, eps_del,
                                             exterior_divisor, rho)
    except ValueError as exc:
        report["status"] = "domain-abort"
        report["abort_reason"] = str(exc)
        gates.append(gate_exact("evaluation_completed", False, str(exc)))
        return report

    gates.append(gate_gt("domain_asin_arg_rho_positive",
                         coefficients["arg_rho"], zero))
    gates.append(gate_lt("domain_asin_arg_rho_below_one",
                         coefficients["arg_rho"], one))
    gates.append(gate_gt("domain_asin_arg_m_rho_positive",
                         coefficients["arg_m_rho"], zero))
    gates.append(gate_lt("domain_asin_arg_m_rho_below_one",
                         coefficients["arg_m_rho"], one))
    gates.append(gate_gt("C_ext_positive", coefficients["C_ext"], zero))

    try:
        integral, integral_upper = integral_bounds(h0, r_lambda, r0, cells)
    except ValueError as exc:
        report["status"] = "domain-abort"
        report["abort_reason"] = str(exc)
        gates.append(gate_exact("evaluation_completed", False, str(exc)))
        return report

    gates.append(gate_gt("gate_C1_high_above_target",
                         coefficients["high"], threshold))
    gates.append(gate_gt("gate_C2_integral_above_target", integral, threshold))
    gates.append(gate_gt("gate_C3_exterior_above_target",
                         coefficients["exterior_rate"], threshold))
    gates.append(gate_gt("gate_C4_fan_above_target",
                         coefficients["C_fan"], threshold))
    gates.append(gate_exact("evaluation_completed", True,
                            "all interval stages evaluated"))

    joint = integral
    for candidate in (coefficients["exterior_rate"].lower(),
                      coefficients["C_fan"].lower(),
                      coefficients["high"].lower()):
        if bool(candidate < joint):
            joint = candidate

    report["status"] = "evaluated"
    report["intervals"] = {
        "Q": str(radicand),
        "d": str(d),
        "r_lambda_sq_minus_d_sq": str(inner),
        "R1_denominator": str(denominator),
        "R1": str(R1),
        "rho": str(rho),
        "m": str(m),
        "h0_over_rho": str(coefficients["arg_rho"]),
        "h0_over_m_rho": str(coefficients["arg_m_rho"]),
        "H_h0": str(coefficients["H_h0"]),
        "C_ext": str(coefficients["C_ext"]),
        "exterior_rate": str(coefficients["exterior_rate"]),
        "C_fan": str(coefficients["C_fan"]),
        "high": str(coefficients["high"]),
        "integral_I": str(integral.union(integral_upper)),
        "joint_coefficient": str(joint),
        "target": str(threshold),
    }
    report["integral_enclosure"] = {
        "lower": _decimal(integral),
        "upper": _decimal(integral_upper),
        "width": _decimal(integral_upper - integral),
        "note": ("lower endpoint from the Arb-native branch hull, upper "
                 "endpoint from the greatest exact branch minorant; only the "
                 "lower endpoint enters gate C2"),
    }
    report["lower_bounds"] = {
        "rho": _decimal(rho.lower()),
        "C_ext": _decimal(coefficients["C_ext"].lower()),
        "high": _decimal(coefficients["high"].lower()),
        "integral_I": _decimal(integral),
        "exterior_rate": _decimal(coefficients["exterior_rate"].lower()),
        "C_fan": _decimal(coefficients["C_fan"].lower()),
        "joint_coefficient": _decimal(joint),
    }
    report["margins_above_target_lower"] = {
        "high": _decimal((coefficients["high"] - threshold).lower()),
        "integral_I": _decimal((integral - threshold).lower()),
        "exterior_rate": _decimal((coefficients["exterior_rate"] - threshold).lower()),
        "C_fan": _decimal((coefficients["C_fan"] - threshold).lower()),
        "joint_coefficient": _decimal((joint - threshold).lower()),
    }
    report["area_lower_bound"] = {
        "expression": "pi * min(h0/(2 pi), I, C_ext/4, C_fan)",
        "lower": _decimal((arb.pi() * joint).lower()),
        "target_pi_T_upper": _decimal((arb.pi() * threshold).upper()),
        "strictly_above_target": bool(arb.pi() * joint > arb.pi() * threshold),
    }
    return report


# ---------------------------------------------------------------------------
# Production checker, guard and mutation controls (not on the fixed path).
# ---------------------------------------------------------------------------

FIXED_PATH_FUNCTIONS = (
    arb_frac,
    iv_frac,
    certainly_gt,
    certainly_lt,
    require_gt,
    geometry_intervals,
    integrand_cell,
    integral_bounds,
    coefficient_intervals,
    _decimal,
    _gate,
    gate_gt,
    gate_lt,
    gate_exact,
    run_certificate,
)

#: Callables that may be invoked by name on the fixed path.  Every one of them
#: is an exact constructor, an exact predicate, or a non-numeric utility.  The
#: mapping is checked by identity at guard time, so rebinding any of these
#: names to another object is itself a rejection.
EXACT_CALL_WHITELIST: dict[str, object] = {
    "arb": arb,
    "Fraction": Fraction,
    "bool": builtins.bool,
    "isinstance": builtins.isinstance,
    "range": builtins.range,
    "str": builtins.str,
    "TypeError": builtins.TypeError,
    "ValueError": builtins.ValueError,
}

#: Method names that may be invoked on the fixed path.  `sqrt`, `asin`, `atan`,
#: `union`, `lower`, `upper`, `pi` and `str` are Arb operations with outward
#: rounding; `append` and `items` are container utilities.
EXACT_METHOD_WHITELIST = frozenset({
    "sqrt", "asin", "atan", "union", "lower", "upper", "pi", "str",
    "append", "items",
})

#: Names that must never appear as a load on the fixed path, whether they are
#: called directly or merely aliased.  Aliasing (`f = float`) is caught because
#: the right-hand side is itself a load of a forbidden name.
FORBIDDEN_NAMES = frozenset({
    "float", "complex", "round", "eval", "exec", "compile", "getattr",
    "setattr", "delattr", "globals", "locals", "vars", "open", "input",
    "breakpoint", "memoryview", "math", "numpy", "np", "decimal", "Decimal",
})

#: Objects that must never be reachable from a load on the fixed path, checked
#: by identity after resolving the name through closure, globals and builtins.
FORBIDDEN_OBJECTS = tuple(
    obj for obj in (
        builtins.float, builtins.complex, builtins.round, builtins.eval,
        builtins.exec, builtins.compile, builtins.getattr, builtins.setattr,
        builtins.delattr, builtins.globals, builtins.locals, builtins.vars,
        builtins.open, builtins.input, builtins.__import__,
    ) if obj is not None
)

#: Statements and expression forms with no place in exact interval arithmetic.
_FORBIDDEN_NODE_KINDS = (
    (ast.Import, "import-statement"),
    (ast.ImportFrom, "import-statement"),
    (ast.Global, "global-or-nonlocal"),
    (ast.Nonlocal, "global-or-nonlocal"),
    (ast.Lambda, "lambda"),
)


def _is_static_int_expr(node: ast.AST) -> bool:
    """True when the node is a compile-time integer arithmetic expression.

    `True`/`False` are excluded even though `bool` subclasses `int`, because a
    boolean never participates in the radial arithmetic.
    """
    if isinstance(node, ast.Constant):
        return isinstance(node.value, int) and not isinstance(node.value, bool)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        return _is_static_int_expr(node.operand)
    if isinstance(node, ast.BinOp) and isinstance(
            node.op, (ast.Add, ast.Sub, ast.Mult, ast.Pow, ast.FloorDiv, ast.Mod)):
        return _is_static_int_expr(node.left) and _is_static_int_expr(node.right)
    return False


def _resolve_name(function, name: str):
    """Resolve a name through closure, then module globals, then builtins."""
    freevars = function.__code__.co_freevars
    if name in freevars and function.__closure__ is not None:
        cell = function.__closure__[freevars.index(name)]
        try:
            return cell.cell_contents
        except ValueError:
            return None
    module_globals = function.__globals__
    if name in module_globals:
        return module_globals[name]
    declared = module_globals.get("__builtins__")
    if isinstance(declared, dict) and name in declared:
        return declared[name]
    return vars(builtins).get(name)


def _is_dunder(name: str) -> bool:
    return name.startswith("__") and name.endswith("__")


def _inspect_fixed_path_function(function, inspected_names: dict) -> tuple[list, list]:
    """Return (findings, outgoing call edges) for one fixed-path function."""
    findings: list[dict] = []
    edges: list[str] = []
    name = function.__name__

    def flag(kind: str, detail: str) -> None:
        findings.append({"function": name, "kind": kind, "detail": detail})

    try:
        source = textwrap.dedent(inspect.getsource(function))
        tree = ast.parse(source)
    except (OSError, TypeError, SyntaxError) as exc:
        flag("source-unavailable", type(exc).__name__ + ": " + str(exc))
        return findings, edges

    for node in ast.walk(tree):
        for node_type, kind in _FORBIDDEN_NODE_KINDS:
            if isinstance(node, node_type):
                flag(kind, ast.dump(node)[:120])

        if isinstance(node, ast.Constant):
            if isinstance(node.value, (builtins.float, builtins.complex)):
                flag("float-or-complex-literal", repr(node.value))

        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            if _is_static_int_expr(node.left) and _is_static_int_expr(node.right):
                flag("exact-int-true-division",
                     ast.unparse(node) if hasattr(ast, "unparse") else "int/int")

        if isinstance(node, ast.Attribute):
            if _is_dunder(node.attr):
                flag("dunder-attribute", node.attr)

        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            if node.id in FORBIDDEN_NAMES:
                flag("forbidden-name", node.id)
            elif _is_dunder(node.id):
                flag("dunder-name", node.id)
            else:
                resolved = _resolve_name(function, node.id)
                if any(resolved is bad for bad in FORBIDDEN_OBJECTS):
                    flag("forbidden-object-alias",
                         node.id + " -> " + getattr(resolved, "__name__", repr(resolved)))

        if isinstance(node, ast.Call):
            target = node.func
            if isinstance(target, ast.Name):
                edges.append(target.id)
                if target.id in EXACT_CALL_WHITELIST:
                    expected = EXACT_CALL_WHITELIST[target.id]
                    if _resolve_name(function, target.id) is not expected:
                        flag("whitelisted-name-rebound", target.id)
                elif target.id in inspected_names:
                    if _resolve_name(function, target.id) is not inspected_names[target.id]:
                        flag("call-target-object-mismatch", target.id)
                else:
                    flag("uninspected-call-target", target.id)
            elif isinstance(target, ast.Attribute):
                edges.append("." + target.attr)
                if target.attr not in EXACT_METHOD_WHITELIST:
                    flag("unwhitelisted-method-call", target.attr)
            else:
                flag("non-static-call-target", type(target).__name__)

    return findings, edges


def fixed_path_guard() -> dict:
    """AST and call-graph exactness regression guard for the fixed path.

    This is a **regression guard, not a mathematical proof**.  It statically
    rejects the constructs by which a binary float could enter the certificate
    path -- float/complex literals in any notation, statically exact integer
    true divisions such as `1/2`, loads or aliases of `float`/`complex`/
    `round`, dynamic escapes (`eval`, `exec`, `compile`, `getattr`,
    `__import__`), dunder access, imports and lambdas -- and it closes the call
    graph, so a helper that is not itself inspected cannot be invoked from the
    fixed path.

    It is deliberately fail-closed: an unknown call target is a rejection
    rather than an allowance.  It is *not* a claim that no conceivable Python
    metaprogramming can evade it; bytecode rewriting, C extensions returning
    inexact values, or a compromised `flint` build are all outside its reach.
    The mathematical content of the certificate rests on Arb's outward
    rounding and on `PROOF.md`, not on this function.
    """
    inspected_names = {f.__name__: f for f in FIXED_PATH_FUNCTIONS}
    duplicates = len(inspected_names) != len(FIXED_PATH_FUNCTIONS)
    findings: list[dict] = []
    call_graph: dict[str, list] = {}
    if duplicates:
        findings.append({"function": "<registry>", "kind": "duplicate-registration",
                         "detail": "FIXED_PATH_FUNCTIONS contains repeated names"})
    for function in FIXED_PATH_FUNCTIONS:
        function_findings, edges = _inspect_fixed_path_function(function, inspected_names)
        findings.extend(function_findings)
        call_graph[function.__name__] = sorted(set(edges))
    return {
        "guard_kind": "AST and call-graph exactness regression guard",
        "not_a_proof": (
            "static regression guard only; does not exclude bytecode "
            "rewriting, C-extension inexactness, or a compromised flint build"),
        "inspected_functions": sorted(inspected_names),
        "exact_call_whitelist": sorted(EXACT_CALL_WHITELIST),
        "exact_method_whitelist": sorted(EXACT_METHOD_WHITELIST),
        "forbidden_names": sorted(FORBIDDEN_NAMES),
        "rejected_constructs": [
            "float or complex literal in any notation, including 1e-3",
            "statically exact integer true division such as 1/2",
            "load or alias of float, complex, round or a dynamic escape",
            "dunder name or dunder attribute access",
            "import, lambda, global/nonlocal, computed call target",
            "call to a function outside the inspected call graph",
        ],
        "known_limitations": [
            "name-resolution of a Div operand is not attempted, so a runtime "
            "int/int division through two variables is not detected statically",
            "correctness of Arb itself is assumed, not verified",
        ],
        "call_graph": call_graph,
        "findings": findings,
        "passed": not findings,
    }


# ---------------------------------------------------------------------------
# Executable negative controls for the guard.  These functions are deliberately
# defective and are never called by the certificate; they exist only so that
# `run_guard_controls` can demonstrate that the guard rejects them.
# ---------------------------------------------------------------------------

def _control_uninspected_helper_target(value):
    """A helper that is intentionally absent from FIXED_PATH_FUNCTIONS."""
    return value


def _control_float_literal(value):
    scientific_notation = 1e-3
    plain_float = 0.5
    return value * scientific_notation * plain_float


def _control_exact_int_division(value):
    return value * (1 / 2)


def _control_float_alias(value):
    f = float
    return f(value)


def _control_uninspected_helper(value):
    return _control_uninspected_helper_target(value)


def _control_dynamic_escape(value):
    return eval("value + 1")


GUARD_CONTROLS = (
    {
        "name": "scientific_notation_float_literal",
        "function": _control_float_literal,
        "expected_kinds": ["float-or-complex-literal"],
        "description": "1e-3 and 0.5 must both be rejected as float literals",
    },
    {
        "name": "exact_int_true_division",
        "function": _control_exact_int_division,
        "expected_kinds": ["exact-int-true-division"],
        "description": "1/2 evaluates to a binary float and must be rejected",
    },
    {
        "name": "float_constructor_alias",
        "function": _control_float_alias,
        "expected_kinds": ["forbidden-name", "uninspected-call-target"],
        "description": "f = float; f(x) must be rejected through the alias",
    },
    {
        "name": "uninspected_helper",
        "function": _control_uninspected_helper,
        "expected_kinds": ["uninspected-call-target"],
        "description": "a helper outside FIXED_PATH_FUNCTIONS must not be callable",
    },
    {
        "name": "dynamic_escape_eval",
        "function": _control_dynamic_escape,
        "expected_kinds": ["forbidden-name"],
        "description": "eval must be rejected on the fixed path",
    },
)


def run_guard_controls() -> list[dict]:
    """Check that the guard actually rejects each deliberately defective case.

    Each control is inspected with exactly the production inspection routine,
    against the production whitelists, so a control passing is evidence about
    the real guard rather than about a copy of it.
    """
    inspected_names = {f.__name__: f for f in FIXED_PATH_FUNCTIONS}
    results = []
    for control in GUARD_CONTROLS:
        function = control["function"]
        if function.__name__ in inspected_names:
            results.append({
                "name": control["name"],
                "control_passed": False,
                "detail": "control function is registered on the fixed path",
            })
            continue
        findings, _edges = _inspect_fixed_path_function(function, inspected_names)
        kinds = sorted({finding["kind"] for finding in findings})
        matched = all(kind in kinds for kind in control["expected_kinds"])
        results.append({
            "name": control["name"],
            "description": control["description"],
            "inspected_function": function.__name__,
            "expected_kinds": control["expected_kinds"],
            "observed_kinds": kinds,
            "observed_findings": findings,
            "rejected_by_guard": bool(findings),
            "expected_kinds_matched": bool(matched),
            "control_passed": bool(findings) and bool(matched),
        })
    return results


def check_gates(report: dict) -> dict:
    """The single production acceptance decision, used for every run."""
    gates = {gate["name"]: gate for gate in report.get("gates", [])}
    missing = [name for name in MANDATORY_GATES if name not in gates]
    failed = [name for name, gate in gates.items() if not gate["passed"]]
    completed = gates.get("evaluation_completed", {}).get("passed", False)
    evaluated = report.get("status") == "evaluated"
    accepted = (evaluated and (not missing) and (not failed)
                and bool(completed))
    if accepted:
        reason = "all mandatory gates present and passing"
    elif not evaluated:
        reason = "evaluation did not complete"
    else:
        reason = "missing or failing gates"
    return {
        "accepted": accepted,
        "reason": reason,
        "abort_reason": report.get("abort_reason"),
        "missing_gates": missing,
        "failed_gates": sorted(failed),
    }


def parameter_digest(parameters: dict[str, Fraction]) -> str:
    canonical = json.dumps(
        {k: str(v.numerator) + "/" + str(v.denominator)
         for k, v in sorted(parameters.items())},
        sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


MUTATIONS = (
    {
        "name": "target_raised",
        "description": "raise the target from 131/6250 to 21/1000",
        "overrides": {"target": Fraction(21, 1000)},
        "expected_failed_gates": ["gate_C1_high_above_target",
                                  "gate_C2_integral_above_target"],
    },
    {
        "name": "h0_lowered",
        "description": "lower the height threshold h0 from 13177/100000 to 3/25",
        "overrides": {"h0": Fraction(3, 25)},
        "expected_failed_gates": ["gate_C1_high_above_target"],
    },
    {
        "name": "exterior_coefficient_weakened",
        "description": "weaken the selected exterior rate from C_ext/4 to C_ext/40",
        "overrides": {"exterior_divisor": Fraction(40)},
        "expected_failed_gates": ["gate_C3_exterior_above_target"],
    },
    {
        "name": "r0_outside_domain",
        "description": "raise r0 to 7/10, which violates r0 < 1/2 and rho > r0",
        "overrides": {"r0": Fraction(7, 10)},
        "expected_failed_gates": ["domain_r0_below_half"],
    },
)


def run_mutations(cells: int) -> list[dict]:
    results = []
    for mutation in MUTATIONS:
        parameters = dict(PRODUCTION_PARAMETERS)
        parameters.update(mutation["overrides"])
        report = run_certificate(parameters, cells=cells)
        decision = check_gates(report)
        failed = set(decision["failed_gates"]) | set(decision["missing_gates"])
        matched = all(name in failed for name in mutation["expected_failed_gates"])
        results.append({
            "name": mutation["name"],
            "description": mutation["description"],
            "overrides": {k: [v.numerator, v.denominator]
                          for k, v in mutation["overrides"].items()},
            "expected_failed_gates": mutation["expected_failed_gates"],
            "observed_failed_gates": decision["failed_gates"],
            "observed_missing_gates": decision["missing_gates"],
            "status": report.get("status"),
            "abort_reason": report.get("abort_reason"),
            "rejected_by_production_checker": not decision["accepted"],
            "mutation_matched": bool(matched),
            "control_passed": bool(matched) and not decision["accepted"],
        })
    return results


def main() -> int:
    started = time.time()
    guard = fixed_path_guard()
    mutation_cells = 1 << 12
    production = run_certificate(PRODUCTION_PARAMETERS, cells=INTEGRAL_CELLS)
    decision = check_gates(production)
    mutations = run_mutations(cells=mutation_cells)
    guard_controls = run_guard_controls()
    mutations_ok = all(entry["control_passed"] for entry in mutations)
    guard_controls_ok = all(entry["control_passed"] for entry in guard_controls)
    overall = bool(guard["passed"] and decision["accepted"]
                   and mutations_ok and guard_controls_ok)
    certificate = {
        "artifact": "spike-001 joint inner/outer fixed-witness Arb certificate",
        "evidence_level": "interval certificate for Hypotheses B and C of PROOF.md",
        "proves_geometric_theorem": False,
        "precision_bits": PRECISION_BITS,
        "arb_rounding": "Arb/FLINT outward-rounded intervals",
        "integral_cells_production": INTEGRAL_CELLS,
        "integral_cells_mutation_controls": mutation_cells,
        "parameter_sha256": parameter_digest(PRODUCTION_PARAMETERS),
        "script_sha256": file_digest(Path(__file__).resolve()),
        "primary_parameters": {k: str(v.numerator) + "/" + str(v.denominator)
                               for k, v in sorted(PRODUCTION_PARAMETERS.items())},
        "fixed_path_guard": guard,
        "fixed_path_guard_controls": guard_controls,
        "all_guard_controls_passed": guard_controls_ok,
        "production": production,
        "production_decision": decision,
        "mutation_controls": mutations,
        "all_mutation_controls_passed": mutations_ok,
        "accepted": overall,
        "elapsed_seconds": time.time() - started,
        "non_claims": [
            "no optimality or global search claim for the parameter tuple",
            "no Lean theorem is asserted or implied",
            "the geometric bridge is the paper proof in PROOF.md",
            "the fixed-path guard is a static AST and call-graph regression "
            "guard, not a proof that binary floats are impossible",
        ],
    }
    OUT.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
    summary = {
        "accepted": overall,
        "fixed_path_guard_passed": guard["passed"],
        "fixed_path_guard_controls": [
            {"name": entry["name"],
             "rejected": entry.get("rejected_by_guard"),
             "matched": entry.get("expected_kinds_matched")}
            for entry in guard_controls],
        "production_decision": decision,
        "joint_coefficient_lower": production.get("lower_bounds", {})
                                             .get("joint_coefficient"),
        "joint_margin_above_target_lower": production
            .get("margins_above_target_lower", {}).get("joint_coefficient"),
        "mutation_controls": [
            {"name": entry["name"],
             "rejected": entry["rejected_by_production_checker"],
             "matched": entry["mutation_matched"]}
            for entry in mutations],
        "certificate": str(OUT),
        "elapsed_seconds": round(certificate["elapsed_seconds"], 3),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if overall else 1


if __name__ == "__main__":
    sys.exit(main())
