"""Bounded exact algebra from angle-addition and integral primitives.

The roof partition, winner order, insertion inequality and physical eligibility
are handwritten premises in THEOREM.md, not machine-proved by this module.
No historical checker, receipt, root atlas or generated table is imported.
"""
import sympy as s

R = s.Rational
TAU = R(1665, 424)
h, q, Q, e, r = s.symbols("h q Q e r", real=True)


class VerificationError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def equal(left, right, message):
    require(s.cancel(left - right) == 0, message)


def direction(half_tangent):
    """Derive cos/sin from (1+i*t)^2/|1+i*t|^2."""
    t = half_tangent
    z = s.expand((1 + s.I*t)**2)
    return s.re(z)/(1+t*t), s.im(z)/(1+t*t)


def rotate(a, b):
    ca, sa = a
    cb, sb = b
    return ca*cb-sa*sb, sa*cb+ca*sb


def cot(v):
    return v[0]/v[1]


def primitives():
    """Cotangent integrals using unnormalised (cos beta,sin beta)=(1,2h)."""
    cG, sG = direction(Q)
    F = 2*h*h*(1/(2*h)-1/Q)
    A = h*h*(cot(rotate((cG, sG), (1, -2*h)))
               - cot(rotate((cG, sG), (1, 2*h))))
    E = h*h*(cot(rotate((cG, sG), (1, 2*h)))
               - cot(rotate(rotate((cG, sG), direction(e)), (1, 2*h))))
    return tuple(s.cancel(v) for v in (F, A, E))


def long_floor(claimed_table=None):
    F, A, _ = primitives()
    L = (TAU-1)*F+TAU*A-h
    Dbar = 1-r*r*(Q*Q-1)**2
    numerator = s.cancel((L/h-R(1, 4)).subs(h, r*Q)*Dbar)
    f = s.Poly(numerator, Q).nth(0)
    expected = (TAU-R(9, 4)-2*(TAU-1)*r+R(9, 4)*r*r+2*(TAU-1)*r**3
                +r*r*(4*TAU-R(9, 2)-4*(TAU-1)*r)*Q*Q
                +r*r*(R(9, 4)+2*(TAU-1)*r)*Q**4)
    equal(numerator, expected, "long-floor clearing from primitive L")
    require(2*TAU-R(5, 2) > 0, "Q-squared coefficient sign")
    # Denominator bounds from h/Q <= 1/2, and h <= 1/5, respectively.
    require(1-R(1, 2)**2 == R(3, 4), "small-Q denominator bound")
    require(1-(R(1, 5)*(R(7, 3)-R(3, 7)))**2 == R(377, 441),
            "large-Q denominator bound")
    intervals = ((0, R(1, 4)), (R(1, 4), R(3, 8)), (R(3, 8), R(1, 2)))
    t = s.Symbol("t")
    derived = []
    for a, b in intervals:
        P = s.Poly(f.subs(r, a+(b-a)*t), t)
        row = tuple(sum(P.nth(j)*s.binomial(k, j)/s.binomial(3, j)
                        for j in range(k+1)) for k in range(4))
        equal(P.as_expr(), sum(row[k]*s.binomial(3, k)*t**k*(1-t)**(3-k)
                              for k in range(4)), "Bernstein basis reconstruction")
        require(all(v > 0 for v in row), "Bernstein positivity")
        derived.append(row)
    if claimed_table is None:
        claimed_table = ((R(711,424),R(3025,2544),R(7613,10176),R(6045,13568)),
                         (R(6045,13568),R(23953,81408),R(28903,162816),R(11595,108544)),
                         (R(11595,108544),R(2941,81408),R(233,20352),R(75,1696)))
    require(len(claimed_table) == 3, "Bernstein interval count")
    for derived_row, claimed_row in zip(derived, claimed_table):
        require(len(claimed_row) == 4, "Bernstein row size")
        for actual, claim in zip(derived_row, claimed_row):
            equal(actual, claim, "Bernstein coefficient differs from defining reserve")
    return tuple(derived)


def separator_algebra():
    height = R(13, 100)
    d = R(3, 7)
    product = s.expand((1+s.I*2*height)**3*(1+s.I*d)**2)
    equal(s.re(product), -R(8363, 3062500), "height product real part")
    equal(s.im(product), R(399871, 306250), "height product imaginary part")
    require(0 < 3*2*height+2*d < 2, "height angle lift bound")
    endpoint = height/d
    g = TAU-2-2*(TAU-1)*r+TAU*(1+d*d)**2*r*r
    F, A, _ = primitives()
    L_over_h = s.cancel(((TAU-1)*F+TAU*A-h)/h).subs(h, r*Q)
    Dbar = 1-r*r*(Q*Q-1)**2
    gap = (Q*Q-d*d)*(2+Q*Q+d*d)
    equal((1+Q*Q)**2-(1+d*d)**2, gap, "separator square difference")
    equal(L_over_h-g, TAU*r*r*(gap+(1+d*d)**2*(1-Dbar))/Dbar,
          "separator minorant derived from primitive reserve")
    derivative = s.diff(g, r).subs(r, endpoint)
    excess = g.subs(r, endpoint)-R(5, 8)
    require(s.diff(g, r, 2) > 0, "separator derivative increases")
    equal(derivative, -R(228688, 90895), "separator derivative")
    require(derivative < 0 and excess > 0, "separator signs")
    equal(excess, R(1012129, 31164000), "separator excess")
    budget = 3*R(1, 4)+2*(R(5, 8)+excess)-2
    equal(budget, R(1012129, 15582000), "assembled linear margin")
    return dict(height_product=str(product), derivative=str(derivative),
                excess=str(excess), margin=budget)


def scalar_conclusion(height, separator_count):
    """Typed scalar budget, NOT a geometric-domain/closure membership checker.

    The caller supplies the actual-gap geometry proved in THEOREM.md.
    This interface deliberately refuses a missing second separator.
    """
    if height == 0:
        # Handwritten premise: finite unions of the degenerate segments are null.
        # This branch uses neither h/Q nor any cotangent expression.
        return dict(S=0, H=0, linear_margin=0, strict=False)
    require(0 < height < R(13, 100), "positive height domain")
    require(type(separator_count) is int and 2 <= separator_count <= 5,
            "two separators required")
    return dict(linear_margin=separator_algebra()["margin"]*height, strict=True)


def recipe_regression(candidate_cos=None):
    c, sn = direction(R(1, 10))
    t = sn/c
    wrong, _ = direction(t)
    if candidate_cos is None:
        candidate_cos = c
    equal(candidate_cos, c, "cosine must use the half-angle tangent")
    require(wrong != c, "old recipe must differ from the literal direction")
    return dict(t=t, correct=c, erroneous=wrong, difference=wrong-c)


def incidence_algebra():
    """Traverse three seven-cycle short-edge patterns; no root/signature atlas.

    The integral inequality for each half-incidence and the target block cap
    remain handwritten geometry. Here only their exact accounting is checked.
    """
    result = {}
    for name, shorts in (("C", (0, 1)), ("D1", (0, 2)), ("D2", (0, 3))):
        longs = [j for j in range(7) if j not in shorts]
        F = {j: s.Symbol(f"F{j}") for j in longs}
        A = {j: s.Symbol(f"A{j}") for j in longs}
        delta = {j: s.Symbol(f"delta{j}") for j in shorts}
        source, target, exposures = sum(F.values()), sum(F.values()), s.Integer(0)
        blocks = []
        for left in longs:
            vertex = (left+1) % 7
            block_shorts = []
            while vertex in shorts:
                block_shorts.append(vertex)
                vertex = (vertex+1) % 7
            right = vertex
            size = len(block_shorts)+1
            blocks.append(size)
            # Singleton h, pair 2h-delta, triple <= 3h-delta1-delta2.
            target += size*h-sum(delta[j] for j in block_shorts)
            for edge in (left, right):
                source += A[edge]/2
                if block_shorts:
                    exposure = s.Symbol(f"E{edge}_block{left}")
                    exposures += exposure
                    source += exposure/2
        weights = [s.expand(source).coeff(A[j]) for j in longs]
        require(weights == [1]*5, "one source bank: duplicate/missing base incidence")
        Phi = sum((TAU-1)*F[j]+TAU*A[j]-h for j in longs)
        Phi += TAU*exposures/2+sum(delta.values())-2*h
        equal(TAU*source-target, Phi, "source/target ledger subtraction")
        require(sum(blocks) == 7 and len(blocks) == 5, "cyclic block partition")
        require(len(exposures.free_symbols) == (2 if name == "C" else 4),
                "exposure incidence count")
        result[name] = dict(block_sizes=sorted(blocks), base_weights=weights,
                            exposure_incidences=len(exposures.free_symbols))
    return result


def verify_all():
    identities = geometry_algebra()
    table = long_floor()
    separator = separator_algebra()
    topologies = incidence_algebra()
    diagnostic = recipe_regression()
    scalar_conclusion(0, 0)
    scalar_conclusion(R(1, 10), 2)
    return dict(status="PASS_EXACT_SEPARATOR_ALGEBRA",
                geometry_formalized=False, identities=sorted(identities),
                bernstein_coefficients=sum(len(row) for row in table),
                incidence_topologies=sorted(topologies),
                height_product=separator["height_product"],
                separator_derivative=separator["derivative"],
                separator_excess=separator["excess"],
                margin=str(separator["margin"]),
                recipe_difference=str(diagnostic["difference"]))


def geometry_algebra():
    F, A, E = primitives()
    equal(F, h-2*h*h/Q, "core integral")
    equal(A, h**3*(1+Q*Q)**2/(Q*Q-h*h*(Q*Q-1)**2), "collar integral")
    cg, sg = direction(q)
    X = (sg-2*h)/cg  # tan x_*; cos g is positive on the short domain.
    cot_g_minus_x = (cg+sg*X)/(sg-cg*X)
    B = s.cancel(2*((X+2*h)/4 + h*h*(1/(2*h)-cot_g_minus_x)
                    +(2*h-q)/4))
    displayed_B = h + q*(1+q*q+8*h*h-8*h*q)/(2*(1-q*q))
    equal(B, displayed_B, "two-center three-piece integral")
    delta = s.factor(2*h-B)
    equal(delta, (2*h-q)*(1+q*q-4*h*q)/(2*(1-q*q)), "short deficit")
    equal(1+q*q-4*h*q, (q-2*h)**2+1-4*h*h, "deficit sign factor")
    zd, zn = 1-e*e-4*h*e, 2*h*(1-e*e)+2*e
    displayed_E = h*h*(1+Q*Q)**2*(zn-2*h*zd)/(
        (2*Q+2*h*(1-Q*Q))*(2*Q*zd+(1-Q*Q)*zn))
    equal(E, displayed_E, "exposure sine/cotangent identity")
    equal(zn-2*h*zd, 2*e*(1+4*h*h), "exposure sign numerator")
    # Expand the outsider identity in the independent sin(v),cos(v) coefficients.
    # With t=tan(beta), multiply the identity by sqrt(1+t^2).
    t, cv, sv = s.symbols("t cv sv", real=True)
    sin2b, cos2b = 2*t/(1+t*t), (1-t*t)/(1+t*t)
    equal((sin2b*cv-cos2b*sv)-t*cv, cos2b*(t*cv-sv),
          "outsider domination trigonometric identity")
    return dict(F=str(F), A=str(A), B=str(B), delta=str(delta), E=str(E),
                outsider="exact identity; geometric signs proved in THEOREM.md")
