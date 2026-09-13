#!/usr/bin/env python3
"""Endpoint-paired radial capacity: independent reconstruction and fatality probes.

Run::

    .venv/bin/python spikes/002-endpoint-capacity/benchmark_capacity.py \
        --out spikes/002-endpoint-capacity/RESULTS.json

Evidence level.  Everything this file emits is *numerical evidence* or *exact
rational arithmetic on reconstructed data*.  Nothing here is a proof.  The
paper-level statements live in ``THEORY.md``; the counterexample catalogue
lives in ``FATALITY.md``.  Three separate evidence grades are produced and are
tagged in ``RESULTS.json`` under ``evidence``:

``exact``
    exact ``Fraction`` / ``Q(sqrt 2)`` arithmetic, no floating point on the
    reported path (profile coefficients, polynomial antiderivatives).
``enclosure``
    a two-sided bracket that is valid *given* an exactly established
    monotonicity (here: ``R`` is nonincreasing on the fundamental sector, so
    left/right Riemann sums bracket the integral).  The monotonicity itself is
    checked numerically on a grid, so the bracket is evidence, not a theorem.
``numeric``
    plain floating point sampling; biased in a stated direction.

Independence discipline.  This file does **not** import, exec, read or
otherwise consume any production module or cached certificate.  The
rational-seven profile pair is retyped from the manuscript displays
(``eq:aprofile``/``eq:sprofile``) and every downstream object -- envelope
branches, switch points, densities, radial function of the literal finite-cell
union -- is rebuilt from scratch.  Production numbers appear only inside
``COMPARISON_ANCHORS`` and are used solely for a *posterior* agreement report.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from fractions import Fraction as F
from typing import Callable, Dict, List, Sequence, Tuple

# --------------------------------------------------------------------------
# Comparison anchors.  These are literal decimal/rational strings copied from
# the manuscript and the production certificate.  They are compared against,
# never used as inputs to a computation.
# --------------------------------------------------------------------------
COMPARISON_ANCHORS = {
    "upper_continuum_certificate_num": 90477812,
    "upper_continuum_certificate_den": 10**9,
    "upper_continuum_reported_decimal": "0.0904778111246769545",
    "lower_published_num": 131,
    "lower_published_den": 6250,
    "source_upper": "paper/star_shaped_kakeya_bounds.tex eq:contbound (Prop. 'continuum area bound')",
    "source_lower": "paper/star_shaped_kakeya_bounds.tex Theorem A / spikes/001-joint-inner-outer",
}


# ==========================================================================
# S0.  Exact arithmetic in Q(sqrt 2) and polynomials over it.
# ==========================================================================
Q2 = Tuple[F, F]  # (p, q) represents p + q*sqrt(2)

SQRT2 = math.sqrt(2.0)


def q2(p, q=0) -> Q2:
    return (F(p), F(q))


def q2add(x: Q2, y: Q2) -> Q2:
    return (x[0] + y[0], x[1] + y[1])


def q2mul(x: Q2, y: Q2) -> Q2:
    return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def q2float(x: Q2) -> float:
    return float(x[0]) + float(x[1]) * SQRT2


Poly = List[Q2]  # coefficient list, index == degree


def padd(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    out = []
    for i in range(n):
        x = a[i] if i < len(a) else q2(0)
        y = b[i] if i < len(b) else q2(0)
        out.append(q2add(x, y))
    return out


def pmul(a: Poly, b: Poly) -> Poly:
    out = [q2(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == (F(0), F(0)):
            continue
        for j, y in enumerate(b):
            out[i + j] = q2add(out[i + j], q2mul(x, y))
    return out


def pscale(a: Poly, c: Q2) -> Poly:
    return [q2mul(x, c) for x in a]


def pderiv(a: Poly) -> Poly:
    if len(a) <= 1:
        return [q2(0)]
    return [q2mul(a[i], q2(i)) for i in range(1, len(a))]


def pantideriv(a: Poly) -> Poly:
    """Antiderivative with zero constant term."""
    out = [q2(0)]
    for i, c in enumerate(a):
        out.append(q2mul(c, (F(1, i + 1), F(0))))
    return out


def peval_float(a: Poly, t: float) -> float:
    acc = 0.0
    for c in reversed(a):
        acc = acc * t + q2float(c)
    return acc


def pcompose_affine(a: Poly, u: Q2, v: Q2) -> Poly:
    """a(u*t + v)."""
    inner = [v, u]
    out: Poly = [q2(0)]
    for c in reversed(a):
        out = padd(pmul(out, inner), [c])
    return out


def poly_repr(a: Poly) -> List[List[str]]:
    return [[str(c[0]), str(c[1])] for c in a]


# ==========================================================================
# S1.  Independent reconstruction of the production rational-seven profiles.
#      Retyped from the manuscript displays; no production import.
# ==========================================================================
def build_rational_seven() -> Dict[str, Poly]:
    v = [q2(-1), q2(2)]  # v = 2t - 1

    # A(v) = -7/80 v + 1/9 v^3 - 1/160 v^5              (eq:Apoly)
    Av = [q2(0), q2(F(-7, 80)), q2(0), q2(F(1, 9)), q2(0), q2(F(-1, 160))]
    # B(v) = 1/68 - 41/120 v^2 + v^4 - 20/27 v^6        (eq:Bpoly)
    Bv = [q2(F(1, 68)), q2(0), q2(F(-41, 120)), q2(0), q2(1), q2(0), q2(F(-20, 27))]

    A_t = pcompose_affine(Av, v[1], v[0])
    B_t = pcompose_affine(Bv, v[1], v[0])

    tt = [q2(0), q2(1)]                # t
    one_minus_t = [q2(1), q2(-1)]      # 1 - t
    t1mt = pmul(tt, one_minus_t)       # t(1-t)

    # a(t) = (1-2t)/(2 sqrt2) + (1/5) t(1-t) A(2t-1);  1/(2 sqrt2) = sqrt2/4
    lin = [q2(1), q2(-2)]              # 1 - 2t
    a_poly = padd(pscale(lin, (F(0), F(1, 4))),
                  pscale(pmul(t1mt, A_t), q2(F(1, 5))))

    # s(t) = t(1-t)/(4-2 sqrt2) * (1 + B(2t-1)/5);  1/(4-2 sqrt2) = (2+sqrt2)/4
    inner = padd([q2(1)], pscale(B_t, q2(F(1, 5))))
    s_poly = pmul(pscale(t1mt, (F(1, 2), F(1, 4))), inner)

    H_poly = padd([q2(F(1, 2))], a_poly)
    sp = pderiv(s_poly)
    spp = pderiv(sp)
    Hp = pderiv(H_poly)

    # J = H^2 - s' H + s H'
    J_poly = padd(padd(pmul(H_poly, H_poly), pscale(pmul(sp, H_poly), q2(-1))),
                  pmul(s_poly, Hp))
    # densities:  R_sta^2 dy = -s s'' dtau ;  R_end^2 dy = J dzeta
    Ps = pantideriv(pscale(pmul(s_poly, spp), q2(-1)))
    Pe = pantideriv(J_poly)
    return {
        "a": a_poly, "s": s_poly, "H": H_poly, "sp": sp, "spp": spp,
        "Hp": Hp, "J": J_poly, "Ps": Ps, "Pe": Pe,
    }


def check_shape_inequalities(P: Dict[str, Poly], n: int = 20001) -> Dict[str, object]:
    """Numerical check of eq:signs and eq:J on a uniform grid (evidence only)."""
    mins = {"s''": math.inf, "H": math.inf, "-H'": math.inf,
            "H-s'": math.inf, "J": math.inf, "s_interior": math.inf}
    argmins = {}
    for i in range(n + 1):
        t = i / n
        vals = {
            "s''": -peval_float(P["spp"], t),
            "H": peval_float(P["H"], t),
            "-H'": -peval_float(P["Hp"], t),
            "H-s'": peval_float(P["H"], t) - peval_float(P["sp"], t),
            "J": peval_float(P["J"], t),
        }
        for k, val in vals.items():
            if val < mins[k]:
                mins[k] = val
                argmins[k] = t
        if 0 < i < n:
            sv = peval_float(P["s"], t)
            if sv < mins["s_interior"]:
                mins["s_interior"] = sv
                argmins["s_interior"] = t
    return {"minima": mins, "argmin": argmins,
            "all_strictly_positive": all(v > 0 for v in mins.values())}


# ==========================================================================
# S2.  Continuum envelope, rebuilt from the branch equations.
# ==========================================================================
class Envelope:
    """R(y) = max(R_sta(y), R_end(y)) on the fundamental sector y in [0,1]."""

    def __init__(self, P: Dict[str, Poly]):
        self.P = P
        self.s = lambda t: peval_float(P["s"], t)
        self.sp = lambda t: peval_float(P["sp"], t)
        self.spp = lambda t: peval_float(P["spp"], t)
        self.H = lambda t: peval_float(P["H"], t)
        self.J = lambda t: peval_float(P["J"], t)
        self.tau_star = self._solve_tau_star()

    # ---- branch parametrisations -----------------------------------------
    def y_end(self, z: float) -> float:
        return z - self.s(z) / self.H(z)

    def y_sta(self, tau: float) -> float:
        if tau == 0.0:
            return 0.0
        return self.s(tau) / self.sp(tau) - tau

    def _solve_tau_star(self) -> float:
        f = lambda t: self.s(t) - (1.0 + t) * self.sp(t)
        lo, hi = 1e-9, 0.999999
        assert f(lo) < 0 < f(hi) or f(lo) > 0 > f(hi), (f(lo), f(hi))
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if (f(lo) < 0) == (f(mid) < 0):
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)

    # ---- inverses (both maps are increasing bijections) -------------------
    def zeta_of_y(self, y: float) -> float:
        lo, hi = 0.0, 1.0
        for _ in range(120):
            mid = 0.5 * (lo + hi)
            if self.y_end(mid) < y:
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)

    def tau_of_y(self, y: float) -> float:
        lo, hi = 0.0, self.tau_star
        for _ in range(120):
            mid = 0.5 * (lo + hi)
            if self.y_sta(mid) < y:
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)

    def R_end(self, y: float) -> float:
        return self.H(self.zeta_of_y(y))

    def R_sta(self, y: float) -> float:
        return self.sp(self.tau_of_y(y))

    def R(self, y: float) -> float:
        return max(self.R_end(y), self.R_sta(y))

    # ---- rigorous-shape bracket ------------------------------------------
    def monotone_bracket(self, N: int) -> Tuple[float, float, bool]:
        """Left/right Riemann brackets for int_0^1 R^2 dy.

        Valid *because* R is nonincreasing (both branches are decreasing in y);
        monotonicity is re-checked on the same grid and reported.
        """
        vals = [self.R(i / N) for i in range(N + 1)]
        monotone = all(vals[i] >= vals[i + 1] - 1e-12 for i in range(N))
        upper = sum(vals[i] ** 2 for i in range(N)) / N
        lower = sum(vals[i + 1] ** 2 for i in range(N)) / N
        return lower, upper, monotone

    # ---- switch structure and the six-piece identity ----------------------
    def switch_points(self, scan: int = 200000) -> List[Dict[str, float]]:
        d = lambda y: self.R_sta(y) - self.R_end(y)
        roots = []
        prev_y, prev_d = 0.0, d(0.0)
        for i in range(1, scan + 1):
            y = i / scan
            cur = d(y)
            if prev_d == 0.0 or (prev_d < 0) != (cur < 0):
                lo, hi = prev_y, y
                for _ in range(120):
                    mid = 0.5 * (lo + hi)
                    if (d(lo) < 0) == (d(mid) < 0):
                        lo = mid
                    else:
                        hi = mid
                yr = 0.5 * (lo + hi)
                if 1e-12 < yr < 1 - 1e-12:
                    roots.append(yr)
            prev_y, prev_d = y, cur
        out = []
        for yr in roots:
            out.append({"y": yr, "tau": self.tau_of_y(yr), "zeta": self.zeta_of_y(yr),
                        "R": self.R(yr)})
        return out

    def six_piece_area(self, switches: List[Dict[str, float]]) -> Dict[str, object]:
        """int_0^1 R^2 dy via the exact branch densities and the located switches."""
        ys = [0.0] + [s["y"] for s in switches] + [1.0]
        total = 0.0
        pieces = []
        for i in range(len(ys) - 1):
            y0, y1 = ys[i], ys[i + 1]
            ym = 0.5 * (y0 + y1)
            end_active = self.R_end(ym) >= self.R_sta(ym)
            if end_active:
                z0, z1 = self.zeta_of_y(y0), self.zeta_of_y(y1)
                contrib = peval_float(self.P["Pe"], z1) - peval_float(self.P["Pe"], z0)
                pieces.append({"branch": "e", "y0": y0, "y1": y1,
                               "p0": z0, "p1": z1, "contrib": contrib})
            else:
                t0, t1 = self.tau_of_y(y0), self.tau_of_y(y1)
                contrib = peval_float(self.P["Ps"], t1) - peval_float(self.P["Ps"], t0)
                pieces.append({"branch": "s", "y0": y0, "y1": y1,
                               "p0": t0, "p1": t1, "contrib": contrib})
            total += contrib
        return {"pieces": pieces, "total": total,
                "pattern": "".join(p["branch"] for p in pieces)}


# ==========================================================================
# S3.  Literal finite-cell reconstruction of the radial function of E_n.
#      Pure geometry: no branch classification is used anywhere here.
# ==========================================================================
def finite_cell_radial(P: Dict[str, Poly], n: int, M: int = 1200,
                       Nt: int = 6000, r_th: float = 0.05,
                       profile: Callable[[float], Tuple[float, float]] | None = None,
                       mode: str = "full"):
    """Radial function of E_n = union_j union_t conv{0, p_j(t), q_j(t)}.

    Uses only the cyclic symmetry (E_n is invariant under rotation by 2 pi / n,
    n odd) and elementary chord geometry.  Returns rho on one period, sampled
    at M bin centres, plus diagnostics.  Sampling is inward-biased: the value
    returned is a *lower* bound for the true rho at that angle.
    """
    import numpy as np

    G = n * M
    dphi = 2.0 * math.pi / G
    rho = np.zeros(G)

    t = (np.arange(Nt) + 0.5) / Nt
    if profile is None:
        a_t = np.array([peval_float(P["a"], float(x)) for x in t])
        s_t = np.array([peval_float(P["s"], float(x)) for x in t])
    else:
        vals = [profile(float(x)) for x in t]
        a_t = np.array([v[0] for v in vals])
        s_t = np.array([v[1] for v in vals])

    dn = math.pi / n
    ang = dn * t
    ux, uy = np.cos(ang), np.sin(ang)
    nx, ny = np.cos(ang - math.pi / 2), np.sin(ang - math.pi / 2)
    off = math.pi * s_t / n
    cx, cy = a_t * ux + off * nx, a_t * uy + off * ny
    px, py = cx - 0.5 * ux, cy - 0.5 * uy

    tau_min = px * ux + py * uy          # p . e
    tau_max = tau_min + 1.0
    fx, fy = px - tau_min * ux, py - tau_min * uy
    h = np.hypot(fx, fy)                 # distance from O to the chord line
    # sign of the frame orientation: cross(nu_hat, e)
    with np.errstate(invalid="ignore", divide="ignore"):
        nux, nuy = np.where(h > 0, fx / np.where(h > 0, h, 1), 0.0), \
                   np.where(h > 0, fy / np.where(h > 0, h, 1), 0.0)
    srot = np.sign(nux * uy - nuy * ux)
    srot = np.where(srot == 0, 1.0, srot)

    theta = ang  # arg of e(theta)

    # widest angular window we ever need
    hmax = float(h.max())
    om_hi_max = math.asin(min(1.0, hmax / r_th)) if hmax > 0 else 0.0
    W = int(math.ceil(om_hi_max / dphi)) + 3

    m_all = np.minimum(np.abs(tau_min), np.abs(tau_max))
    foot_interior = (tau_min < 0) & (tau_max > 0)
    m_dist = np.where(foot_interior, h, np.sqrt(h ** 2 + m_all ** 2))
    Rmax = np.sqrt(h ** 2 + np.maximum(tau_min ** 2, tau_max ** 2))

    sides = {"full": (+1.0, -1.0), "lead_only": (+1.0,),
             "trail_only": (-1.0,), "endpoints_only": (+1.0, -1.0)}[mode]
    chunk = max(1, 4_000_000 // max(W, 1))
    for start in range(0, Nt, chunk):
        sl = slice(start, min(start + chunk, Nt))
        hs = h[sl]
        for sigma in sides:
            tau_e = tau_max[sl] if sigma > 0 else tau_min[sl]
            live = (sigma * tau_e) > 0
            if not live.any():
                continue
            tau_in = np.where(sigma > 0, np.maximum(tau_min[sl], 0.0),
                              np.minimum(tau_max[sl], 0.0))
            x_hi = np.sqrt(hs ** 2 + tau_e ** 2)
            x_lo = np.maximum(np.sqrt(hs ** 2 + tau_in ** 2), r_th)
            live &= (x_hi > x_lo) & (hs > 0)
            if not live.any():
                continue
            om_lo = np.arcsin(np.clip(hs / np.maximum(x_hi, 1e-300), 0, 1))
            om_hi = np.arcsin(np.clip(hs / np.maximum(x_lo, 1e-300), 0, 1))
            if mode == "endpoints_only":
                om_hi = om_lo                    # keep the endpoint only, drop the chord
            base = np.where(sigma > 0, theta[sl], theta[sl] + math.pi)
            direction = -sigma * srot[sl]          # arg = base + direction*omega
            # endpoint angle corresponds to omega = om_lo
            psi_end = base + direction * om_lo
            i0 = np.round(psi_end / dphi)
            ks = np.arange(W)
            idx = i0[:, None] + direction[:, None] * ks[None, :]
            psi = idx * dphi
            omega = (psi - base[:, None]) * direction[:, None]
            if mode == "endpoints_only":
                ok = live[:, None] & (ks[None, :] == 0)
            else:
                ok = live[:, None] & (omega >= om_lo[:, None]) \
                    & (omega <= om_hi[:, None]) & (omega > 0)
            if mode == "endpoints_only":
                r = np.where(ok, x_hi[:, None] + 0.0 * omega, 0.0)
            else:
                r = np.where(ok, hs[:, None]
                             / np.maximum(np.sin(np.abs(omega)), 1e-300), 0.0)
            flat_idx = np.mod(idx.astype(np.int64), G).ravel()
            np.maximum.at(rho, flat_idx, r.ravel())

    fold = rho.reshape(n, M).max(axis=0)
    norm_area = float((fold ** 2).mean())          # = (1/pi) * (1/2) int rho^2 dphi
    half = M // 2                                   # pi is an odd multiple of pi/n
    pair = fold ** 2 + np.roll(fold, half) ** 2
    return {
        "n": n, "M": M, "Nt": Nt, "r_threshold": r_th, "mode": mode,
        "normalised_area_lower": norm_area,
        "rho_min": float(fold.min()), "rho_max": float(fold.max()),
        "pair_sum_min": float(pair.min()),
        "pair_sum_at_quarter": float(pair[M // 4]),
        "sup_h": float(h.max()),
        "sup_m_dist": float(m_dist.max()),
        "min_Rmax": float(Rmax.min()),
        "sup_delta_defect": float(np.max(
            np.arcsin(np.clip(h / np.maximum(np.sqrt(h ** 2 + tau_min ** 2), 1e-300), 0, 1))
            + np.arcsin(np.clip(h / np.maximum(np.sqrt(h ** 2 + tau_max ** 2), 1e-300), 0, 1)))),
        "fold": fold,
    }


# ==========================================================================
# S4.  Compression spectra (endpoint and interior contact), dyadic.
# ==========================================================================
def compression_spectrum(fmap: Callable[[float], float], levels: Sequence[int]) -> List[Dict]:
    """Dyadic compression ratios |f(I)|/|I| for a monotone f:[0,1]->[0,1]."""
    out = []
    for m in levels:
        N = 2 ** m
        ratios = []
        prev = fmap(0.0)
        for i in range(1, N + 1):
            cur = fmap(i / N)
            ratios.append((cur - prev) * N)
            prev = cur
        ratios.sort()
        out.append({
            "scale_m": m, "n_tiles": N,
            "min": ratios[0], "q05": ratios[max(0, int(0.05 * N) - 1)],
            "median": ratios[N // 2], "max": ratios[-1],
            "mean_ratio_must_be_one": sum(ratios) / N,
            "hall_expansion_lambda_m": ratios[0],
            "packing_mass_of_compressed_tiles": sum(1 for r in ratios if r < 0.5) / N,
            "image_mass_of_compressed_tiles": sum(r for r in ratios if r < 0.5) / N,
        })
    return out


def far_endpoint_overlap(env: Envelope) -> Dict[str, float]:
    """Image measures of the two far-endpoint branches and their overlap.

    The leading endpoint has radius H(zeta); the trailing endpoint has radius
    1 - H (up to O(h^2)).  The *far* endpoint is the leading one exactly where
    H > 1/2.  Both far families are pushed into the same fundamental sector by
    the n-fold symmetry, so their images can overlap; the overlap is exactly
    the mass that a paired-endpoint functional double counts.
    """
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if env.H(mid) > 0.5:
            lo = mid
        else:
            hi = mid
    zc = 0.5 * (lo + hi)
    y_c = env.y_end(zc)
    # leading-far image = [0, y_c]; trailing-far image = reflection of [y_c,1]
    img_lead = y_c
    img_trail = 1.0 - y_c            # reflected copy y -> 1-y of [y_c,1]
    overlap = max(0.0, min(img_lead, img_trail) - 0.0)
    return {"zeta_switch": zc, "y_switch": y_c,
            "leading_far_image": img_lead, "trailing_far_image": img_trail,
            "image_overlap": overlap,
            "union_of_far_images": max(img_lead, img_trail)}


# ==========================================================================
# S5.  The one-dimensional sliver covering constant.
# ==========================================================================
def sliver_covering_probe(mu: float, N: int = 720, trials: int = 40,
                          seed: int = 20260803) -> Dict[str, float]:
    """Adversarial search for a small feasible U on a discretised circle.

    Feasibility (the exact hypothesis of the covering lemma): for every cell
    theta there is a *connected* run W of cells inside U with
    dist(theta, W) <= mu |W|.  Equivalently theta lies in the mu|C|-enlargement
    of some connected component C of U.  The proved bound is |U| >= L/(1+2mu);
    the periodic construction attains it.  This probe searches for anything
    smaller (which would falsify the lemma).
    """
    rng = random.Random(seed)
    cell = 1.0 / N

    def feasible(mask: List[bool]) -> bool:
        # components of U on the circle
        if all(mask):
            return True
        if not any(mask):
            return False
        start = next(i for i in range(N) if not mask[i])
        comps = []  # (start_index, length_in_cells)
        i = 0
        run_start = None
        order = [(start + k) % N for k in range(N)]
        for pos, idx in enumerate(order):
            if mask[idx]:
                if run_start is None:
                    run_start = pos
            else:
                if run_start is not None:
                    comps.append((run_start, pos - run_start))
                    run_start = None
        if run_start is not None:
            comps.append((run_start, N - run_start))
        covered = [False] * N
        for (cs, cl) in comps:
            reach = mu * cl                     # in cells, each side
            lo = cs - reach                     # real interval [cs, cs+cl] enlarged
            hi = cs + cl + reach
            k = int(math.floor(lo - 0.5))
            while k <= int(math.ceil(hi)):
                if lo <= k + 0.5 <= hi:         # cell centre inside the enlargement
                    covered[order[k % N]] = True
                k += 1
        return all(covered)

    def comp_lengths(mask: List[bool]) -> List[int]:
        if all(mask):
            return [N]
        start = next(i for i in range(N) if not mask[i])
        order = [(start + k) % N for k in range(N)]
        out, run = [], 0
        for idx in order:
            if mask[idx]:
                run += 1
            elif run:
                out.append(run)
                run = 0
        if run:
            out.append(run)
        return out

    seeds: List[List[bool]] = [[True] * N]
    period_cells = max(2, int(round(1.0 + 2.0 * mu)))
    for b in (1, 2, 3, 5, 8):
        per = int(round(b * (1.0 + 2.0 * mu)))
        if per < b + 1 or per > N:
            continue
        seeds.append([(i % per) < b for i in range(N)])
    best = 1.0
    best_cont = 1.0
    for trial in range(trials):
        mask = list(seeds[trial % len(seeds)])
        if not feasible(mask):
            mask = [True] * N
        idxs = list(range(N))
        rng.shuffle(idxs)
        for i in idxs:
            if not mask[i]:
                continue
            mask[i] = False
            if not feasible(mask):
                mask[i] = True
        dens = sum(mask) / N
        best = min(best, dens)
        # exact continuum necessary condition:  sum_C |C| (1+2mu) >= L
        cover_budget = sum(cl * (1.0 + 2.0 * mu) for cl in comp_lengths(mask)) / N
        if cover_budget >= 1.0:
            best_cont = min(best_cont, dens)
    proved = 1.0 / (1.0 + 2.0 * mu)
    return {"mu": mu, "N": N, "seeded_periodic_starts": len(seeds),
            "greedy_best_density_grid": best,
            "greedy_best_density_continuum_feasible": best_cont,
            "proved_sharp_density": proved,
            "grid_artifact_gap": proved - best,
            "falsified": best_cont < proved - 2.0 * cell,
            "note": ("grid feasibility over-counts each component by up to one cell; "
                     "only solutions satisfying the exact continuum budget "
                     "sum |C|(1+2mu) >= L can falsify the lemma")}


def theorem_a_geometric_probe(r: float, R: float = 0.5, n_theta: int = 4000,
                             n_h: int = 600) -> Dict[str, float]:
    """Direct falsification attempt on Theorem A's geometry (not on Lemma 7).

    For each direction theta the adversary may pick any height h in [0, r] and
    any side s = +-1; the resulting sliver is the *rigid* interval
    theta - s*[arcsin(h/R), arcsin(h/r)] -- not merely "an interval whose
    distance is at most mu times its length".  We search for the smallest
    periodic U (intervals of length ell, period per) such that every direction
    can be served, and compare with the Theorem-A density (R-r)/(R+r).
    """
    import numpy as np

    hs = np.linspace(0.0, r, n_h)
    d = np.arcsin(np.clip(hs / r, 0, 1))
    dp = np.arcsin(np.clip(hs / R, 0, 1))
    bound = (R - r) / (R + r)

    def served(per: float, ell: float) -> bool:
        # U = union over k of [k*per, k*per + ell]; test theta on a fine grid
        th = np.linspace(0.0, per, n_theta, endpoint=False)
        ok = np.zeros(n_theta, dtype=bool)
        for sgn in (+1.0, -1.0):
            lo = th[:, None] - sgn * d[None, :]
            hi = th[:, None] - sgn * dp[None, :]
            a = np.minimum(lo, hi)
            b = np.maximum(lo, hi)
            # both ends must land in the same copy of [0, ell] modulo per
            ka = np.floor(a / per)
            same = (np.floor(b / per) == ka)
            inside = same & ((a - ka * per) >= 0.0) & ((b - ka * per) <= ell)
            ok |= inside.any(axis=1)
        return bool(ok.all())

    lo_dens, hi_dens = 0.0, 1.0
    per = 1.0
    for _ in range(40):
        mid = 0.5 * (lo_dens + hi_dens)
        if served(per, mid * per):
            hi_dens = mid
        else:
            lo_dens = mid
    return {"r": r, "R": R, "theoremA_density_bound": bound,
            "minimal_feasible_periodic_density": hi_dens,
            "slack": hi_dens - bound,
            "falsified": hi_dens < bound - 1e-3}


def G_kernel(lam: float) -> float:
    """G(lam) = int_lam^1 x (1-x)/(1+x) dx  =  [x - x^2/2 - ln(1+x)] ... exact form."""
    prim = lambda x: -0.5 * x * x + 2.0 * x - 2.0 * math.log(1.0 + x)
    return prim(1.0) - prim(lam)


def radial_window_integral(a: float, b: float, R: float) -> float:
    """Integral_a^b u(R-u)/(R+u) du."""
    def primitive(u: float) -> float:
        return -0.5 * u * u + 2.0 * R * u - 2.0 * R * R * math.log(R + u)
    return primitive(b) - primitive(a)


def seven_hundredths_schedule() -> Dict[str, object]:
    radii = [0.5, 0.5003, 0.5012, 0.5027, 0.5048, 0.5075, 0.5109, 0.5147]
    endpoints = [0.0175, 0.3355, 0.3419, 0.3520, 0.3661,
                 0.3841, 0.4075, 0.4392, 0.5147]
    common = 371.0 / 16650.0
    rows = []
    for j in range(8):
        m_upper = 7.0 * (j + 1) / 400.0
        payment = radial_window_integral(m_upper, endpoints[1], radii[0])
        for k in range(1, j + 1):
            payment += radial_window_integral(endpoints[k], endpoints[k + 1], radii[k])
        rows.append({"j": j, "m_upper": m_upper, "payment": payment,
                     "margin_over_common": payment - common})
    high_lower = (32.0 / 89.0) * (0.369 ** 2) / 2.0
    return {
        "eta": 7.0 / 50.0,
        "area_bound": 7.0 / 100.0,
        "coefficient_over_pi": 7.0 / (100.0 * math.pi),
        "common_rational_coefficient": common,
        "radii": radii,
        "endpoints": endpoints,
        "rows": rows,
        "minimum_low_payment": min(row["payment"] for row in rows),
        "minimum_low_margin_over_common": min(row["margin_over_common"] for row in rows),
        "high_uniform_lower": high_lower,
        "high_margin_over_common": high_lower - common,
    }


def one_forty_one_schedule() -> Dict[str, object]:
    b = [0.027226, 0.038590, 0.047324, 0.054682, 0.061151, 0.066981, 0.072321, 0.077266, 0.081884, 0.086225, 0.090323, 0.094208, 0.097900, 0.101419, 0.104778, 0.107987, 0.111058, 0.113996, 0.116807, 0.119496, 0.122066, 0.124519, 0.126854, 0.129071, 0.131166, 0.133135, 0.134969, 0.136656, 0.138174, 0.139487, 0.140523, 0.141046]
    radii = [0.500000, 0.500740, 0.501486, 0.502234, 0.502981, 0.503725, 0.504466, 0.505203, 0.505934, 0.506660, 0.507380, 0.508092, 0.508797, 0.509494, 0.510182, 0.510860, 0.511528, 0.512185, 0.512830, 0.513462, 0.514081, 0.514684, 0.515271, 0.515841, 0.516390, 0.516918, 0.517421, 0.517896, 0.518338, 0.518740, 0.519092, 0.519371]
    switches = [0.027226, 0.339842, 0.344933, 0.349939, 0.354888, 0.359794, 0.364671, 0.369526, 0.374368, 0.379204, 0.384040, 0.388883, 0.393740, 0.398615, 0.403517, 0.408452, 0.413428, 0.418453, 0.423537, 0.428690, 0.433923, 0.439251, 0.444691, 0.450264, 0.455995, 0.461917, 0.468075, 0.474531, 0.481375, 0.488752, 0.496925, 0.506472, 0.519371]
    common = 22447.0 / 1000000.0
    rows = []
    for j in range(32):
        payment = radial_window_integral(b[j], switches[1], radii[0])
        for k in range(1, j + 1):
            payment += radial_window_integral(switches[k], switches[k + 1], radii[k])
        rows.append({"j": j, "m_upper": b[j], "payment": payment,
                     "margin_over_common": payment - common})
    eta = 141046.0 / 1000000.0
    factor = 320523.0 / 891046.0
    width = 184377.0 / 500000.0
    high_lower = factor * width * width / 2.0
    return {
        "eta": eta,
        "area_bound": 141.0 / 2000.0,
        "coefficient_over_pi": 141.0 / (2000.0 * math.pi),
        "common_rational_coefficient": common,
        "class_upper_endpoints": b,
        "radii": radii,
        "switches": switches,
        "rows": rows,
        "minimum_low_payment": min(row["payment"] for row in rows),
        "minimum_low_margin_over_common": min(row["margin_over_common"] for row in rows),
        "height_margin_over_target": eta / 2.0 - 141.0 / 2000.0,
        "high_uniform_lower": high_lower,
        "high_margin_over_common": high_lower - common,
        "gain_over_7_100": 141.0 / 2000.0 - 7.0 / 100.0,
    }


def sliver_capacity_bound(r0: float) -> float:
    """int_{r0}^{1/2} r (1-2r)/(1+2r) dr, the Theorem-A capacity coefficient."""
    prim = lambda r: r - 0.5 * r * r - 0.5 * math.log(1.0 + 2.0 * r)
    return prim(0.5) - prim(r0)


def sliver_break_even_r0(target: float) -> float:
    lo, hi = 0.0, 0.5
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if sliver_capacity_bound(mid) > target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


# ==========================================================================
# S6.  Adversarial models.
# ==========================================================================
def cs_family_endpoint_energy(kappa: float, gamma: float) -> Dict[str, float]:
    """Cunningham-Schoenberg style one-cell family a = kappa(1-2t)/2, s = gamma t(1-t).

    Exact closed forms:
        int_0^1 J dzeta = 1/4 + kappa^2/12 - gamma*kappa/3       (endpoint branch)
        int R_sta^2 dy  = 2 gamma^2 (tau*^2/2 - tau*^3/3),  tau* = sqrt(2)-1
    The endpoint branch is the *paired endpoint* capacity of the family; the
    stationary branch is the interior-contact capacity.
    """
    endpoint = 0.25 + kappa ** 2 / 12.0 - gamma * kappa / 3.0
    # stationary branch: y = tau^2/(1-2tau) is gamma-independent, tau* = sqrt2 - 1
    ts = math.sqrt(2.0) - 1.0
    stationary = 2.0 * gamma ** 2 * (ts * ts / 2.0 - ts ** 3 / 3.0)
    H0, H1 = 0.5 + kappa / 2.0, 0.5 - kappa / 2.0
    return {"kappa": kappa, "gamma": gamma,
            "endpoint_branch_int_J": endpoint,
            "stationary_branch_int": stationary,
            "H_max": H0, "H_min": H1,
            "shape_feasible_H_minus_sp": 0.5 - abs(kappa / 2.0 - gamma)}


def astroid_radial(nphi: int = 4000, nsig: int = 4000) -> Dict[str, float]:
    """Sliding-ladder (astroid) model: every endpoint sits on a coordinate axis."""
    import numpy as np
    phi = (np.arange(nphi) + 0.5) * (2 * math.pi / nphi)
    sig = (np.arange(1, nsig) / nsig) * (math.pi / 2)
    c, d = np.cos(sig), np.sin(sig)
    # first-quadrant reduction, then reflect
    ph = np.abs(np.mod(phi, math.pi / 2))
    cph, sph = np.cos(ph), np.sin(ph)
    denom = cph[:, None] / c[None, :] + sph[:, None] / d[None, :]
    r = 1.0 / denom
    rho = r.max(axis=1)
    return {"normalised_capacity": float((rho ** 2).mean()),
            "exact_astroid_normalised": 3.0 / 8.0,
            "endpoint_arg_atoms": 4,
            "endpoint_only_capacity": 0.0,
            "rho_min": float(rho.min()), "rho_max": float(rho.max())}


def far_needle_model(T: float, eta: float) -> Dict[str, float]:
    """Needle for direction theta centred at T e(theta) + eta nu(theta)."""
    A = math.hypot(eta, T - 0.5)
    B = math.hypot(eta, T + 0.5)
    m = A if T > 0.5 else eta
    lam = m / B
    return {"T": T, "eta": eta, "A": A, "B": B, "m_dist": m, "M_dist": B,
            "lambda": lam,
            "sliver_payment_over_pi": B * B * G_kernel(lam),
            "triangle_area": eta / 2.0,
            "M2_minus_m2": B * B - m * m}


def far_common_center_model(R: float) -> Dict[str, float]:
    """All unit needles share centre (R,0); their union is B((R,0),1/2)."""
    if R <= 0.5:
        raise ValueError("R must exceed 1/2")
    alpha = math.asin(1.0 / (2.0 * R))
    area = math.pi / 8.0 + alpha / 4.0 + 0.5 * math.sqrt(R * R - 0.25)
    return {
        "R": R,
        "support_half_angle": alpha,
        "projective_pair_nonzero_support_length": 2.0 * alpha,
        "projective_pair_zero_interval_length": math.pi - 2.0 * alpha,
        "pointwise_pair_floor": 0.0,
        "essential_pair_floor": 0.0,
        "star_hull_area": area,
        "full_projective_pair_integral": 2.0 * area,
    }


def zero_height_pair_energy(nsamp: int = 200001) -> Dict[str, float]:
    """h == 0 branch: A + B = 1 exactly, endpoints exactly antipodal."""
    worst = math.inf
    for i in range(nsamp):
        A = i / (nsamp - 1)
        worst = min(worst, A * A + (1 - A) ** 2)
    return {"min_A2_plus_B2": worst, "attained_at_A": 0.5,
            "capacity_lower_over_pi": worst / 4.0 * 1.0,
            "sharp_capacity_over_pi": 0.25}


# ==========================================================================
# S7.  Driver.
# ==========================================================================
def _numpy_version() -> str:
    try:
        import numpy
        return numpy.__version__
    except ImportError:
        return "absent"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--ns", default="51,101,201,401")
    args = ap.parse_args()

    t0 = time.time()
    res: Dict[str, object] = {}
    res["meta"] = {
        "generated_by": "spikes/002-endpoint-capacity/benchmark_capacity.py",
        "python": sys.version.split()[0],
        "quick": bool(args.quick),
        "numpy": _numpy_version(),
        "independence": ("profiles retyped from paper eq:aprofile/eq:sprofile; "
                         "no production module imported; no cached spectrum read"),
    }
    res["comparison_anchors"] = COMPARISON_ANCHORS

    # ---- definitions and normalisations ---------------------------------
    res["definitions"] = {
        "Tp": "projective direction circle R/piZ, total mass pi",
        "chord": "Gamma_theta(u) = p_theta + u e(theta), u in [0,1], the full paired chord",
        "rho": "rho(phi) = sup{|x| : x in union_theta Gamma_theta, arg x = phi}, sup of empty set = 0",
        "Cap2": "Cap2 = (1/2) * upper-Lebesgue-integral over S^1 of rho(phi)^2 dphi",
        "identity": "Cap2 = outer Lebesgue measure of Tri(E) = union_theta conv(0, Gamma_theta)",
        "normalisation": "all capacities are reported divided by pi",
        "h": "h(theta) = dist(O, aff Gamma_theta)",
        "m": "m(theta) = dist(O, Gamma_theta) (segment, not line)",
        "M": "M(theta) = max_u |Gamma_theta(u)| >= 1/2",
        "delta": "angular defect from antipodality; A B sin(delta) = h and A^2+B^2+2AB cos(delta) = 1",
        "lower_published": "131*pi/6250 = 0.020960*pi",
        "upper_certified": "< 90477812e-9 * pi (continuum), the near-extremizer ceiling",
    }

    # ---- S1/S2 ----------------------------------------------------------
    P = build_rational_seven()
    res["profiles"] = {
        "a_coeffs_p_plus_q_sqrt2": poly_repr(P["a"]),
        "s_coeffs_p_plus_q_sqrt2": poly_repr(P["s"]),
        "H_coeffs_p_plus_q_sqrt2": poly_repr(P["H"]),
        "J_coeffs_p_plus_q_sqrt2": poly_repr(P["J"]),
        "evidence": "exact",
    }
    res["shape_inequalities"] = check_shape_inequalities(P, 4001 if args.quick else 20001)
    res["shape_inequalities"]["evidence"] = "numeric"

    env = Envelope(P)
    res["envelope"] = {"tau_star": env.tau_star, "evidence": "numeric"}

    refine = [200, 400, 800, 1600] if args.quick else [200, 800, 3200, 12800, 51200]
    table = []
    for N in refine:
        lo, hi, mono = env.monotone_bracket(N)
        table.append({"N": N, "lower": lo, "upper": hi, "width": hi - lo,
                      "R_monotone_nonincreasing": mono})
    res["continuum_refinement_table"] = {"rows": table, "evidence": "enclosure"}

    sw = env.switch_points(20000 if args.quick else 200000)
    six = env.six_piece_area(sw)
    res["switch_structure"] = {
        "n_switches": len(sw), "switches": sw,
        "active_branch_pattern": six["pattern"],
        "six_piece_total": six["total"],
        "six_piece_pieces": six["pieces"],
        "evidence": "numeric",
    }

    cert = COMPARISON_ANCHORS["upper_continuum_certificate_num"] / \
        COMPARISON_ANCHORS["upper_continuum_certificate_den"]
    res["agreement_with_production_upper"] = {
        "reconstructed_six_piece": six["total"],
        "reconstructed_bracket": [table[-1]["lower"], table[-1]["upper"]],
        "production_certificate_strict_upper": cert,
        "paper_reported_decimal": float(COMPARISON_ANCHORS["upper_continuum_reported_decimal"]),
        "six_piece_minus_reported": six["total"] - float(
            COMPARISON_ANCHORS["upper_continuum_reported_decimal"]),
        "bracket_contains_reported": table[-1]["lower"] <= float(
            COMPARISON_ANCHORS["upper_continuum_reported_decimal"]) <= table[-1]["upper"],
        "reconstruction_below_certificate": six["total"] < cert,
    }

    # radial floor and pair floor of the near-extremizer (R is nonincreasing)
    R1 = env.R(1.0)
    Rhalf = env.R(0.5)
    pair_min = min(env.R(y) ** 2 + env.R(1 - y) ** 2 for y in
                   [i / 2000 for i in range(2001)])
    res["near_extremizer_profile"] = {
        "R_at_0": env.R(0.0), "R_at_half": Rhalf, "R_at_1": R1,
        "radial_floor_min_R": R1,
        "radial_floor_capacity_over_pi": R1 ** 2,
        "antipodal_pair_floor_min": pair_min,
        "antipodal_pair_capacity_over_pi": pair_min / 2.0,
        "H_at_1_exact_baseline": 0.5 - 1.0 / (2 * math.sqrt(2)),
        "evidence": "numeric",
    }

    # ---- level-set margin table vs Theorem A ------------------------------
    lvl = []
    for r in [0.05, 0.1, 0.146, 0.2, 0.25, 0.3, 0.4, 0.45]:
        lo, hi = 0.0, 1.0
        for _ in range(200):                      # R is nonincreasing on [0,1]
            mid = 0.5 * (lo + hi)
            if env.R(mid) >= r:
                lo = mid
            else:
                hi = mid
        actual = lo if env.R(0.0) >= r else 0.0
        bound = (1 - 2 * r) / (1 + 2 * r) if r < 0.5 else 0.0
        lvl.append({"r": r, "theoremA_bound_over_pi": bound,
                    "near_extremizer_actual_over_pi": actual,
                    "slack": actual - bound, "satisfied": actual >= bound - 1e-9})
    res["level_set_margins"] = {
        "rows": lvl,
        "statement": "|{rho > r}| / pi  >=  (1-2r)/(1+2r)  for a selector with m == 0",
        "all_satisfied": all(x["satisfied"] for x in lvl),
        "min_slack": min(x["slack"] for x in lvl),
        "evidence": "numeric",
    }

    # ---- S4 spectra ------------------------------------------------------
    levels = [1, 2, 3, 4, 6, 8] if args.quick else [1, 2, 3, 4, 6, 8, 10, 12]
    res["spectra"] = {
        "endpoint_compression": compression_spectrum(env.y_end, levels),
        "interior_contact_compression": compression_spectrum(
            lambda x: env.y_sta(x * env.tau_star), levels),
        "endpoint_jacobian_min_J_over_H2": min(
            env.J(i / 20000) / env.H(i / 20000) ** 2 for i in range(20001)),
        "far_endpoint_images": far_endpoint_overlap(env),
        "evidence": "numeric",
    }

    # ---- S3 literal finite-cell reconstruction ---------------------------
    finite_rows = []
    try:
        import numpy  # noqa: F401
        ns = [int(x) for x in args.ns.split(",")]
        if args.quick:
            ns = ns[:2]
        for n in ns:
            out = finite_cell_radial(P, n, M=600 if args.quick else 1200,
                                     Nt=3000 if args.quick else 8000)
            out.pop("fold")
            finite_rows.append(out)
        res["finite_cell_reconstruction"] = {
            "rows": finite_rows,
            "note": ("rho is sampled on a finite angular grid, so the reported "
                     "value is a lower bound for the area of the LITERAL finite-cell "
                     "set E_n; E_n itself lies above the n -> infinity continuum "
                     "limit, so the table should decrease toward the continuum "
                     "target from above as n grows"),
            "continuum_target": six["total"],
            "evidence": "numeric",
        }
    except ImportError:
        res["finite_cell_reconstruction"] = {"skipped": "numpy unavailable"}

    # ---- S5 covering constant -------------------------------------------
    probes = []
    for mu in ([0.25, 1.0] if args.quick else [0.1, 0.25, 0.5, 1.0, 2.0]):
        probes.append(sliver_covering_probe(mu, N=240 if args.quick else 600,
                                            trials=6 if args.quick else 24))
    res["sliver_covering_probe"] = {"rows": probes, "evidence": "numeric",
                                    "proved_bound": "|U| >= L/(1+2mu), sharp"}
    try:
        import numpy  # noqa: F401
        res["theorem_a_geometric_probe"] = {
            "rows": [theorem_a_geometric_probe(rr,
                                               n_theta=800 if args.quick else 3000,
                                               n_h=200 if args.quick else 500)
                     for rr in [0.05, 0.1, 0.2, 0.3, 0.4]],
            "note": ("adversary may choose h and the side per direction; the "
                     "sliver shape is the rigid arcsin pair, so the achievable "
                     "density is at least the Theorem-A density"),
            "evidence": "numeric",
        }
    except ImportError:
        res["theorem_a_geometric_probe"] = {"skipped": "numpy unavailable"}

    # ---- ledger ----------------------------------------------------------
    published = COMPARISON_ANCHORS["lower_published_num"] / \
        COMPARISON_ANCHORS["lower_published_den"]
    coeff0 = sliver_capacity_bound(0.0)
    ledger_rows = []
    for r0 in [0.0, 1 / 32, 1 / 16, 1 / 8, 0.1475, 3 / 16, 1 / 4]:
        c = sliver_capacity_bound(r0)
        ledger_rows.append({
            "r0": r0, "capacity_coefficient_over_pi": c,
            "beats_published_131_over_6250": c > published,
            "ratio_to_published": c / published,
            "fraction_of_certified_ceiling": c / cert,
        })
    res["finite_schedule_seven_hundredths"] = seven_hundredths_schedule()
    res["finite_schedule_seven_hundredths"]["evidence"] = "exact-formula numeric mirror; see exact Fraction certificate"
    res["finite_schedule_141_over_2000"] = one_forty_one_schedule()
    res["finite_schedule_141_over_2000"]["evidence"] = "32-segment exact-formula numeric mirror; see exact Fraction certificate"
    res["finite_schedule_variational"] = {
        "exact_constant": "C_FS = sup over all admissible finite schedules",
        "theorem": "L*(E) >= C_FS for every star-shaped Kakeya set",
        "certified_explicit_lower": 141.0 / 2000.0,
        "formal_bvp_numeric_candidate": 0.0705668,
        "candidate_status": "not a validated enclosure or proved approximation of C_FS",
        "evidence": "see FINITE-SCHEDULE-VARIATIONAL.md",
    }
    res["target_ledger"] = {
        "published_lower_over_pi": published,
        "certified_upper_ceiling_over_pi": cert,
        "headroom_ratio_ceiling_over_published": cert / published,
        "theoremA_coefficient_r0_zero": coeff0,
        "theoremA_break_even_r0": sliver_break_even_r0(published),
        "theoremA_scope": "class-scoped: every selected needle has m(theta)<=r0",
        "intermediate_universal_area_bound": 1.0 / 15.0,
        "intermediate_universal_coefficient_over_pi": 1.0 / (15.0 * math.pi),
        "optimized_universal_area_bound": 1717.0 / 25000.0,
        "optimized_universal_coefficient_over_pi": 1717.0 / (25000.0 * math.pi),
        "optimized_relative_gain_over_published":
            (1717.0 / (25000.0 * math.pi)) / published - 1.0,
        "intermediate_seven_hundredths_area_bound": 7.0 / 100.0,
        "exact_variational_headline": "C_FS",
        "certified_explicit_area_lower": 141.0 / 2000.0,
        "certified_explicit_coefficient_over_pi": 141.0 / (2000.0 * math.pi),
        "explicit_gain_over_7_100": 141.0 / 2000.0 - 7.0 / 100.0,
        "rows": ledger_rows,
        "route_ceilings": {
            "uniform_radial_floor_route": R1 ** 2,
            "antipodal_pair_floor_universal": 0.0,
            "antipodal_pair_floor_near_extremizer_diagnostic": pair_min / 2.0,
            "endpoint_only_route": 0.0,
            "explanation": ("near-extremizer values are diagnostics only; explicit "
                            "legal adversaries determine whether a route survives "
                            "universally"),
        },
        "evidence": "numeric",
    }

    # ---- S6 adversarial models and mutations ------------------------------
    cs_rows = []
    for kappa in [0.0, 0.25, 1 / math.sqrt(2), 0.85, 0.95, 0.99, 1.0]:
        gamma = (1.0 + kappa) / 2.0
        cs_rows.append(cs_family_endpoint_energy(kappa, gamma))
    res["adversary_endpoint_collapse"] = {
        "family": "a = kappa(1-2t)/2, s = gamma t(1-t), gamma = (1+kappa)/2",
        "rows": cs_rows,
        "verdict": ("endpoint branch int J -> 0 as kappa -> 1 while the "
                    "interior-contact branch stays bounded below: any "
                    "endpoint-only capacity functional collapses"),
        "cs_baseline_kappa": 1 / math.sqrt(2),
        "cs_baseline_endpoint_value": cs_family_endpoint_energy(
            1 / math.sqrt(2), (1 + 1 / math.sqrt(2)) / 2)["endpoint_branch_int_J"],
        "evidence": "exact-closed-form",
    }

    try:
        res["adversary_astroid"] = astroid_radial(2000 if args.quick else 6000,
                                                  2000 if args.quick else 6000)
        res["adversary_astroid"]["evidence"] = "numeric"
    except ImportError:
        res["adversary_astroid"] = {"skipped": "numpy unavailable"}

    res["adversary_far_needles"] = {
        "rows": [far_needle_model(T, eta) for T, eta in
                 [(1.0, 1e-3), (2.0, 1e-3), (10.0, 1e-3), (100.0, 1e-3),
                  (10.0, 10.0), (100.0, 100.0)]],
        "note": ("m^2 + 1/4 <= M^2 always; the perpendicular far needle has "
                 "h = m so the elementary triangle bound h/2 takes over"),
        "evidence": "exact-closed-form",
    }
    res["adversary_far_common_center"] = {
        "family": "N_theta=(R,0)+[-1/2,1/2]e(theta); E=conv(0,B((R,0),1/2))",
        "rows": [far_common_center_model(R) for R in (0.51, 1.0, 2.0, 10.0, 100.0)],
        "verdict": ("pointwise, a.e., essential-inf, quantile, and fixed local-average "
                    "antipodal floors have best universal constant zero; full-angle "
                    "average is exactly twice radial capacity"),
        "evidence": "exact-closed-form",
    }
    res["adversary_zero_height"] = zero_height_pair_energy(20001 if args.quick else 200001)
    res["adversary_zero_height"]["evidence"] = "numeric"

    # mutations
    mut = {}
    Mmut = 600 if args.quick else 1200
    nmut = 101
    try:
        import numpy  # noqa: F401
        base = finite_cell_radial(P, nmut, M=Mmut, Nt=3000 if args.quick else 8000,
                                  mode="full")
        lead = finite_cell_radial(P, nmut, M=Mmut, Nt=3000 if args.quick else 8000,
                                  mode="lead_only")
        ep_rows = []
        for Mep in ([300, 600] if args.quick else [300, 600, 1200, 2400]):
            e = finite_cell_radial(P, nmut, M=Mep, Nt=3000 if args.quick else 8000,
                                   mode="endpoints_only")
            e.pop("fold")
            ep_rows.append({"M": Mep, "normalised_area_lower": e["normalised_area_lower"],
                            "rho_min": e["rho_min"]})
        for d in (base, lead):
            d.pop("fold")
        mut["MUT-1-remove-pairing"] = {
            "check": ("replace the paired chord constraint A^2 + B^2 >= 1/2 by the "
                      "unpaired endpoint marginal max(A,B) >= 1/2"),
            "zero_height_paired_capacity_over_pi": 0.25,
            "zero_height_unpaired_capacity_over_pi": 0.125,
            "ratio": 0.5,
            "gate": "sharp constant for the h == 0 class",
            "visibly_changed": True,
            "secondary_finite_cell_witness": {
                "note": ("the rational-seven near-extremizer is pairing-symmetric "
                         "(its two far-endpoint images nest), so dropping one "
                         "endpoint family is almost invisible there; the mutation "
                         "is decisive on the h == 0 class and on the astroid"),
                "pair_floor_both_families": base["pair_sum_min"],
                "pair_floor_leading_family_only": lead["pair_sum_min"],
                "area_both": base["normalised_area_lower"],
                "area_leading_only": lead["normalised_area_lower"],
            },
            "astroid_witness": {
                "endpoint_argument_atoms": 4,
                "endpoint_only_capacity_over_pi": 0.0,
                "true_capacity_over_pi": 3.0 / 8.0,
            },
        }
        coll = lambda t: (0.99 * (1.0 - 2.0 * t) / 2.0, ((1.0 + 0.99) / 2.0) * t * (1.0 - t))
        coll_full = finite_cell_radial(P, nmut, M=Mmut,
                                       Nt=3000 if args.quick else 8000,
                                       mode="full", profile=coll)
        coll_ep = finite_cell_radial(P, nmut, M=Mmut,
                                     Nt=3000 if args.quick else 8000,
                                     mode="endpoints_only", profile=coll)
        for d in (coll_full, coll_ep):
            d.pop("fold")
        mut["MUT-2-remove-interior-contacts"] = {
            "check": ("discard every chord interior and keep only the two chord "
                      "endpoints; evaluate on a legal endpoint-collapse family"),
            "collapse_family": "a = 0.99(1-2t)/2, s = 0.995 t(1-t) (legal, compact, admissible)",
            "collapse_full_chord_capacity": coll_full["normalised_area_lower"],
            "collapse_endpoints_only_capacity": coll_ep["normalised_area_lower"],
            "rational_seven_full_chord_capacity": base["normalised_area_lower"],
            "rational_seven_endpoints_only_capacity": ep_rows[-1]["normalised_area_lower"],
            "endpoint_refinement_rows_rational_seven": ep_rows,
            "gate_threshold": published,
            "verdict_full_on_collapse_family": coll_full["normalised_area_lower"] > published,
            "verdict_endpoints_only_on_collapse_family":
                coll_ep["normalised_area_lower"] > published,
            "visibly_rejected": (coll_full["normalised_area_lower"] > published)
                                and not (coll_ep["normalised_area_lower"] > published),
            "closed_form_cross_check": {
                "family": "a = kappa(1-2t)/2, s = gamma t(1-t), gamma=(1+kappa)/2",
                "kappa_sweep_endpoint_branch": [
                    (r["kappa"], r["endpoint_branch_int_J"]) for r in cs_rows],
                "endpoint_capacity_at_kappa_1": cs_family_endpoint_energy(1.0, 1.0)[
                    "endpoint_branch_int_J"],
                "interior_capacity_at_kappa_1": cs_family_endpoint_energy(1.0, 1.0)[
                    "stationary_branch_int"],
            },
        }
    except ImportError:
        mut["MUT-1-remove-pairing"] = {"skipped": "numpy unavailable"}
        mut["MUT-2-remove-interior-contacts"] = {
            "closed_form_only": [(r["kappa"], r["endpoint_branch_int_J"]) for r in cs_rows]}

    # MUT-3: coarsen one dyadic scale
    fine = compression_spectrum(env.y_end, [8 if args.quick else 12])[0]
    coarse = compression_spectrum(env.y_end, [1])[0]
    mut["MUT-3-coarsen-one-scale"] = {
        "check": "Hall expansion constant lambda_m = min dyadic endpoint expansion",
        "fine_scale": fine["scale_m"], "fine_lambda": fine["hall_expansion_lambda_m"],
        "coarse_scale": coarse["scale_m"], "coarse_lambda": coarse["hall_expansion_lambda_m"],
        "ratio_coarse_over_fine": coarse["hall_expansion_lambda_m"]
                                  / max(fine["hall_expansion_lambda_m"], 1e-300),
        "gate_threshold_lambda": 0.1,
        "verdict_fine": fine["hall_expansion_lambda_m"] > 0.1,
        "verdict_coarse": coarse["hall_expansion_lambda_m"] > 0.1,
        "visibly_changed": (fine["hall_expansion_lambda_m"] > 0.1)
                           != (coarse["hall_expansion_lambda_m"] > 0.1),
        "note": ("coarsening reports expansion lambda = %.4f where the fine scale "
                 "sees %.5f; a Hall alternative certified at the coarse scale is "
                 "not valid at the fine scale"
                 % (coarse["hall_expansion_lambda_m"], fine["hall_expansion_lambda_m"])),
    }
    # MUT-4: null-fibre a.e. relaxation
    mut["MUT-4-null-fibre-ae-relaxation"] = {
        "check": ("replace the pointwise fibre constraint rho(arg x) >= |x| by "
                  "an a.e.-in-phi constraint"),
        "exact_value_over_pi": six["total"],
        "true_value_zero_height_over_pi": 0.25,
        "relaxed_LP_value_over_pi": 0.0,
        "reason": ("for h == 0 every chord meets each circle in a two-point set, so "
                   "every fibre {phi : some chord point has argument phi and radius "
                   ">= r} is a countable union of singletons per direction; an "
                   "a.e.-in-phi constraint is satisfied by rho == 0 off a null set "
                   "and the relaxed infimum is 0, while the true value is >= 1/4"),
        "visibly_collapsed": True,
    }
    res["mutations"] = mut

    # ---- candidate inequality margins ------------------------------------
    res["candidate_margins"] = {
        "C1_uniform_radial_floor": {
            "statement": "rho >= c a.e.  =>  Cap2 >= pi c^2",
            "near_extremizer_value_of_c": R1,
            "implied_ceiling_over_pi": R1 ** 2,
            "margin_vs_published": R1 ** 2 - published,
            "status": ("false in general: the origin-crossing radial family "
                       "Gamma_theta=[T e(theta),(T+1)e(theta)] has rho=0 on "
                       "an oriented half-circle"),
        },
        "C2_antipodal_pair_floor": {
            "statement": "rho(phi)^2 + rho(phi+pi)^2 >= c  =>  Cap2 >= pi c/2",
            "near_extremizer_value_of_c": pair_min,
            "implied_ceiling_over_pi": pair_min / 2.0,
            "margin_vs_published": pair_min / 2.0 - published,
            "status": ("REFUTED universally: far common-centre radial hulls have "
                       "rho(phi)=rho(phi+pi)=0 on a positive-measure interval; "
                       "the reported near-extremizer value is diagnostic only"),
        },
        "C3_hall_carleson_endpoint_expansion": {
            "statement": ("either the paired endpoint image expands by lambda "
                          "or a compression payment is collected"),
            "near_extremizer_min_expansion": res["spectra"]["endpoint_jacobian_min_J_over_H2"],
            "collapse_family_min_expansion": 0.0,
            "status": "REFUTED: expansion branch is vacuous on a legal family",
        },
        "C4_radial_sliver_covering": {
            "statement": ("class-scoped: if all needles satisfy m(theta)<=r0, "
                          "then |{rho >= r}| >= pi*(1-2r)/(1+2r) and the "
                          "integrated coefficient is 0.0284264 at r0=0"),
            "scope": "class-scoped; every selected needle meets B(O,r0)",
            "coefficient_r0_zero": coeff0,
            "margin_vs_published": coeff0 - published,
            "fraction_of_ceiling": coeff0 / cert,
            "status": "PROVED (see THEORY.md Theorem A); constant not claimed sharp",
        },
        "C5_universal_radial_ledger": {
            "statement": "L*(E) >= 1/15 for every star-shaped Kakeya set",
            "area_bound": 1.0 / 15.0,
            "coefficient_over_pi": 1.0 / (15.0 * math.pi),
            "margin_vs_published_coefficient": 1.0 / (15.0 * math.pi) - published,
            "status": "PROVED intermediate rational witness",
        },
        "C6_optimized_universal_radial_ledger": {
            "statement": "L*(E) >= 1717/25000 for every star-shaped Kakeya set",
            "area_bound": 1717.0 / 25000.0,
            "coefficient_over_pi": 1717.0 / (25000.0 * math.pi),
            "margin_vs_published_coefficient":
                1717.0 / (25000.0 * math.pi) - published,
            "relative_gain_over_published":
                (1717.0 / (25000.0 * math.pi)) / published - 1.0,
            "mechanism_numeric_ceiling_area": 0.06868430842034249,
            "status": ("PROVED intermediate result; see UNIVERSAL-OPTIMIZED.md "
                       "and exact optimized certificate"),
        },
        "C7_finite_schedule_seven_hundredths": {
            "statement": "L*(E) >= 7/100 for every star-shaped Kakeya set",
            "area_bound": 7.0 / 100.0,
            "coefficient_over_pi": 7.0 / (100.0 * math.pi),
            "gain_over_1717_25000": 7.0 / 100.0 - 1717.0 / 25000.0,
            "minimum_low_payment": res["finite_schedule_seven_hundredths"]["minimum_low_payment"],
            "common_rational_coefficient": 371.0 / 16650.0,
            "status": ("PROVED intermediate result; see "
                       "UNIVERSAL-SEVEN-HUNDREDTHS.md and exact certificate"),
        },
        "C8_finite_schedule_141_over_2000": {
            "statement": "32-segment schedule certifies C_FS >= 141/2000",
            "certified_witness_area": 141.0 / 2000.0,
            "coefficient_over_pi": 141.0 / (2000.0 * math.pi),
            "gain_over_7_100": 141.0 / 2000.0 - 7.0 / 100.0,
            "minimum_low_payment": res["finite_schedule_141_over_2000"]["minimum_low_payment"],
            "common_rational_coefficient": 22447.0 / 1000000.0,
            "status": ("CERTIFIED explicit witness for C_FS; see "
                       "UNIVERSAL-141-OVER-2000.md and exact certificate"),
        },
    }

    res["verdict"] = {
        "go_no_go": ("GO: exact finite-schedule variational bound C_FS, with "
                    "certified witness 141/2000; NO-GO only for the endpoint-only "
                    "Hall-Carleson candidate"),
        "no_go": {
            "target": "paired endpoint image expansion / Hall-Carleson alternative",
            "killer_family": "a = kappa(1-2t)/2, s = (1+kappa)/2 * t(1-t), kappa -> 1",
            "why": ("the endpoint Jacobian J = H^2 - s'H + sH' vanishes identically "
                    "at kappa = 1, so the whole projective direction circle is "
                    "mapped by the leading-endpoint argument map onto a single "
                    "output angle: the expansion branch of any Hall alternative is "
                    "vacuous on a legal family"),
            "near_extremizer_min_expansion":
                res["spectra"]["endpoint_jacobian_min_J_over_H2"],
            "collapse_family_min_expansion": 0.0,
        },
        "go": {
            "statement": ("FINITE-SCHEDULE-VARIATIONAL.md Theorem V plus the "
                          "certified 32-segment witness"),
            "class": "every star-shaped Kakeya set; arbitrary selector",
            "exact_variational_constant": "C_FS",
            "certified_explicit_area_lower": 141.0 / 2000.0,
            "certified_explicit_coefficient_over_pi": 141.0 / (2000.0 * math.pi),
            "intermediate_area_bounds": [1.0 / 15.0, 1717.0 / 25000.0, 7.0 / 100.0],
            "finite_schedule_minimum_low_payment":
                res["finite_schedule_141_over_2000"]["minimum_low_payment"],
            "coefficient_at_r0_zero_for_stronger_scoped_corollary": coeff0,
            "break_even_r0_for_stronger_scoped_corollary":
                res["target_ledger"]["theoremA_break_even_r0"],
            "not_li_confined_escaping": True,
            "handles_near_extremizer":
                (141.0 / (2000.0 * math.pi)) < cert,
        },
    }
    res["meta"]["runtime_seconds"] = time.time() - t0

    txt = json.dumps(res, indent=2, sort_keys=False, default=float)
    if args.out:
        with open(args.out, "w") as fh:
            fh.write(txt + "\n")
        print(f"wrote {args.out} ({len(txt)} bytes) in "
              f"{res['meta']['runtime_seconds']:.1f}s")
    else:
        print(txt)

    # ---- console summary --------------------------------------------------
    print()
    print("== reconstruction ==")
    print(f"  six-piece  int R^2 dy      = {six['total']:.16f}  pattern={six['pattern']}")
    print(f"  bracket                    = [{table[-1]['lower']:.10f}, {table[-1]['upper']:.10f}]")
    print(f"  production strict upper    = {cert:.10f}")
    print(f"  paper reported decimal     = {COMPARISON_ANCHORS['upper_continuum_reported_decimal']}")
    for row in finite_rows:
        print(f"  literal n={row['n']:>5}: normalised area (lower) = "
              f"{row['normalised_area_lower']:.6f}  sup h = {row['sup_h']:.3e}")
    print("== ledger ==")
    print(f"  published lower  = {published:.10f} * pi")
    print(f"  certified ceiling= {cert:.10f} * pi")
    print(f"  Theorem A (r0=0) = {coeff0:.10f} * pi   ratio {coeff0/published:.3f}x")
    print(f"  break-even r0    = {res['target_ledger']['theoremA_break_even_r0']:.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
