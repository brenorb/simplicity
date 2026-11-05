#!/usr/bin/env python3
"""Exact integer interval proof for the native TwoCrypto source projection."""

from dataclasses import dataclass
import json

WAD = 10**18
ANN = 4_000_000
GAMMA = 199 * 10**15
INT256 = 2**255
UINT256 = 2**256


def quot(a, b):
    """Signed Vyper division truncates towards zero."""
    return (-1 if (a < 0) != (b < 0) else 1) * (abs(a) // abs(b))


@dataclass(frozen=True)
class Bounds:
    low: int
    high: int

    def __post_init__(self):
        assert -INT256 <= self.low <= self.high < INT256

    def __add__(self, other):
        return Bounds(self.low + other.low, self.high + other.high)

    def __neg__(self):
        return Bounds(-self.high, -self.low)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        return corners(self, other, lambda a, b: a * b)

    def __floordiv__(self, other):
        assert other.low > 0 or other.high < 0
        return corners(self, other, quot)

    def square(self):
        hi = max(self.low**2, self.high**2)
        lo = min(self.low**2, self.high**2) if self.low * self.high > 0 else 0
        return Bounds(lo, hi)

    def abs_lower(self):
        return min(abs(self.low), abs(self.high)) if self.low * self.high > 0 else 0


def exact(n):
    return Bounds(n, n)


def corners(a, b, f):
    edges = [f(x, y) for x in (a.low, a.high) for y in (b.low, b.high)]
    return Bounds(min(edges), max(edges))


def deltas(a, b, c, d):
    d0 = exact(3) * a * c // b - b
    d1 = exact(3) * d0 + b - ((exact(27) * a.square() // b) * d // b)
    return d0, d1


def prove_fallback():
    # Rational subintervals [i/10000,(i+1)/10000] cover every gated ratio.
    denominator = 10_000
    coefficient, remainder = divmod(ANN * GAMMA**2, 400_000_000)
    assert remainder == 0
    maxima = []
    for i in range(4500, 5500):
        a = exact(10**32)
        b = Bounds(coefficient * denominator // (i + 1),
                   coefficient * denominator // i) - exact(3 * 10**32 + 2 * GAMMA * 10**14)
        c = (exact(3 * 10**32 + 4 * GAMMA * 10**14 + GAMMA**2 // 10**4 - 4 * coefficient)
             + Bounds(4 * coefficient * i // denominator,
                      4 * coefficient * (i + 1) // denominator))
        d = exact(-((WAD + GAMMA)**2 // 10**4))
        d0, d1 = deltas(a, b, c, d)
        # The source threshold is min(abs(d0),abs(d1),a), with strict bounds.
        # Its 10**30 case is selected throughout this interval.
        assert min(d0.abs_lower(), d1.abs_lower(), a.low) > 10**30
        assert a.high == 10**32
        divisor = exact(10**12)
        a, b, c, d = (x // divisor for x in (a, b, c, d))
        d0, d1 = deltas(a, b, c, d)
        discr = d1.square() + (exact(4) * d0.square() // b) * d0
        assert discr.high < 0, (i, discr)
        maxima.append(discr.high)
    assert 8*WAD*ANN*GAMMA**2 < INT256
    return max(maxima)


def prove_spot():
    # The runtime gate bounds floor(K0_36 / WAD) to [0.95,1.02) WAD.
    # Prove the unused spot calculation still has a positive denominator
    # and that every unsigned intermediate fits the source's word size.
    unit = WAD**2
    lowers, uppers = [], []
    for i in range(9500, 10200):
        k = Bounds(i * unit // 10_000, (i + 1) * unit // 10_000)
        gk = ((exact(2) * k.square() // exact(unit)) * k // exact(unit)
              + exact((GAMMA + WAD)**2)
              - ((k.square() // exact(unit)) * exact(2*GAMMA+3*WAD) // exact(WAD)))
        assert gk.low > 0, (i, gk)
        lowers.append(gk.low)
        uppers.append(gk.high)
    largest_reserve = 4 * WAD
    smallest_reserve = 10**17
    smallest_d = 10**17
    n = ANN * GAMMA**2 // 10_000
    largest_k = 102 * unit // 100
    correction_product = n * largest_reserve // smallest_d * largest_k
    denominator = max(uppers) + correction_product // unit
    spot_numerator = largest_reserve * denominator // smallest_reserve * WAD
    assert max(correction_product, largest_reserve * denominator, spot_numerator,
               spot_numerator // min(lowers) * WAD,
               4 * largest_reserve**2 // smallest_d * unit,
               2 * largest_k**2, 2 * largest_k**2 // unit * largest_k,
               largest_k**2 // unit * (2*GAMMA+3*WAD)) < UINT256
    return min(lowers)


def main():
    # These source input guards also follow from the runtime ratio gate.
    limit = 100*WAD * (2*10**16) // GAMMA
    assert 10**36//limit <= 90*WAD//100 <= 110*WAD//100 <= limit
    result = {
        "source_revision": "5cbe558902402e8fcb331463089db65fc56c11f9",
        "ann": ANN,
        "gamma": GAMMA,
        "ratio_gate": "45*D <= 100*x_j <= 55*D",
        "fallback_ratio_cells": 1000,
        "source_discriminant_upper_bound": str(prove_fallback()),
        "source_divider": str(10**12),
        "spot_ratio_cells": 700,
        "source_spot_gk0_lower_bound": str(prove_spot()),
        "no_rebalance": "WAD <= vp <= 2*WAD and profit >= WAD imply (vp-WAD)^2 <= profit*WAD",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
