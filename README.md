# Mathlib Contributions

Lean 4 + Mathlib formalizations of classical analysis and number theory theorems,
developed as standalone contributions for [Mathlib4](https://github.com/leanprover-community/mathlib4).

## Modules

### `Contributions.Perron` — Perron's Summation Formula

Formalizes Perron's formula connecting Dirichlet series partial sums to
vertical contour integrals:

```
Σ_{n ≤ x} a(n) = (1/2πi) ∫_{σ-iT}^{σ+iT} F(s) x^s/s ds + O(error)
```

**Status:** Definitions complete, kernel estimates proved, main theorems stated
with documented proof strategies. Requires Mathlib compilation to fill remaining
`sorry`s (API name resolution).

Built on Mathlib's existing infrastructure:
- `Analysis.MellinTransform` / `Analysis.MellinInversion`
- `NumberTheory.LSeries.*`
- `Analysis.Complex.CauchyIntegral`

**Target Mathlib module:** `Mathlib.NumberTheory.LSeries.Perron`

### Planned: Mergelyan's Theorem

Complex polynomial approximation on compact sets with connected complement.
Longer-term project; see `docs/PERRON_SCOPE.md` for the development plan.

**Target Mathlib module:** `Mathlib.Analysis.Complex.PolynomialApproximation.Mergelyan`

## Build

```bash
lake exe cache get
lake build
```

Lean 4.16.0-rc1 | Mathlib v4.16.0-rc1

## Author

J. L. Nielsen, Center for Topological Physics
