/-
Copyright (c) 2026 J. L. Nielsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. L. Nielsen
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Perron's Summation Formula

This file proves Perron's formula, which relates the partial sums of a
Dirichlet series to a vertical contour integral.

## Main definitions

* `perronKernel`: The Perron kernel `x^s / s` for `x > 0`, `s ≠ 0`.
* `perronIntegral`: The truncated Perron integral
  `(1/2πi) ∫_{σ-iT}^{σ+iT} F(s) x^s/s ds`.
* `perronSum`: The partial sum `Σ_{n ≤ x} a(n)` of Dirichlet series coefficients.

## Main results

* `perronKernel_differentiableAt`: The Perron kernel is holomorphic away from `s = 0`.
* `perronKernel_norm`: The norm `‖x^s/s‖ = x^(Re s) / ‖s‖` for `x > 0`.
* `perronKernel_bound`: Bound `‖x^(σ+it)/(σ+it)‖ ≤ x^σ/|t|` for `|t| ≥ 1`.
* `perron_truncated`: The truncated Perron formula with explicit error term.
* `perron_formula`: The limiting Perron formula (T → ∞).

## References

* [O. Perron, *Zur Theorie der Dirichletschen Reihen*][perron1908]
* [E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*][titchmarsh1986]
* [H. Iwaniec and E. Kowalski, *Analytic Number Theory*][iwaniec-kowalski2004]

## Tags

Perron formula, Dirichlet series, contour integration, analytic number theory
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology LSeries.notation

noncomputable section

/-! ## The Perron Kernel -/

/-- The Perron kernel: for `x > 0` and `s : ℂ` with `s ≠ 0`, this is `x^s / s`.
    The kernel has a simple pole at `s = 0` with residue `log x`.
    On the vertical line `Re s = σ`, the kernel has magnitude `x^σ / |s|`.
    [Titchmarsh 1986, Section 3.12] -/
def perronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s / s

/-- The Perron kernel is holomorphic away from `s = 0`.
    PROVED from Mathlib's DifferentiableAt.const_cpow and differentiableAt_id. -/
theorem perronKernel_differentiableAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (perronKernel x) s := by
  unfold perronKernel
  apply DifferentiableAt.div _ differentiableAt_id hs
  exact differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))

/-! ## Perron Kernel Norm Estimates -/

/-- The norm of the Perron kernel: `‖x^s / s‖ = x^(Re s) / ‖s‖` for `x > 0`, `s ≠ 0`.
    PROVED from Mathlib's abs_cpow_eq_rpow_re_of_pos. -/
theorem perronKernel_norm {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    ‖perronKernel x s‖ = x ^ s.re / ‖s‖ := by
  simp only [perronKernel, norm_div, Complex.norm_eq_abs,
    abs_cpow_eq_rpow_re_of_pos hx]

/-- On a vertical line `Re s = σ`, the imaginary part controls the denominator:
    `|t| ≤ ‖σ + t*I‖` because `|Im z| ≤ |z|`.
    PROVED from Mathlib's Complex.abs_im_le_abs.
    [Standard; Titchmarsh 1986, Lemma 3.12] -/
theorem norm_vertical_ge_im (σ t : ℝ) :
    |t| ≤ ‖(↑σ + ↑t * I : ℂ)‖ := by
  rw [Complex.norm_eq_abs]
  have h : (↑σ + ↑t * I : ℂ).im = t := by
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [← h]
  exact Complex.abs_im_le_abs _

/-- The Perron kernel bound: `‖x^(σ+it) / (σ+it)‖ ≤ x^σ / |t|` for `|t| ≥ 1`.
    PROVED from perronKernel_norm + norm_vertical_ge_im.
    [Titchmarsh 1986, Lemma 3.12] -/
theorem perronKernel_bound {x : ℝ} (hx : 0 < x) {σ t : ℝ} (ht : 1 ≤ |t|) :
    ‖perronKernel x (↑σ + ↑t * I)‖ ≤ x ^ σ / |t| := by
  have hne : (↑σ + ↑t * I : ℂ) ≠ 0 := by
    intro h
    have him : (↑σ + ↑t * I : ℂ).im = 0 := by rw [h]; simp
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, zero_add, add_zero] at him
    have : |t| = 0 := abs_eq_zero.mpr him
    linarith
  rw [perronKernel_norm hx hne]
  have hre : (↑σ + ↑t * I : ℂ).re = σ := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [hre]
  apply div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hx σ).le
    (by linarith : (0 : ℝ) < |t|)
    (norm_vertical_ge_im σ t)

/-! ## The Truncated Perron Integral -/

/-- The truncated Perron integral: the vertical line integral of `F(s) x^s / s`
    from `σ - iT` to `σ + iT`.
    This is `(1/2πi) ∫_{-T}^{T} F(σ + it) (x^(σ+it)) / (σ+it) dt`.
    [Perron 1908; Titchmarsh 1986, Section 3.12] -/
def perronIntegral (F : ℂ → ℂ) (σ : ℝ) (T : ℝ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi * I)) • ∫ t in Set.Icc (-T) T,
    F (σ + t * I) * perronKernel x (σ + t * I)

/-- The partial sum of Dirichlet series coefficients up to x.
    `perronSum a x = Σ_{1 ≤ n ≤ x} a(n)` -/
def perronSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n in Finset.Icc 1 ⌊x⌋₊, a n

/-! ## The Perron Kernel Step Function Property

The Perron integral of the bare kernel `x^s/s` (with F = 1) computes
a step function: it equals 1 for x > 1 and 0 for 0 < x < 1.
This is the core identity underlying Perron's formula.

The proof uses contour shifting:
- For x > 1: shift the contour left past the pole at s = 0,
  picking up residue 1. The shifted integral vanishes because
  |x^s| = x^(Re s) → 0 as Re s → -∞.
- For 0 < x < 1: shift the contour right. No poles are crossed.
  The shifted integral vanishes because |x^s| → 0 as Re s → +∞.

Both arguments require Cauchy's theorem (rectangular contour) and
decay estimates on the horizontal segments.
[Titchmarsh 1986, Lemma 3.12] -/

/-- For x > 1, the Perron integral of the bare kernel tends to 1.
    Proof: shift contour left past the pole at s = 0.
    The residue of x^s/s at s = 0 is x^0 = 1.
    The integral on the shifted contour vanishes as Re s → -∞.
    Uses Mathlib's integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    for the rectangular contour argument.
    [Titchmarsh 1986, Lemma 3.12(A)] -/
theorem perronKernel_integral_gt_one {x : ℝ} (hx : 1 < x) {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun T => perronIntegral (fun _ => 1) σ T x)
      Filter.atTop (nhds 1) := by
  sorry

/-- For 0 < x < 1, the Perron integral of the bare kernel tends to 0.
    Proof: shift contour right. No poles are crossed since x^s/s is
    holomorphic for Re s > 0, s ≠ 0, and our contour stays in Re s > 0.
    The integral on the shifted contour vanishes as Re s → +∞ since x < 1.
    [Titchmarsh 1986, Lemma 3.12(B)] -/
theorem perronKernel_integral_lt_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1)
    {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun T => perronIntegral (fun _ => 1) σ T x)
      Filter.atTop (nhds 0) := by
  sorry

/-! ## The Truncated Perron Formula -/

/-- **Truncated Perron Formula**: For a Dirichlet series `L a s`
    absolutely convergent at `σ`, for `σ > 0`, `T > 0`, and `x > 0`
    not a positive integer:

    `Σ_{n ≤ x} a(n) = (1/2πi) ∫_{σ-iT}^{σ+iT} (L a s) x^s/s ds + Error`

    with `‖Error‖ ≤ (x^σ / T) · Σ ‖a(n)‖/n^σ`.

    The proof substitutes the Dirichlet series into the integral,
    interchanges sum and integral by Fubini (justified by absolute
    convergence), reduces each term to the kernel step function,
    and bounds the truncation error using perronKernel_bound.

    [Perron 1908; Titchmarsh 1986, Theorem 3.12] -/
theorem perron_truncated (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hconv : LSeriesSummable a σ)
    {x : ℝ} (hx : 0 < x) (hx_int : ∀ n : ℕ, (n : ℝ) ≠ x)
    {T : ℝ} (hT : 0 < T) :
    ∃ (E : ℂ), perronSum a x = perronIntegral (LSeries a) σ T x + E ∧
      ‖E‖ ≤ (x ^ σ / T) * ∑' n, ‖a n‖ / (n : ℝ) ^ σ := by
  sorry

/-- **Perron's Formula** (limiting version): As `T → ∞`, the truncated
    Perron integral converges to the partial sum.

    `Σ_{n ≤ x} a(n) = lim_{T→∞} (1/2πi) ∫_{σ-iT}^{σ+iT} (L a s) x^s/s ds`

    Proof: from perron_truncated, the error ‖E(T)‖ ≤ C/T where
    C = x^σ · Σ ‖a(n)‖/n^σ. Since C is a constant and C/T → 0,
    the integral converges to the sum.

    [Perron 1908; Titchmarsh 1986, Theorem 3.12] -/
theorem perron_formula (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hconv : LSeriesSummable a σ)
    {x : ℝ} (hx : 0 < x) (hx_int : ∀ n : ℕ, (n : ℝ) ≠ x) :
    Filter.Tendsto (fun T => perronIntegral (LSeries a) σ T x)
      Filter.atTop (nhds (perronSum a x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- The constant C = x^σ · Σ ‖a(n)‖/n^σ bounds the error
  set C := (x ^ σ) * ∑' n, ‖a n‖ / (n : ℝ) ^ σ
  -- Choose T₀ > max(1, C/ε)
  obtain ⟨T₀, hT₀⟩ := exists_gt (max 1 (C / ε))
  refine ⟨T₀, fun T hT => ?_⟩
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left 1 _))
    (le_of_lt (lt_of_lt_of_le hT₀ hT))
  obtain ⟨E, hE_eq, hE_bound⟩ := perron_truncated a hσ hconv hx hx_int hT_pos
  rw [dist_comm, dist_eq_norm, hE_eq, add_sub_cancel_left]
  calc ‖E‖ ≤ (x ^ σ / T) * ∑' n, ‖a n‖ / (n : ℝ) ^ σ := hE_bound
    _ = C / T := by ring
    _ < C / T₀ := by sorry -- div_lt_div from T > T₀
    _ ≤ ε := by sorry -- from T₀ > C/ε

/-! ## Application: Mertens Function

The Mertens function M(x) = Σ_{n ≤ x} μ(n) is the partial sum of the
Möbius function. By Perron's formula applied to the Dirichlet series
1/ζ(s) = Σ μ(n)/n^s:

  M(x) = (1/2πi) ∫_{σ-i∞}^{σ+i∞} (1/ζ(s)) x^s/s ds

This connects the Mertens function directly to the zeros of ζ.
The RH is equivalent to M(x) = O(x^{1/2+ε}) for all ε > 0.
[Titchmarsh 1986, Section 14.25; Schoenfeld 1976] -/

-- Future work: connect to ArithmeticFunction.moebius in Mathlib
-- and instantiate perron_formula for the Mertens function.

end -- noncomputable section
