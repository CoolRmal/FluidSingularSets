module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# The coefficient estimate from Frostman growth

At one spatial generation, Cauchy–Schwarz uses the number of descendant cubes and
their total mass. Summing generations uses the geometric decay of their side lengths.
The coefficient `r * sqrt (r^3 / F) * sqrt mass` is the trace coefficient
`r^(5/2) * sqrt mass / sqrt F`, written to expose its nonnegative factors.
-/

@[expose] public section

open Finset

namespace FluidSingularSets

/-- A finite family of masses satisfies the square-root Cauchy–Schwarz bound. -/
theorem sum_sqrt_mass_le {ι : Type*} (P : Finset ι) (m : ι → ℝ) {M : ℝ}
    (hm : ∀ i ∈ P, 0 ≤ m i) (hsum : ∑ i ∈ P, m i ≤ M) :
    (∑ i ∈ P, Real.sqrt (m i)) ≤ Real.sqrt ((P.card : ℝ) * M) := by
  have hcs := sum_mul_sq_le_sq_mul_sq P (fun i ↦ Real.sqrt (m i)) (fun _ ↦ (1 : ℝ))
  have hsq : (∑ i ∈ P, Real.sqrt (m i)) ^ 2 ≤ (P.card : ℝ) * M := by
    have hsquares : (∑ i ∈ P, Real.sqrt (m i) ^ 2) = ∑ i ∈ P, m i :=
      sum_congr rfl (fun i hi ↦ Real.sq_sqrt (hm i hi))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one, hsquares] at hcs
    nlinarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg P.card : (0 : ℝ) ≤ _)]
  exact Real.le_sqrt_of_sq_le hsq

/-- The trace coefficients at one level are bounded by its side length times a root constant.
The cardinality hypothesis is the three-dimensional count of spatial descendants. -/
theorem level_frostman_coefficient_sum_le {ι : Type*} (P : Finset ι) (m : ι → ℝ)
    {r R F F₀ M : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hF₀ : 0 < F₀) (hF : F₀ ≤ F)
    (hM : 0 ≤ M) (hm : ∀ i ∈ P, 0 ≤ m i) (hsum : ∑ i ∈ P, m i ≤ M)
    (hcard : (P.card : ℝ) * r ^ 3 ≤ R ^ 3) :
    (∑ i ∈ P, r * Real.sqrt (r ^ 3 / F) * Real.sqrt (m i)) ≤
      r * Real.sqrt (R ^ 3 * M / F₀) := by
  have harg : r ^ 3 / F * ((P.card : ℝ) * M) ≤ R ^ 3 * M / F₀ := by
    calc
      _ = ((P.card : ℝ) * r ^ 3) * M / F := by ring
      _ ≤ R ^ 3 * M / F := by
        gcongr
        exact hF₀.le.trans hF
      _ ≤ R ^ 3 * M / F₀ := by gcongr
  calc
    _ = r * (Real.sqrt (r ^ 3 / F) * ∑ i ∈ P, Real.sqrt (m i)) := by
      rw [← mul_sum]; ring
    _ ≤ r * (Real.sqrt (r ^ 3 / F) * Real.sqrt ((P.card : ℝ) * M)) := by
      gcongr
      exact sum_sqrt_mass_le P m hm hsum
    _ = r * Real.sqrt (r ^ 3 / F * ((P.card : ℝ) * M)) := by
      rw [Real.sqrt_mul (div_nonneg (pow_nonneg hr _) (hF₀.le.trans hF))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) hr

/-- Growth of the root mass, monotone scale weights and a geometric side-length sum imply
the spatial Carleson coefficient bound. The result is uniform in the number of generations.
-/
theorem finite_frostman_carleson_bound {ι : Type*} (N : Finset ℕ) (P : ℕ → Finset ι)
    (m : ℕ → ι → ℝ) (r F : ℕ → ℝ) {R F₀ M A : ℝ}
    (hR : 0 ≤ R) (hF₀ : 0 < F₀) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hr : ∀ n ∈ N, 0 ≤ r n) (hF : ∀ n ∈ N, F₀ ≤ F n)
    (hm : ∀ n ∈ N, ∀ i ∈ P n, 0 ≤ m n i)
    (hmass : ∀ n ∈ N, ∑ i ∈ P n, m n i ≤ M)
    (hcard : ∀ n ∈ N, ((P n).card : ℝ) * r n ^ 3 ≤ R ^ 3)
    (hscale : ∑ n ∈ N, r n ≤ 2 * R) (hgrowth : M ≤ A * R * F₀) :
    (∑ n ∈ N, ∑ i ∈ P n,
      r n * Real.sqrt (r n ^ 3 / F n) * Real.sqrt (m n i)) ≤
      2 * Real.sqrt A * R ^ 3 := by
  have harg : R ^ 3 * M / F₀ ≤ A * R ^ 4 := by
    apply (div_le_iff₀ hF₀).2
    calc
      R ^ 3 * M ≤ R ^ 3 * (A * R * F₀) :=
        mul_le_mul_of_nonneg_left hgrowth (pow_nonneg hR _)
      _ = _ := by ring
  have hsqrt : Real.sqrt (R ^ 3 * M / F₀) ≤ Real.sqrt A * R ^ 2 := by
    calc
      _ ≤ Real.sqrt (A * R ^ 4) := Real.sqrt_le_sqrt harg
      _ = Real.sqrt A * R ^ 2 := by
        rw [Real.sqrt_mul hA, show R ^ 4 = (R ^ 2) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg R)]
  calc
    _ ≤ ∑ n ∈ N, r n * Real.sqrt (R ^ 3 * M / F₀) :=
      sum_le_sum (fun n hn ↦ level_frostman_coefficient_sum_le (P n) (m n)
        (hr n hn) hR hF₀ (hF n hn) hM (hm n hn) (hmass n hn) (hcard n hn))
    _ = (∑ n ∈ N, r n) * Real.sqrt (R ^ 3 * M / F₀) := (sum_mul ..).symm
    _ ≤ 2 * R * Real.sqrt (R ^ 3 * M / F₀) := by gcongr
    _ ≤ 2 * R * (Real.sqrt A * R ^ 2) := by gcongr
    _ = _ := by ring

/-- For dyadic side lengths, the geometric scale bound and the three-dimensional descendant
count give the root Carleson estimate without a separate summability assumption. -/
theorem dyadic_frostman_carleson_bound {ι : Type*} (L : ℕ) (P : ℕ → Finset ι)
    (m : ℕ → ι → ℝ) (F : ℕ → ℝ) {R F₀ M A : ℝ}
    (hR : 0 ≤ R) (hF₀ : 0 < F₀) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hF : ∀ n < L, F₀ ≤ F n) (hm : ∀ n < L, ∀ i ∈ P n, 0 ≤ m n i)
    (hmass : ∀ n < L, ∑ i ∈ P n, m n i ≤ M)
    (hcard : ∀ n < L, (P n).card ≤ 8 ^ n) (hgrowth : M ≤ A * R * F₀) :
    (∑ n ∈ range L, ∑ i ∈ P n,
      (R * (1 / 2 : ℝ) ^ n) * Real.sqrt ((R * (1 / 2 : ℝ) ^ n) ^ 3 / F n) *
        Real.sqrt (m n i)) ≤ 2 * Real.sqrt A * R ^ 3 := by
  apply finite_frostman_carleson_bound (range L) P m
    (fun n ↦ R * (1 / 2 : ℝ) ^ n) F hR hF₀ hM hA
  · intro n _
    positivity
  · simpa only [mem_range] using hF
  · simpa only [mem_range] using hm
  · simpa only [mem_range] using hmass
  · intro n hn
    calc
      _ ≤ (8 : ℝ) ^ n * (R * (1 / 2 : ℝ) ^ n) ^ 3 := by
        gcongr
        exact_mod_cast hcard n (mem_range.1 hn)
      _ = R ^ 3 := by
        rw [mul_pow, pow_right_comm]
        calc
          _ = R ^ 3 * ((8 : ℝ) * (1 / 2 : ℝ) ^ 3) ^ n := by rw [mul_pow]; ring
          _ = _ := by norm_num
  · rw [← mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left (sum_geometric_two_le L) hR]
  · exact hgrowth

end FluidSingularSets
