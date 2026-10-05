module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic

/-!
# The mass-ratio layer-cake estimate

The finite layer-cake argument below converts a bound on the total coefficient mass above
each ratio threshold into a bound on its square-root moment.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- A finite nonnegative moment is the integral of its weighted superlevel sums. -/
theorem finite_weighted_layercake {ι : Type*} (P : Finset ι) (β r : ι → ℝ)
    (hβ : ∀ i ∈ P, 0 ≤ β i) (hr : ∀ i ∈ P, 0 ≤ r i) :
    ENNReal.ofReal (∑ i ∈ P, β i * r i) =
      ∫⁻ t in Ioi (0 : ℝ),
        ∑ i ∈ P, (Iio (r i)).indicator (fun _ ↦ ENNReal.ofReal (β i)) t := by
  classical
  rw [lintegral_finsetSum P (fun i _ ↦ measurable_const.indicator measurableSet_Iio)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ mul_nonneg (hβ i hi) (hr i hi))]
  apply sum_congr rfl
  intro i hi
  rw [setLIntegral_indicator measurableSet_Iio]
  have hset : Iio (r i) ∩ Ioi (0 : ℝ) = Ioo 0 (r i) := by ext t; simp; tauto
  rw [hset, setLIntegral_const, Real.volume_Ioo, sub_zero]
  exact ENNReal.ofReal_mul (hβ i hi)

/-- The inverse-square tail kernel has integral `1/a` above a positive cutoff. -/
theorem lintegral_inverse_square_Ioi {a : ℝ} (ha : 0 < a) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-2 : ℝ))) = ENNReal.ofReal (1 / a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
    norm_num
    simp [Real.rpow_neg_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (ha.trans ht).le _

/-- A positive cutoff splits a bounded tail into a constant part and an inverse-square part. -/
theorem lintegral_tail_le {T : ℝ → ℝ≥0∞} {a A B : ℝ}
    (ha : 0 < a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlow : ∀ t > 0, T t ≤ ENNReal.ofReal A)
    (hhigh : ∀ t > 0, T t ≤ ENNReal.ofReal B * ENNReal.ofReal (t ^ (-2 : ℝ))) :
    (∫⁻ t in Ioi (0 : ℝ), T t) ≤ ENNReal.ofReal (A * a + B / a) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  rw [hsplit]
  apply le_trans (lintegral_union_le T (Ioc 0 a) (Ioi a))
  have hlo : (∫⁻ t in Ioc 0 a, T t) ≤ ENNReal.ofReal (A * a) := by
    calc
      _ ≤ ∫⁻ _t in Ioc (0 : ℝ) a, ENNReal.ofReal A := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t ht
        exact hlow t ht.1
      _ = _ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
        exact (ENNReal.ofReal_mul hA).symm
  have hhi : (∫⁻ t in Ioi a, T t) ≤ ENNReal.ofReal (B / a) := by
    calc
      _ ≤ ∫⁻ t in Ioi a, ENNReal.ofReal B * ENNReal.ofReal (t ^ (-2 : ℝ)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        exact hhigh t (ha.trans ht)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_inverse_square_Ioi ha]
        rw [← ENNReal.ofReal_mul hB]
        congr 1
        ring
  calc
    _ ≤ ENNReal.ofReal (A * a) + ENNReal.ofReal (B / a) := add_le_add hlo hhi
    _ = _ := (ENNReal.ofReal_add (mul_nonneg hA ha.le) (div_nonneg hB ha.le)).symm

/-- A weighted finite moment is bounded using its inverse-square superlevel estimate and any
positive splitting threshold. -/
theorem finite_moment_le_of_tail {ι : Type*} (P : Finset ι) (β r : ι → ℝ)
    {C M V a : ℝ} (hβ : ∀ i ∈ P, 0 ≤ β i) (hr : ∀ i ∈ P, 0 ≤ r i)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hV : 0 ≤ V) (ha : 0 < a)
    (htail : ∀ t > 0, (∑ i ∈ P.filter (fun i ↦ t < r i), β i) ≤
      C * min V (M / t ^ 2)) :
    (∑ i ∈ P, β i * r i) ≤ C * (V * a + M / a) := by
  classical
  let T : ℝ → ℝ≥0∞ := fun t ↦
    ∑ i ∈ P, (Iio (r i)).indicator (fun _ ↦ ENNReal.ofReal (β i)) t
  have hrepr (t : ℝ) : T t = ENNReal.ofReal
      (∑ i ∈ P.filter (fun i ↦ t < r i), β i) := by
    dsimp [T]
    rw [sum_filter]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ by split <;> simp_all)]
    apply sum_congr rfl
    intro i _
    by_cases hi : t < r i <;> simp [hi]
  have hlo : ∀ t > 0, T t ≤ ENNReal.ofReal (C * V) := by
    intro t ht
    rw [hrepr]
    exact ENNReal.ofReal_le_ofReal ((htail t ht).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hC))
  have hhi : ∀ t > 0,
      T t ≤ ENNReal.ofReal (C * M) * ENNReal.ofReal (t ^ (-2 : ℝ)) := by
    intro t ht
    rw [hrepr, ← ENNReal.ofReal_mul (mul_nonneg hC hM)]
    apply ENNReal.ofReal_le_ofReal
    have hpower : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by norm_num
    rw [hpower]
    have hbound := (htail t ht).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
    simpa [div_eq_mul_inv, mul_assoc] using hbound
  have hlin := lintegral_tail_le ha (mul_nonneg hC hV) (mul_nonneg hC hM) hlo hhi
  rw [← finite_weighted_layercake P β r hβ hr] at hlin
  have hright : C * V * a + C * M / a = C * (V * a + M / a) := by ring
  rw [hright] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC
    (add_nonneg (mul_nonneg hV ha.le) (div_nonneg hM ha.le)))).1 hlin

/-- Optimizing the layer-cake threshold gives the square-root mass bound with constant two. -/
theorem finite_moment_le_sqrt_of_tail {ι : Type*} (P : Finset ι) (β r : ι → ℝ)
    {C M V : ℝ} (hβ : ∀ i ∈ P, 0 ≤ β i) (hr : ∀ i ∈ P, 0 ≤ r i)
    (hC : 0 ≤ C) (hM : 0 < M) (hV : 0 < V)
    (htail : ∀ t > 0, (∑ i ∈ P.filter (fun i ↦ t < r i), β i) ≤
      C * min V (M / t ^ 2)) :
    (∑ i ∈ P, β i * r i) ≤ 2 * C * Real.sqrt (M * V) := by
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hbound := finite_moment_le_of_tail P β r hβ hr hC hM.le hV.le
    (div_pos hsM hsV) htail
  have heq : C * (V * (Real.sqrt M / Real.sqrt V) +
      M / (Real.sqrt M / Real.sqrt V)) = 2 * C * Real.sqrt (M * V) := by
    rw [Real.sqrt_mul hM.le V]
    field_simp
    rw [Real.sq_sqrt hM.le, Real.sq_sqrt hV.le]
    ring
  exact hbound.trans_eq heq

/-- The finite mass-ratio layer-cake step used in the dissipation trace argument. -/
theorem finite_mass_ratio_trace {ι : Type*} (P : Finset ι) (β μ ν : ι → ℝ)
    {C M V : ℝ} (hβ : ∀ i ∈ P, 0 ≤ β i) (hν : ∀ i ∈ P, 0 < ν i)
    (hC : 0 ≤ C) (hM : 0 < M) (hV : 0 < V)
    (htail : ∀ s > 0, (∑ i ∈ P.filter (fun i ↦ s * ν i < μ i), β i) ≤
      C * min V (M / s)) :
    (∑ i ∈ P, β i * Real.sqrt (μ i / ν i)) ≤ 2 * C * Real.sqrt (M * V) := by
  classical
  apply finite_moment_le_sqrt_of_tail P β (fun i ↦ Real.sqrt (μ i / ν i))
    hβ (fun i _ ↦ Real.sqrt_nonneg _) hC hM hV
  intro t ht
  have hfilters : P.filter (fun i ↦ t < Real.sqrt (μ i / ν i)) =
      P.filter (fun i ↦ t ^ 2 * ν i < μ i) := by
    ext i
    simp only [mem_filter]
    by_cases hi : i ∈ P
    · simp only [hi, true_and, Real.lt_sqrt ht.le, lt_div_iff₀ (hν i hi)]
    · simp [hi]
  rw [hfilters]
  exact htail (t ^ 2) (sq_pos_of_pos ht)

/-- Uniform mass-ratio tail bounds on finite subfamilies control the full trace series. -/
theorem mass_ratio_trace_summable {ι : Type*} (β μ ν : ι → ℝ) {C M V : ℝ}
    (hβ : ∀ i, 0 ≤ β i) (hν : ∀ i, 0 < ν i)
    (hC : 0 ≤ C) (hM : 0 < M) (hV : 0 < V)
    (htail : ∀ (P : Finset ι) (s : ℝ), 0 < s →
      (∑ i ∈ P.filter (fun i ↦ s * ν i < μ i), β i) ≤ C * min V (M / s)) :
    Summable (fun i ↦ β i * Real.sqrt (μ i / ν i)) ∧
      (∑' i, β i * Real.sqrt (μ i / ν i)) ≤ 2 * C * Real.sqrt (M * V) := by
  have hnonneg : ∀ i, 0 ≤ β i * Real.sqrt (μ i / ν i) :=
    fun i ↦ mul_nonneg (hβ i) (Real.sqrt_nonneg _)
  have hbound (P : Finset ι) :
      (∑ i ∈ P, β i * Real.sqrt (μ i / ν i)) ≤ 2 * C * Real.sqrt (M * V) :=
    finite_mass_ratio_trace P β μ ν (fun i _ ↦ hβ i) (fun i _ ↦ hν i)
      hC hM hV (htail P)
  have hsum := summable_of_sum_le hnonneg hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end FluidSingularSets
