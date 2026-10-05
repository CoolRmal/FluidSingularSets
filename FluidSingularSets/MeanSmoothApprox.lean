-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MeanMotionBound
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Smooth approximation of actual weighted means

Smooth density in `L^(3/2)` constructs acceleration approximants. A single fixed
cutoff gives common compact support. Integrating the approximants recovers smooth
means and paths; finite-volume Hölder controls their uniform errors.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step4 CKN.Leray
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A fixed time neighborhood used for all acceleration approximants. -/
def meanApproxTimeSet (a b : ℝ) : Set ℝ :=
  Metric.closedBall ((a + b) / 2) (2 * (b - a))

theorem isCompact_meanApproxTimeSet (a b : ℝ) : IsCompact (meanApproxTimeSet a b) :=
  isCompact_closedBall _ _

theorem Icc_subset_meanApproxTimeSet {a b : ℝ} (hab : a < b) :
    Icc a b ⊆ meanApproxTimeSet a b := by
  intro t ht
  rw [meanApproxTimeSet, Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith [ht.1, ht.2]

private def meanApproxCutoff (a b : ℝ) (hab : a < b) :
    ContDiffBump ((a + b) / 2) where
  rIn := b - a
  rOut := 2 * (b - a)
  rIn_pos := sub_pos.mpr hab
  rIn_lt_rOut := by linarith

private theorem meanApproxCutoff_one {a b : ℝ} (hab : a < b) {t : ℝ}
    (ht : t ∈ Icc a b) : meanApproxCutoff a b hab t = 1 := by
  apply (meanApproxCutoff a b hab).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(b - a) ≤ t - (a + b) / 2 ∧ t - (a + b) / 2 ≤ b - a
  constructor <;> linarith [ht.1, ht.2]

/-- Smooth density, localized using one common compact time support. -/
theorem exists_smooth_acceleration_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) {g : ℝ → E}
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (Ioo a b))) :
    ∃ g' : ℝ → E, ContDiff ℝ ∞ g' ∧ HasCompactSupport g' ∧
      tsupport g' ⊆ meanApproxTimeSet a b ∧
      MemLp g' (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      eLpNorm ((Ioo a b).indicator g - g')
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ ENNReal.ofReal ε := by
  let g₀ := (Ioo a b).indicator g
  have hg₀ : MemLp g₀ (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hg
  obtain ⟨v, _hvc, hvs, hv⟩ := hg₀.exist_eLpNorm_sub_le
    ENNReal.ofReal_ne_top (by norm_num) hε
  let ρ := meanApproxCutoff a b hab
  let g' : ℝ → E := fun t ↦ ρ t • v t
  have hgs : ContDiff ℝ ∞ g' := ρ.contDiff.smul hvs
  have hgc : HasCompactSupport g' := ρ.hasCompactSupport.smul_right
  have hsupp : tsupport g' ⊆ meanApproxTimeSet a b := by
    exact (tsupport_smul_subset_left ρ v).trans_eq ρ.tsupport_eq
  have hgp : MemLp g' (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    hgs.continuous.memLp_of_hasCompactSupport hgc
  refine ⟨g', hgs, hgc, hsupp, hgp, ?_⟩
  apply le_trans (eLpNorm_mono (hg₀.sub hgp).aestronglyMeasurable (fun t ↦ ?_)) hv
  have hρ : ρ t • g₀ t = g₀ t := by
    by_cases ht : t ∈ Ioo a b
    · simp only [g₀, indicator_of_mem ht]
      rw [meanApproxCutoff_one hab (Ioo_subset_Icc_self ht), one_smul]
    · simp [g₀, ht]
  calc
    ‖(g₀ - g') t‖ = ‖ρ t • (g₀ t - v t)‖ := by
      congr 1
      simp only [Pi.sub_apply, g', smul_sub, hρ]
    _ = |ρ t| * ‖(g₀ - v) t‖ := by rw [norm_smul, Real.norm_eq_abs]; rfl
    _ ≤ ‖(g₀ - v) t‖ := by
      have hρnorm : |ρ t| ≤ 1 := by
        rw [abs_of_nonneg ρ.nonneg]
        exact ρ.le_one
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hρnorm (norm_nonneg _)

/-- Smooth accelerations have smooth primitives, with the genuine derivative. -/
theorem smooth_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : ContDiff ℝ ∞ g) (t₀ : ℝ) (c : E) :
    ContDiff ℝ ∞ (fun t ↦ c + ∫ τ in t₀..t, g τ) ∧
      ∀ t, HasDerivAt (fun s ↦ c + ∫ τ in t₀..s, g τ) (g t) t := by
  have hd (t : ℝ) : HasDerivAt (fun s ↦ c + ∫ τ in t₀..s, g τ) (g t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuous.continuousAt).const_add c
  refine ⟨contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hd t).differentiableAt, ?_⟩, hd⟩
  convert hg using 1
  funext t
  exact (hd t).deriv

/-- Finite-volume Hölder in the form needed for uniform primitive convergence. -/
theorem integral_norm_le_threeHalves_norm_mul_volume
    {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ} [IsFiniteMeasure μ]
    {g : ℝ → E} (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) μ) :
    (∫ t, ‖g t‖ ∂μ) ≤
      (eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal *
        (μ univ).toReal ^ (1 / 3 : ℝ) := by
  have hh := integral_norm_le_moment_mul_volume
    (show (3 / 2 : ℝ).HolderConjugate 3 by constructor <;> norm_num) hg
  have heq := hg.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofReal_ne_top
  have hpnon : 0 ≤ (∫ t, ‖g t‖ ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
    positivity
  have hreal := congrArg ENNReal.toReal heq
  norm_num only [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal hpnon] at hreal
  norm_num only [one_div_div] at hh
  rwa [hreal]

/-- The fixed finite-volume constant converting acceleration error to mean error. -/
def meanApproxErrorConstant (a b : ℝ) : ℝ :=
  (volume (meanApproxTimeSet a b)).toReal ^ (1 / 3 : ℝ)

/-- An `L^(3/2)` approximation of the genuine acceleration gives smooth means
and smooth paths, with quantitative errors. The mean estimate holds on all time. -/
theorem exists_smooth_mean_and_path_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) {g m : ℝ → E}
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (Ioo a b)))
    (hm : Continuous m)
    (hinc : ∀ s t : ℝ, m t - m s = ∫ τ in s..t, (Ioo a b).indicator g τ) :
    ∃ g' m' X' : ℝ → E,
      ContDiff ℝ ∞ g' ∧ ContDiff ℝ ∞ m' ∧ ContDiff ℝ ∞ X' ∧
      tsupport g' ⊆ meanApproxTimeSet a b ∧
      MemLp g' (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ t, HasDerivAt m' (g' t) t) ∧ (∀ t, HasDerivAt X' (m' t) t) ∧
      eLpNorm ((Ioo a b).indicator g - g')
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ ENNReal.ofReal ε ∧
      (∀ t, ‖m' t - m t‖ ≤ meanApproxErrorConstant a b * ε) ∧
      (∀ t ∈ Icc a b, ‖X' t - ∫ τ in a..t, m τ‖ ≤
        (b - a) * (meanApproxErrorConstant a b * ε)) := by
  obtain ⟨g', hgs, hgc, hgsupp, hgp, hge⟩ :=
    exists_smooth_acceleration_approx hab hε hg
  let g₀ := (Ioo a b).indicator g
  let m' : ℝ → E := fun t ↦ m a + ∫ τ in a..t, g' τ
  let X' : ℝ → E := fun t ↦ ∫ τ in a..t, m' τ
  obtain ⟨hms, hmd⟩ := smooth_primitive hgs a (m a)
  have hms' : ContDiff ℝ ∞ m' := hms
  obtain ⟨hXs, hXd⟩ := smooth_primitive hms' a (0 : E)
  have hg₀ : MemLp g₀ (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hg
  have hgJ : IntegrableOn g (Ioo a b) := hg.integrable (by norm_num)
  have hgint : Integrable g₀ volume := hgJ.integrable_indicator measurableSet_Ioo
  have hg'int : Integrable g' volume := hgs.continuous.integrable_of_hasCompactSupport hgc
  have herrint : Integrable (g₀ - g') volume := hgint.sub hg'int
  let K := meanApproxTimeSet a b
  have hKfin : volume K < (∞ : ℝ≥0∞) := (isCompact_meanApproxTimeSet a b).measure_lt_top
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hKfin.ne
  have herr : MemLp (g₀ - g') (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict K) :=
    (hg₀.sub hgp).mono_measure Measure.restrict_le_self
  have hLp : eLpNorm (g₀ - g') (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict K) ≤ ENNReal.ofReal ε :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hge
  have hrealLp : (eLpNorm (g₀ - g') (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict K)).toReal ≤ ε := by
    simpa only [ENNReal.toReal_ofReal hε.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hLp
  have hzero (t : ℝ) (ht : t ∉ K) : (g₀ - g') t = 0 := by
    have htJ : t ∉ Ioo a b := fun h ↦
      ht (Icc_subset_meanApproxTimeSet hab (Ioo_subset_Icc_self h))
    have htgs : g' t = 0 := by
      by_contra hne
      exact ht (hgsupp (subset_tsupport g' hne))
    simp [g₀, htJ, htgs]
  have hnorm : (∫ t, ‖(g₀ - g') t‖) ≤ meanApproxErrorConstant a b * ε := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht ↦ by rw [hzero t ht, norm_zero])]
    have hh := integral_norm_le_threeHalves_norm_mul_volume herr
    rw [Measure.restrict_apply_univ] at hh
    exact hh.trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hrealLp (by positivity))
  have hmean (t : ℝ) : ‖m' t - m t‖ ≤ meanApproxErrorConstant a b * ε := by
    rw [norm_sub_rev]
    have heq : m t - m' t = ∫ τ in a..t, (g₀ - g') τ := by
      dsimp only [m']
      rw [← sub_sub, hinc a t]
      exact (intervalIntegral.integral_sub
        hgint.intervalIntegrable hg'int.intervalIntegrable).symm
    rw [heq]
    exact (intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun τ ↦ norm_nonneg _) herrint.norm)).trans hnorm
  refine ⟨g', m', X', hgs, hms', ?_, hgsupp, hgp, hmd, ?_, hge, hmean, ?_⟩
  · simpa only [zero_add] using hXs
  · simpa only [zero_add] using hXd
  · intro t ht
    change ‖(∫ τ in a..t, m' τ) - ∫ τ in a..t, m τ‖ ≤ _
    rw [← intervalIntegral.integral_sub
      (hms'.continuous.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := t) (fun s _ ↦ hmean s)
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at hh
    exact hh.trans (by
      calc
        meanApproxErrorConstant a b * ε * (t - a) ≤
            meanApproxErrorConstant a b * ε * (b - a) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
            (mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) hε.le)
        _ = _ := mul_comm _ _)

/-- Genuine convergent smooth approximants for an acceleration and its mean.
The acceleration errors converge strongly in `L^(3/2)` on all time, the means
converge uniformly on all time, and the paths converge uniformly on `[a,b]`. -/
theorem exists_smooth_mean_and_path_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {g m : ℝ → E}
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (Ioo a b)))
    (hm : Continuous m)
    (hinc : ∀ s t : ℝ, m t - m s = ∫ τ in s..t, (Ioo a b).indicator g τ) :
    ∃ g' m' X' : ℕ → ℝ → E,
      (∀ n, ContDiff ℝ ∞ (g' n) ∧ ContDiff ℝ ∞ (m' n) ∧ ContDiff ℝ ∞ (X' n) ∧
        tsupport (g' n) ⊆ meanApproxTimeSet a b ∧
        MemLp (g' n) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        (∀ t, HasDerivAt (m' n) (g' n t) t) ∧
        (∀ t, HasDerivAt (X' n) (m' n t) t)) ∧
      Tendsto (fun n ↦ eLpNorm ((Ioo a b).indicator g - g' n)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) atTop (𝓝 0) ∧
      TendstoUniformly m' m atTop ∧
      TendstoUniformlyOn X' (fun t ↦ ∫ τ in a..t, m τ) atTop (Icc a b) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc a b →
        ‖m' n t‖ ≤ C ∧ ‖X' n t‖ ≤ C := by
  classical
  have hex (n : ℕ) := exists_smooth_mean_and_path_approx hab
    (show 0 < 1 / ((n : ℝ) + 1) by positivity) hg hm hinc
  choose g' m' X' hgs hms hXs hsupp hgp hmd hXd hLp hmean hpath using hex
  have heps : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmeanLim : Tendsto (fun n : ℕ ↦ meanApproxErrorConstant a b *
      (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul heps
  have hpathLim : Tendsto (fun n : ℕ ↦ (b - a) * (meanApproxErrorConstant a b *
      (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hmeanLim
  refine ⟨g', m', X', fun n ↦
    ⟨hgs n, hms n, hXs n, hsupp n, hgp n, hmd n, hXd n⟩, ?_, ?_, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal heps)
      (fun _ ↦ zero_le) hLp
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp hmeanLim).2 ε hε] with n hn t
    rw [dist_eq_norm, norm_sub_rev]
    exact (hmean n t).trans_lt hn
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp hpathLim).2 ε hε] with n hn t ht
    rw [dist_eq_norm, norm_sub_rev]
    exact (hpath n t ht).trans_lt hn
  · obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      hm.continuousOn
    have hXcont : Continuous (fun t ↦ ∫ τ in a..t, m τ) :=
      (intervalIntegral.differentiable_integral_of_continuous hm).continuous
    obtain ⟨P, hP⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      hXcont.continuousOn
    have hC : 0 ≤ meanApproxErrorConstant a b := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hwidthPos : 0 < b - a := sub_pos.mpr hab
    refine ⟨|M| + |P| + meanApproxErrorConstant a b +
      (b - a) * meanApproxErrorConstant a b + 1, by positivity, ?_⟩
    intro n t ht
    have hepsn : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hme : ‖m' n t - m t‖ ≤ meanApproxErrorConstant a b :=
      (hmean n t).trans (by simpa using mul_le_mul_of_nonneg_left hepsn hC)
    have hpe : ‖X' n t - ∫ τ in a..t, m τ‖ ≤
        (b - a) * meanApproxErrorConstant a b := (hpath n t ht).trans (by
      exact mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_left hepsn hC) hwidthPos.le)
    have hmnorm := norm_add_le (m' n t - m t) (m t)
    have hpnorm := norm_add_le (X' n t - ∫ τ in a..t, m τ) (∫ τ in a..t, m τ)
    simp only [sub_add_cancel] at hmnorm hpnorm
    have hmabs := (hM t ht).trans (le_abs_self M)
    have hpabs := (hP t ht).trans (le_abs_self P)
    have hwidth : 0 ≤ (b - a) * meanApproxErrorConstant a b :=
      mul_nonneg (sub_nonneg.mpr hab.le) hC
    constructor <;> linarith [abs_nonneg M, abs_nonneg P]

/-- Uniform approximation preserves a supplied quantitative mean bound up to
an arbitrarily small error, eventually for the entire compact time interval. -/
theorem eventually_mean_bound_of_uniform_approx
    {E : Type*} [NormedAddCommGroup E] {S : Set ℝ}
    {m : ℝ → E} {m' : ℕ → ℝ → E} {M δ : ℝ}
    (hconv : TendstoUniformlyOn m' m atTop S)
    (hbound : ∀ t ∈ S, ‖m t‖ ≤ M) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ t ∈ S, ‖m' n t‖ ≤ M + δ := by
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ] with n hn t ht
  have hdist : ‖m' n t - m t‖ < δ := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact hn t ht
  have htri := norm_add_le (m' n t - m t) (m t)
  simp only [sub_add_cancel] at htri
  linarith [hbound t ht]

/-- The actual vector acceleration of a weighted suitable velocity mean. -/
def weightedMeanAcceleration (B : Set Vec3) (χ : Vec3 → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t : ℝ) : Vec3 :=
  fun i ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, t)

theorem suitable_weightedMeanAcceleration_memLp_threeHalves
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    MemLp (weightedMeanAcceleration B χ u Du p)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J) :=
  MemLp.of_eval fun i ↦
    suitable_weighted_mean_acceleration_memLp_threeHalves hsol hbox hχ hχc i

/-- Actual suitability constructs a continuous vector mean, its genuine
`L^(3/2)` acceleration, and an exact primitive identity through both endpoints. -/
theorem exists_suitable_weighted_vector_mean_primitive
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b)) (hab : a < b)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) :
    ∃ m : ℝ → Vec3, Continuous m ∧
      (∀ i, AbsolutelyContinuousOnInterval (fun t ↦ m t i) a b) ∧
      ((fun t i ↦ weightedVelocityMean B χ u i t) =ᵐ[volume.restrict (Ioo a b)] m) ∧
      MemLp (weightedMeanAcceleration B χ u Du p)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (Ioo a b)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        HasDerivAt m (weightedMeanAcceleration B χ u Du p t) t) ∧
      ∀ s t : ℝ, m t - m s = ∫ τ in s..t,
        (Ioo a b).indicator (weightedMeanAcceleration B χ u Du p) τ := by
  classical
  have hex (i : Fin 3) :=
    exists_suitable_weighted_mean_absolutelyContinuous hsol hbox hab hχ hχc hχs i
  choose m hmcont hmac hmean hder hinc using hex
  let M : ℝ → Vec3 := fun t i ↦ m i t
  have hg := suitable_weightedMeanAcceleration_memLp_threeHalves hsol hbox hχ hχc
  have hgJ : IntegrableOn (weightedMeanAcceleration B χ u Du p) (Ioo a b) :=
    hg.integrable (by norm_num)
  have hg₀ : Integrable ((Ioo a b).indicator (weightedMeanAcceleration B χ u Du p))
      volume := hgJ.integrable_indicator measurableSet_Ioo
  refine ⟨M, continuous_pi hmcont, hmac, ?_, hg, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hmean] with t ht
    exact funext ht
  · filter_upwards [ae_all_iff.mpr hder] with t ht
    exact hasDerivAt_pi.mpr ht
  · intro s t
    funext i
    have hproj := (ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm
      (hg₀.intervalIntegrable : IntervalIntegrable
        ((Ioo a b).indicator (weightedMeanAcceleration B χ u Du p)) volume s t)
    have hfun : (fun τ ↦ (ContinuousLinearMap.proj (R := ℝ) i)
        ((Ioo a b).indicator (weightedMeanAcceleration B χ u Du p) τ)) =
        (Ioo a b).indicator
          (fun τ ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, τ)) := by
      funext τ
      by_cases hτ : τ ∈ Ioo a b <;> simp [hτ, weightedMeanAcceleration]
    rw [hfun] at hproj
    exact (hinc i s t).trans hproj

/-- Any chosen continuous representative of the actual weighted mean admits
smooth frame data. In particular this applies to the representative carrying
the quantitative motion bound; no acceleration or approximation assumption is
added to suitable weak solution hypotheses. -/
theorem exists_suitable_weighted_mean_smooth_sequence
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b)) (hab : a < b)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B)
    {m : ℝ → Vec3} (hm : Continuous m)
    (hmean : (fun t i ↦ weightedVelocityMean B χ u i t)
      =ᵐ[volume.restrict (Ioo a b)] m) :
    ∃ g' m' X' : ℕ → ℝ → Vec3,
      (∀ n, ContDiff ℝ ∞ (g' n) ∧ ContDiff ℝ ∞ (m' n) ∧ ContDiff ℝ ∞ (X' n) ∧
        tsupport (g' n) ⊆ meanApproxTimeSet a b ∧
        MemLp (g' n) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        (∀ t, HasDerivAt (m' n) (g' n t) t) ∧
        (∀ t, HasDerivAt (X' n) (m' n t) t)) ∧
      Tendsto (fun n ↦ eLpNorm
        ((Ioo a b).indicator (weightedMeanAcceleration B χ u Du p) - g' n)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) atTop (𝓝 0) ∧
      TendstoUniformlyOn m' m atTop (Icc a b) ∧
      TendstoUniformlyOn X' (fun t ↦ ∫ τ in a..t, m τ) atTop (Icc a b) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc a b →
        ‖m' n t‖ ≤ C ∧ ‖X' n t‖ ≤ C := by
  obtain ⟨M, hMc, _hMa, hMmean, hg, _hMd, hinc⟩ :=
    exists_suitable_weighted_vector_mean_primitive hsol hbox hab hχ hχc hχs
  have hae : M =ᵐ[volume.restrict (Ioo a b)] m := hMmean.symm.trans hmean
  rw [restrict_Ioo_eq_restrict_Icc] at hae
  have heq : EqOn M m (Icc a b) :=
    Measure.eqOn_Icc_of_ae_eq volume hab.ne hae hMc.continuousOn hm.continuousOn
  obtain ⟨g', m', X', hsmooth, hLp, hmconv, hXconv, hbound⟩ :=
    exists_smooth_mean_and_path_sequence hab hg hMc hinc
  refine ⟨g', m', X', hsmooth, hLp,
    hmconv.tendstoUniformlyOn.congr_right heq, hXconv.congr_right ?_, hbound⟩
  intro t ht
  exact intervalIntegral.integral_congr (heq.mono
    (uIcc_subset_Icc ⟨le_rfl, hab.le⟩ ht))

end FluidSingularSets
