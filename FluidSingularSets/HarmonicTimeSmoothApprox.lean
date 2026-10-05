-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MeanSmoothApprox
public import FluidSingularSets.WeakContinuousTimePrimitive
public import FluidSingularSets.SuitableHarmonicGradientTime
public import FluidSingularSets.StrongLpProducts

/-!
# Smooth time approximation inside the harmonic-gradient operator image

Smooth density is applied to the actual Banach-valued derivative before applying
an operator. Integrating these derivatives gives smooth time curves with a common
compact derivative support and genuine uniform convergence of their primitives.
Applying the harmonic-gradient operator preserves its spatial structure exactly.
-/

@[expose] public section

open MeasureTheory Set Filter CKN TopologicalSpace
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

private def harmonicTimeCutoff (a b : ℝ) (hab : a < b) :
    ContDiffBump ((a + b) / 2) where
  rIn := b - a
  rOut := 2 * (b - a)
  rIn_pos := sub_pos.mpr hab
  rIn_lt_rOut := by linarith

private theorem harmonicTimeCutoff_one {a b : ℝ} (hab : a < b) {t : ℝ}
    (ht : t ∈ Icc a b) : harmonicTimeCutoff a b hab t = 1 := by
  apply (harmonicTimeCutoff a b hab).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(b - a) ≤ t - (a + b) / 2 ∧ t - (a + b) / 2 ≤ b - a
  constructor <;> linarith [ht.1, ht.2]

/-- The actual derivative admits smooth approximants at every finite exponent
at least one, with one fixed compact time support. -/
theorem exists_smooth_time_derivative_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpfin : p ≠ ⊤) {g : ℝ → E}
    (hg : MemLp g p (volume.restrict (Ioo a b))) :
    ∃ g' : ℝ → E, ContDiff ℝ ∞ g' ∧ HasCompactSupport g' ∧
      tsupport g' ⊆ meanApproxTimeSet a b ∧ MemLp g' p volume ∧
      eLpNorm ((Ioo a b).indicator g - g') p volume ≤ ENNReal.ofReal ε := by
  let g₀ := (Ioo a b).indicator g
  have hg₀ : MemLp g₀ p volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hg
  obtain ⟨v, _hvc, hvs, hv⟩ := hg₀.exist_eLpNorm_sub_le hpfin hp hε
  let ρ := harmonicTimeCutoff a b hab
  let g' : ℝ → E := fun t ↦ ρ t • v t
  have hgs : ContDiff ℝ ∞ g' := ρ.contDiff.smul hvs
  have hgc : HasCompactSupport g' := ρ.hasCompactSupport.smul_right
  have hsupp : tsupport g' ⊆ meanApproxTimeSet a b :=
    (tsupport_smul_subset_left ρ v).trans_eq ρ.tsupport_eq
  have hgp : MemLp g' p volume := hgs.continuous.memLp_of_hasCompactSupport hgc
  refine ⟨g', hgs, hgc, hsupp, hgp, ?_⟩
  apply le_trans (eLpNorm_mono (hg₀.sub hgp).aestronglyMeasurable (fun t ↦ ?_)) hv
  have hρ : ρ t • g₀ t = g₀ t := by
    by_cases ht : t ∈ Ioo a b
    · simp only [g₀, indicator_of_mem ht]
      rw [harmonicTimeCutoff_one hab (Ioo_subset_Icc_self ht), one_smul]
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

/-- Finite-volume Hölder controls the true norm integral at a general exponent. -/
theorem integral_norm_le_eLpNorm_finite_volume
    {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {g : ℝ → E} (hg : MemLp g p μ) :
    (∫ t, ‖g t‖ ∂μ) ≤ (eLpNorm g p μ).toReal *
      (μ univ ^ (1 - p.toReal⁻¹)).toReal := by
  have hpReal : 1 ≤ p.toReal := by
    simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpfin).2 hp
  have hpow : 0 ≤ 1 - p.toReal⁻¹ := by
    have hinv : p.toReal⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hpReal
    linarith
  have hfactor : μ univ ^ (1 - p.toReal⁻¹) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hpow (measure_ne_top μ univ)).ne
  have hh : eLpNorm g 1 μ ≤ eLpNorm g p μ * μ univ ^ (1 - p.toReal⁻¹) := by
    simpa only [ENNReal.toReal_one, one_div, inv_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg.aestronglyMeasurable
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hg.eLpNorm_ne_top hfactor) hh
  rw [ENNReal.toReal_mul, eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable] at hreal
  exact hreal

/-- The finite factor converting a derivative error into a uniform primitive error. -/
def harmonicTimeApproxErrorConstant (a b : ℝ) (p : ℝ≥0∞) : ℝ :=
  (volume (meanApproxTimeSet a b) ^ (1 - p.toReal⁻¹)).toReal

/-- Smooth true primitives of the approximated derivative, with a quantitative
uniform error on all time. The primitive constant is kept exactly. -/
theorem exists_smooth_time_primitive_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpfin : p ≠ ⊤) {g : ℝ → E}
    (hg : MemLp g p (volume.restrict (Ioo a b))) (c : E) (t₀ : ℝ) :
    ∃ g' h' : ℝ → E,
      ContDiff ℝ ∞ g' ∧ ContDiff ℝ ∞ h' ∧ HasCompactSupport g' ∧
      tsupport g' ⊆ meanApproxTimeSet a b ∧ MemLp g' p volume ∧
      (∀ t, HasDerivAt h' (g' t) t) ∧
      eLpNorm ((Ioo a b).indicator g - g') p volume ≤ ENNReal.ofReal ε ∧
      ∀ t, ‖h' t - (c + ∫ s in t₀..t, (Ioo a b).indicator g s)‖ ≤
        harmonicTimeApproxErrorConstant a b p * ε := by
  obtain ⟨g', hgs, hgc, hsupp, hgp, hLp⟩ :=
    exists_smooth_time_derivative_approx hab hε hp hpfin hg
  let g₀ := (Ioo a b).indicator g
  let h' : ℝ → E := fun t ↦ c + ∫ s in t₀..t, g' s
  obtain ⟨hhs, hhd⟩ := smooth_primitive hgs t₀ c
  have hg₀ : MemLp g₀ p volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hg
  have hgJ : IntegrableOn g (Ioo a b) volume := hg.integrable hp
  have hgint : Integrable g₀ volume := hgJ.integrable_indicator measurableSet_Ioo
  have hg'int : Integrable g' volume := hgs.continuous.integrable_of_hasCompactSupport hgc
  have herrint : Integrable (g₀ - g') volume := hgint.sub hg'int
  let K := meanApproxTimeSet a b
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr
    (isCompact_meanApproxTimeSet a b).measure_lt_top.ne
  have herr : MemLp (g₀ - g') p (volume.restrict K) :=
    (hg₀.sub hgp).mono_measure Measure.restrict_le_self
  have hLpK : eLpNorm (g₀ - g') p (volume.restrict K) ≤ ENNReal.ofReal ε :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hLp
  have hrealLp : (eLpNorm (g₀ - g') p (volume.restrict K)).toReal ≤ ε := by
    simpa only [ENNReal.toReal_ofReal hε.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hLpK
  have hzero (t : ℝ) (ht : t ∉ K) : (g₀ - g') t = 0 := by
    have htJ : t ∉ Ioo a b := fun h ↦
      ht (Icc_subset_meanApproxTimeSet hab (Ioo_subset_Icc_self h))
    have htgs : g' t = 0 := by
      by_contra hne
      exact ht (hsupp (subset_tsupport g' hne))
    simp [g₀, htJ, htgs]
  have hnorm : (∫ t, ‖(g₀ - g') t‖) ≤ harmonicTimeApproxErrorConstant a b p * ε := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht ↦ by rw [hzero t ht, norm_zero])]
    have hh := integral_norm_le_eLpNorm_finite_volume hp hpfin herr
    rw [Measure.restrict_apply_univ] at hh
    exact hh.trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hrealLp ENNReal.toReal_nonneg)
  refine ⟨g', h', hgs, hhs, hgc, hsupp, hgp, hhd, hLp, ?_⟩
  intro t
  rw [norm_sub_rev]
  have heq : (c + ∫ s in t₀..t, g₀ s) - h' t = ∫ s in t₀..t, (g₀ - g') s := by
    dsimp only [h']
    rw [add_sub_add_left_eq_sub]
    exact (intervalIntegral.integral_sub
      hgint.intervalIntegrable hg'int.intervalIntegrable).symm
  rw [heq]
  exact (intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun s ↦ norm_nonneg _) herrint.norm)).trans hnorm

/-- A genuine convergent sequence of smooth primitives at every finite exponent
at least one. The derivative also converges strongly in `L¹` on all time. -/
theorem exists_smooth_time_primitive_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {g : ℝ → E} (hg : MemLp g p (volume.restrict (Ioo a b))) (c : E) (t₀ : ℝ) :
    ∃ g' h' : ℕ → ℝ → E,
      (∀ n, ContDiff ℝ ∞ (g' n) ∧ ContDiff ℝ ∞ (h' n) ∧
        HasCompactSupport (g' n) ∧ tsupport (g' n) ⊆ meanApproxTimeSet a b ∧
        MemLp (g' n) p volume ∧ (∀ t, HasDerivAt (h' n) (g' n t) t)) ∧
      Tendsto (fun n ↦ eLpNorm ((Ioo a b).indicator g - g' n) p volume) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm ((Ioo a b).indicator g - g' n) 1 volume) atTop (𝓝 0) ∧
      TendstoUniformly h' (fun t ↦ c + ∫ s in t₀..t, (Ioo a b).indicator g s) atTop ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc a b → ‖h' n t‖ ≤ C := by
  classical
  have hex (n : ℕ) := exists_smooth_time_primitive_approx hab
    (show 0 < 1 / ((n : ℝ) + 1) by positivity) hp hpfin hg c t₀
  choose g' h' hgs hhs hgc hsupp hgp hhd hLp herr using hex
  let g₀ := (Ioo a b).indicator g
  have hg₀ : MemLp g₀ p volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hg
  have heps : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hLpLim : Tendsto (fun n ↦ eLpNorm (g₀ - g' n) p volume) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal heps)
      (fun _ ↦ zero_le) hLp
  have herrLim : Tendsto (fun n : ℕ ↦ harmonicTimeApproxErrorConstant a b p *
      (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul heps
  refine ⟨g', h', fun n ↦ ⟨hgs n, hhs n, hgc n, hsupp n, hgp n, hhd n⟩,
    hLpLim, ?_, ?_, ?_⟩
  · let K := meanApproxTimeSet a b
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr
      (isCompact_meanApproxTimeSet a b).measure_lt_top.ne
    have hconvK : Tendsto (fun n ↦ eLpNorm (g' n - g₀) p (volume.restrict K))
        atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLpLim
        (fun _ ↦ zero_le)
      intro n
      change eLpNorm (g' n - g₀) p (volume.restrict K) ≤ eLpNorm (g₀ - g' n) p volume
      rw [eLpNorm_sub_comm (f := g' n) (g := g₀) (μ := volume.restrict K)]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    have hL1K := tendsto_eLpNorm_one_of_sub hp hpfin
      (hg₀.mono_measure Measure.restrict_le_self)
      (fun n ↦ (hgp n).mono_measure Measure.restrict_le_self) hconvK
    convert hL1K using 1
    funext n
    change eLpNorm (g₀ - g' n) 1 volume = eLpNorm (g' n - g₀) 1 (volume.restrict K)
    rw [eLpNorm_sub_comm (f := g' n) (g := g₀) (μ := volume.restrict K)]
    apply (eLpNorm_restrict_eq_of_support_subset
      (hg₀.sub (hgp n)).aestronglyMeasurable ?_).symm
    intro t ht
    by_contra hnot
    have htJ : t ∉ Ioo a b := fun h ↦
      hnot (Icc_subset_meanApproxTimeSet hab (Ioo_subset_Icc_self h))
    have htgs : g' n t = 0 := by
      by_contra hne
      exact hnot (hsupp n (subset_tsupport (g' n) hne))
    simp [Function.mem_support, g₀, htJ, htgs] at ht
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp herrLim).2 ε hε] with n hn t
    rw [dist_eq_norm, norm_sub_rev]
    exact (herr n t).trans_lt hn
  · have hgJ : IntegrableOn g (Ioo a b) volume := hg.integrable hp
    have hgint : Integrable g₀ volume := hgJ.integrable_indicator measurableSet_Ioo
    have hcont : Continuous (fun t ↦ c + ∫ s in t₀..t, g₀ s) :=
      continuous_const.add (hgint.continuous_primitive t₀)
    obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      hcont.continuousOn
    have hC : 0 ≤ harmonicTimeApproxErrorConstant a b p := ENNReal.toReal_nonneg
    refine ⟨|M| + harmonicTimeApproxErrorConstant a b p + 1, by positivity, ?_⟩
    intro n t ht
    have hepsn : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have herror : ‖h' n t - (c + ∫ s in t₀..t, g₀ s)‖ ≤
        harmonicTimeApproxErrorConstant a b p :=
      (herr n t).trans (by simpa using mul_le_mul_of_nonneg_left hepsn hC)
    have htri := norm_add_le (h' n t - (c + ∫ s in t₀..t, g₀ s))
      (c + ∫ s in t₀..t, g₀ s)
    simp only [sub_add_cancel] at htri
    have habs := (hM t ht).trans (le_abs_self M)
    linarith

/-- The actual field primitive remains in the exact operator image. Its force
constant is the Bochner average of the actual force minus its primitive. -/
theorem operator_image_ae_time_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeparableSpace K]
    (L : E →L[ℝ] C(K, Vec3)) {a b c : ℝ} (hab : a < b) (hc : c ∈ Ioo a b)
    {f g : ℝ → E} (hf : IntegrableOn f (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) :
    (fun t ↦ L (f t)) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ L (average (volume.restrict (Ioo a b))
        (fun s ↦ f s - ∫ v in c..s, (Ioo a b).indicator g v) +
          ∫ s in c..t, (Ioo a b).indicator g s) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  let : Countable D := hDc.to_subtype
  let A : (D × Fin 3) → C(K, Vec3) →L[ℝ] ℝ :=
    fun α ↦ (ContinuousLinearMap.proj α.2 : Vec3 →L[ℝ] ℝ).comp
      (ContinuousMap.evalCLM ℝ (α.1 : K))
  have hcoord (α : D × Fin 3) := weakTimeDerivative_scalar_ae_primitive
    hab hc hf hg hw ((A α).comp L)
  filter_upwards [ae_all_iff.mpr hcoord] with t ht
  apply ContinuousMap.coe_injective
  apply hDd.denseRange_val.equalizer (L (f t)).continuous
    (L (average (volume.restrict (Ioo a b))
      (fun s ↦ f s - ∫ v in c..s, (Ioo a b).indicator g v) +
        ∫ s in c..t, (Ioo a b).indicator g s)).continuous
  funext x
  apply funext
  intro i
  change (A (x, i)) (L (f t)) = (A (x, i)) (L
    (average (volume.restrict (Ioo a b))
      (fun s ↦ f s - ∫ v in c..s, (Ioo a b).indicator g v) +
        ∫ s in c..t, (Ioo a b).indicator g s))
  rw [map_add, map_add]
  exact ht (x, i)

/-- The exact Banach-valued constant fixed by the original field and derivative. -/
def averagedTimePrimitiveConstant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (a b c : ℝ) : E :=
  average (volume.restrict (Ioo a b))
    (fun s ↦ f s - ∫ v in c..s, (Ioo a b).indicator g v)

/-- The actual primitive fixed by the averaged original field. -/
def averagedTimePrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (a b c t : ℝ) : E :=
  averagedTimePrimitiveConstant f g a b c + ∫ s in c..t, (Ioo a b).indicator g s

/-- The operator image of the actual averaged primitive has genuine continuous,
AC, AE-field, and AE-derivative data, all derived from the original weak evolution. -/
theorem operator_averagedTimePrimitive_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeparableSpace K]
    (L : E →L[ℝ] C(K, Vec3)) {a b c : ℝ} (hab : a < b) (hc : c ∈ Ioo a b)
    {f g : ℝ → E} (hf : IntegrableOn f (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) :
    Continuous (fun t ↦ L (averagedTimePrimitive f g a b c t)) ∧
      AbsolutelyContinuousOnInterval (fun t ↦ L (averagedTimePrimitive f g a b c t)) a b ∧
      (fun t ↦ L (f t)) =ᵐ[volume.restrict (Ioo a b)]
        (fun t ↦ L (averagedTimePrimitive f g a b c t)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt
        (fun t ↦ L (averagedTimePrimitive f g a b c t)) (L (g t)) t) ∧
      ∀ s t : ℝ, L (averagedTimePrimitive f g a b c t) -
        L (averagedTimePrimitive f g a b c s) =
          ∫ v in s..t, (Ioo a b).indicator (fun t ↦ L (g t)) v := by
  let g₀ := (Ioo a b).indicator g
  let C := averagedTimePrimitiveConstant f g a b c
  have hg₀ : Integrable g₀ volume := hg.integrable_indicator measurableSet_Ioo
  have hPcont : Continuous (averagedTimePrimitive f g a b c) :=
    continuous_const.add (hg₀.continuous_primitive c)
  have hPAC : AbsolutelyContinuousOnInterval (averagedTimePrimitive f g a b c) a b := by
    have hp := banach_intervalIntegral_absolutelyContinuous (a := a) (b := b) (c := c)
      hg₀.intervalIntegrable (by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hc)
    have htrans : Isometry (fun x : E ↦ C + x) :=
      Isometry.of_dist_eq fun x y ↦ by simp only [dist_eq_norm, add_sub_add_left_eq_sub]
    exact htrans.lipschitzWith.comp_absolutelyContinuousOnInterval hp
  refine ⟨L.continuous.comp hPcont, L.lipschitzWith.comp_absolutelyContinuousOnInterval hPAC,
    operator_image_ae_time_primitive L hab hc hf hg hw, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae
      (LocallyIntegrable.ae_hasDerivAt_integral hg₀.locallyIntegrable),
      ae_restrict_mem measurableSet_Ioo] with t ht htJ
    have hd := L.hasFDerivAt.comp_hasDerivAt t ((ht c).const_add C)
    simpa only [Function.comp_def, averagedTimePrimitive, C, g₀, indicator_of_mem htJ] using hd
  · intro s t
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hg₀.intervalIntegrable : IntervalIntegrable g₀ volume c s)
      (hg₀.intervalIntegrable : IntervalIntegrable g₀ volume s t)
    have hdiff : averagedTimePrimitive f g a b c t -
        averagedTimePrimitive f g a b c s = ∫ v in s..t, g₀ v := by
      dsimp only [averagedTimePrimitive]
      rw [← hi]
      abel
    rw [← map_sub, hdiff, ← L.intervalIntegral_comp_comm hg₀.intervalIntegrable]
    congr 1
    funext v
    by_cases hv : v ∈ Ioo a b <;> simp [g₀, hv]

/-- Strong convergence of actual Banach fields is preserved by a genuine
bounded linear operator, with no convergence premise for its images. -/
theorem tendsto_eLpNorm_operator_sub
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {μ : Measure α} {p : ℝ≥0∞}
    {f : α → E} {fs : ℕ → α → E} (hf : MemLp f p μ)
    (hfs : ∀ n, MemLp (fs n) p μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (f - fs n) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ L (f x) - L (fs n x)) p μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : eLpNorm (fun x ↦ L (f x) - L (fs n x)) p μ ≤
      ENNReal.ofReal ‖L‖ * eLpNorm (f - fs n) p μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (L.continuous.comp_aestronglyMeasurable (hf.sub (hfs n)).aestronglyMeasurable
        |>.congr (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply, map_sub]))
    exact Eventually.of_forall fun x ↦ by
      rw [← map_sub]
      exact L.le_opNorm (f x - fs n x)
  have hzero := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖L‖) hconv
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hzero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ ↦ zero_le) hbound

/-- Actual smooth time curves inside a prescribed operator image. The force
constant is fixed by the actual weak field, and every image derivative is exact.
Strong derivative convergence is proved at both the original exponent and `L¹`. -/
theorem exists_operator_image_smooth_time_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeparableSpace K]
    (L : E →L[ℝ] C(K, Vec3)) {a b c : ℝ} (hab : a < b) (hc : c ∈ Ioo a b)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) {f g : ℝ → E}
    (hf : IntegrableOn f (Ioo a b) volume) (hg : MemLp g p (volume.restrict (Ioo a b)))
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) :
    ∃ g' h' : ℕ → ℝ → E,
      (∀ n, ContDiff ℝ ∞ (g' n) ∧ ContDiff ℝ ∞ (h' n) ∧
        HasCompactSupport (g' n) ∧ tsupport (g' n) ⊆ meanApproxTimeSet a b ∧
        MemLp (g' n) p volume ∧ (∀ t, HasDerivAt (h' n) (g' n t) t) ∧
        ContDiff ℝ ∞ (fun t ↦ L (h' n t)) ∧
        (∀ t, HasDerivAt (fun s ↦ L (h' n s)) (L (g' n t)) t)) ∧
      (fun t ↦ L (f t)) =ᵐ[volume.restrict (Ioo a b)]
        (fun t ↦ L (averagedTimePrimitive f g a b c t)) ∧
      Tendsto (fun n ↦ eLpNorm ((Ioo a b).indicator g - g' n) p volume) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm ((Ioo a b).indicator g - g' n) 1 volume) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦
        L ((Ioo a b).indicator g t) - L (g' n t)) p volume) atTop (𝓝 0) ∧
      TendstoUniformly (fun n t ↦ L (h' n t))
        (fun t ↦ L (averagedTimePrimitive f g a b c t)) atTop ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc a b → ‖L (h' n t)‖ ≤ C := by
  have hgJ : IntegrableOn g (Ioo a b) volume := hg.integrable hp
  obtain ⟨g', h', hsm, hconv, hconv1, hunif, C, hC, hbound⟩ :=
    exists_smooth_time_primitive_sequence hab hp hpfin hg
      (averagedTimePrimitiveConstant f g a b c) c
  have hg₀ : MemLp ((Ioo a b).indicator g) p volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hg
  refine ⟨g', h', ?_, operator_image_ae_time_primitive L hab hc hf hgJ hw,
    hconv, hconv1, tendsto_eLpNorm_operator_sub L hg₀ (fun n ↦ (hsm n).2.2.2.2.1) hconv,
    L.uniformContinuous.comp_tendstoUniformly hunif, ?_⟩
  · intro n
    obtain ⟨hgs, hhs, hgc, hsupp, hgp, hhd⟩ := hsm n
    exact ⟨hgs, hhs, hgc, hsupp, hgp, hhd, L.contDiff.comp hhs,
      fun t ↦ L.hasFDerivAt.comp_hasDerivAt t (hhd t)⟩
  · refine ⟨‖L‖ * C + 1, by positivity, ?_⟩
    intro n t ht
    exact (L.le_opNorm _).trans (by
      have hh := mul_le_mul_of_nonneg_left (hbound n t ht) (norm_nonneg L)
      linarith)

local instance harmonicTimeApproxForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicTimeApproxForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual continuous harmonic correction, fixed inside the exact force
operator image by the original suitable velocity and momentum force. -/
def unitBallHarmonicTimePrimitive
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ t : ℝ) : C(unitBallPressureCompactInterior, Vec3) :=
  -unitBallHarmonicForceGradientExtended
    (averagedTimePrimitive (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u D p) (t₀ - 4) (t₀ + 4) t₀ t)

/-- All actual time-regularity and representation data for the suitable harmonic
correction. No primitive, convergence, or evolution conclusion is assumed. -/
theorem suitable_unitBall_harmonicTimePrimitive_data
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    Continuous (unitBallHarmonicTimePrimitive u Du p t₀) ∧
      AbsolutelyContinuousOnInterval (unitBallHarmonicTimePrimitive u Du p t₀)
        (t₀ - 4) (t₀ + 4) ∧
      unitBallHarmonicGradientTimeCurve u =ᵐ[volume.restrict (Ioo (t₀ - 4) (t₀ + 4))]
        unitBallHarmonicTimePrimitive u Du p t₀ ∧
      (∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
        HasDerivAt (unitBallHarmonicTimePrimitive u Du p t₀)
          (unitBallHarmonicGradientTimeDerivative u Du p t) t) ∧
      ∀ s t : ℝ, unitBallHarmonicTimePrimitive u Du p t₀ t -
        unitBallHarmonicTimePrimitive u Du p t₀ s = ∫ v in s..t,
          (Ioo (t₀ - 4) (t₀ + 4)).indicator
            (unitBallHarmonicGradientTimeDerivative u Du p) v := by
  obtain ⟨hf, hg⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  exact operator_averagedTimePrimitive_data (-unitBallHarmonicForceGradientExtended)
    (by linarith) ⟨by linarith, by linarith⟩ hf hg
    (suitable_unitBall_momentum_hasWeakTimeDerivativeOn hsol hdom)

/-- Genuine suitable data produces time-smooth force primitives and their exact
harmonic-gradient images. The actual derivative converges strongly in `L¹`, and
the harmonic correction converges uniformly, including both time endpoints. -/
theorem exists_suitable_unitBall_harmonicTime_smooth_sequence
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∃ g' h' : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1),
      (∀ n, ContDiff ℝ ∞ (g' n) ∧ ContDiff ℝ ∞ (h' n) ∧
        HasCompactSupport (g' n) ∧
        tsupport (g' n) ⊆ meanApproxTimeSet (t₀ - 4) (t₀ + 4) ∧
        MemLp (g' n) 1 volume ∧ (∀ t, HasDerivAt (h' n) (g' n t) t) ∧
        ContDiff ℝ ∞ (fun t ↦ -unitBallHarmonicForceGradientExtended (h' n t)) ∧
        (∀ t, HasDerivAt (fun s ↦ -unitBallHarmonicForceGradientExtended (h' n s))
          (-unitBallHarmonicForceGradientExtended (g' n t)) t)) ∧
      unitBallHarmonicGradientTimeCurve u =ᵐ[volume.restrict (Ioo (t₀ - 4) (t₀ + 4))]
        unitBallHarmonicTimePrimitive u Du p t₀ ∧
      Tendsto (fun n ↦ eLpNorm
        ((Ioo (t₀ - 4) (t₀ + 4)).indicator (unitBallMomentumForceCurve u Du p) - g' n)
          1 volume) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦
        -unitBallHarmonicForceGradientExtended
          ((Ioo (t₀ - 4) (t₀ + 4)).indicator (unitBallMomentumForceCurve u Du p) t) +
            unitBallHarmonicForceGradientExtended (g' n t)) 1 volume) atTop (𝓝 0) ∧
      TendstoUniformly (fun n t ↦ -unitBallHarmonicForceGradientExtended (h' n t))
        (unitBallHarmonicTimePrimitive u Du p t₀) atTop ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc (t₀ - 4) (t₀ + 4) →
        ‖-unitBallHarmonicForceGradientExtended (h' n t)‖ ≤ C := by
  obtain ⟨hf, hg⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  obtain ⟨g', h', hsm, hrep, hconv, _hconv1, hfield, hunif, hbound⟩ :=
    exists_operator_image_smooth_time_sequence (-unitBallHarmonicForceGradientExtended)
      (by linarith) ⟨by linarith, by linarith⟩ (le_refl 1) ENNReal.one_ne_top
      hf (memLp_one_iff_integrable.mpr hg)
      (suitable_unitBall_momentum_hasWeakTimeDerivativeOn hsol hdom)
  refine ⟨g', h', hsm, hrep, hconv, ?_, hunif, hbound⟩
  simpa only [neg_apply, sub_neg_eq_add] using hfield

end FluidSingularSets
