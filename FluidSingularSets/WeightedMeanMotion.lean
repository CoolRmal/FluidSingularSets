-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PressureGradientFiveFourths
public import CKN.Leray.Support.WeakContL3Support
public import CKN.Leray.StabilityMomentumSupport

/-!
# Motion of actual weighted velocity means

Separated compact spatial tests in the genuine suitable momentum identity give
one-dimensional weak derivatives of weighted velocity means. These derivatives
admit continuous, absolutely continuous representatives through interior terminal
times. The construction uses the supplied velocity, weak gradient and pressure.

The distributional and one-dimensional analytic infrastructure is reused from
the proved CKN results of Scott Armstrong and Vlad Vicol, under Apache 2.0.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step4 CKN.Leray
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual weighted component of a velocity slice. -/
def weightedVelocityMean (B : Set Vec3) (χ : Vec3 → ℝ)
    (u : ParabolicPoint → Vec3) (i : Fin 3) (t : ℝ) : ℝ :=
  ∫ x in B, u (x, t) i * χ x

/-- The actual momentum flux against a scalar spatial weight. -/
def weightedMomentumFlux (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (i : Fin 3) (w : ParabolicPoint) : ℝ :=
  (∑ j : Fin 3, u w i * u w j * spatialDeriv χ j w.1) -
    (∑ j : Fin 3, Du w i j * spatialDeriv χ j w.1) +
    p w * spatialDeriv χ i w.1

private def weightedMeanTest (χ : Vec3 → ℝ) (η : ℝ → ℝ)
    (i : Fin 3) (w : Vec3 × ℝ) : Vec3 :=
  fun j ↦ if j = i then χ w.1 * η w.2 else 0

private theorem weightedMeanTest_tsupport
    (χ : Vec3 → ℝ) (η : ℝ → ℝ) (i : Fin 3) :
    tsupport (weightedMeanTest χ η i) ⊆ tsupport χ ×ˢ tsupport η := by
  apply closure_minimal
  · intro w hw
    have hne : weightedMeanTest χ η i w ≠ 0 := hw
    have hχ : χ w.1 ≠ 0 := by
      intro hzero
      apply hne
      funext j
      simp [weightedMeanTest, hzero]
    have hη : η w.2 ≠ 0 := by
      intro hzero
      apply hne
      funext j
      simp [weightedMeanTest, hzero]
    exact ⟨subset_tsupport χ hχ, subset_tsupport η hη⟩
  · exact (isClosed_tsupport χ).prod (isClosed_tsupport η)

private theorem weightedMeanTest_mem
    {Ω : Set Vec3} {I : Set ℝ} {χ : Vec3 → ℝ} {η : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ω) (hη : IsIntervalTest I η) (i : Fin 3) :
    weightedMeanTest χ η i ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
  refine ⟨?_, ?_, (weightedMeanTest_tsupport χ η i).trans (prod_mono hχs hη.2.2)⟩
  · apply contDiff_pi.mpr
    intro j
    by_cases hji : j = i
    · simpa only [weightedMeanTest, hji, ite_true] using
        CKN.Core.Endgame.contDiff_separatedProduct hχ hη.1
    · simpa only [weightedMeanTest, hji, ite_false] using
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 × ℝ ↦ (0 : ℝ)))
  · apply HasCompactSupport.of_support_subset_isCompact (hχc.isCompact.prod hη.2.1.isCompact)
    exact (subset_tsupport _).trans (weightedMeanTest_tsupport χ η i)

/-- Actual suitability gives the separated scalar momentum identity on every
interior spatial box and time interval containing the compact test supports. -/
theorem suitable_weighted_momentum_identity
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b))
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin 3)
    (η : ℝ → ℝ) (hη : IsIntervalTest (Ioo a b) η) :
    (∫ w, -(u (parabolicHomeomorph.symm w) i * χ w.1 * deriv η w.2) -
      weightedMomentumFlux χ u Du p i (parabolicHomeomorph.symm w) * η w.2
      ∂((volume.restrict B).prod (volume.restrict (Ioo a b)))) = 0 := by
  let Φ := weightedMeanTest χ η i
  have hBΩ : B ⊆ Ω := subset_closure.trans hbox.2.2.1
  have hJI : Ioo a b ⊆ I := subset_closure.trans hbox.2.2.2.2.2
  have htest := weightedMeanTest_mem hχ hχc (hχs.trans hBΩ)
    (show IsIntervalTest I η from ⟨hη.1, hη.2.1, hη.2.2.trans hJI⟩) i
  have hsupport : tsupport (show ParabolicPoint → Vec3 from Φ) ⊆ spaceTimeSet B (Ioo a b) := by
    rw [tsupport_parabolic_eq]
    exact (weightedMeanTest_tsupport χ η i).trans (prod_mono hχs hη.2.2)
  have hmom := (hsol.2.2.2.2.2.2.2.1 Φ htest).2
  have hlocal := stability_momentum_integral_eq_localBox Φ htest hsupport u Du p
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at hmom hlocal
  rw [hlocal] at hmom
  rw [setIntegral_parabolic_to_product] at hmom
  have hmeasure : (volume.restrict B).prod (volume.restrict (Ioo a b)) =
      (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ Ioo a b) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  rw [← hmeasure] at hmom
  have ht (j : Fin 3) (w : ParabolicPoint) :
      timePartial (fun v ↦ Φ v j) w =
        if j = i then χ w.1 * deriv η w.2 else 0 := by
    by_cases hji : j = i
    · simp only [Φ, weightedMeanTest, hji, ite_true]
      exact CKN.Core.Endgame.timePartial_separatedProduct χ hη.1 w
    · simp [Φ, weightedMeanTest, hji, timePartial]
  have hs (j k : Fin 3) (w : ParabolicPoint) :
      spatialPartial (fun v ↦ Φ v j) k w =
        if j = i then spatialDeriv χ k w.1 * η w.2 else 0 := by
    by_cases hji : j = i
    · simp only [Φ, weightedMeanTest, hji, ite_true]
      exact CKN.Core.Endgame.spatialPartial_separatedProduct η hχ k w
    · simp [Φ, weightedMeanTest, hji, spatialPartial]
  convert hmom using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun w ↦ by
    simp only [ht, hs, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, parabolicHomeomorph_symm_apply]
    simp only [weightedMomentumFlux]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring

private theorem memLp_two_of_finite_energy
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {v : α → E} (hv : AEStronglyMeasurable v μ)
    (he : (∫⁻ w, ‖v w‖ₑ ^ (2 : ℝ) ∂μ) < ∞) : MemLp v 2 μ := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hv]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) he.ne

/-- The genuine local energy and pressure classes make every term of the
weighted momentum flux integrable, without stronger velocity hypotheses. -/
theorem suitable_weighted_momentum_terms_integrable
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (i : Fin 3) :
    Integrable (fun w : ParabolicPoint ↦ u w i * χ w.1)
        (volume.restrict (spaceTimeSet B J)) ∧
      Integrable (weightedMomentumFlux χ u Du p i)
        (volume.restrict (spaceTimeSet B J)) := by
  let Q := spaceTimeSet B J
  let μ := (volume : Measure ParabolicPoint).restrict Q
  have hBfinite : volume B < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  have hJfinite : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  let : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    change volume (B ×ˢ J) ≠ ∞
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact (ENNReal.mul_lt_top hBfinite hJfinite).ne
  have he := hsol.toData.energy_lintegral_lt_top hbox
  have hu : MemLp u 2 μ := memLp_two_of_finite_energy
    (hsol.toData.aestronglyMeasurable_velocity hbox)
    ((lintegral_mono fun _ ↦ le_add_of_nonneg_right (by positivity)).trans_lt he)
  have hd : MemLp Du 2 μ := memLp_two_of_finite_energy
    (hsol.toData.aestronglyMeasurable_gradient hbox)
    ((lintegral_mono fun _ ↦ le_add_of_nonneg_left (by positivity)).trans_lt he)
  have hp := (hsol.toData.memLp_pressure hbox).integrable (by norm_num)
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ.continuous
  have hmean : Integrable (fun w : ParabolicPoint ↦ u w i * χ w.1) μ :=
    ((hu.eval i).integrable (by norm_num)).mul_bdd
      (hχ.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun w ↦ hCχ w.1)
  have hdχ (j : Fin 3) : Continuous (spatialDeriv χ j) :=
    (contDiff_spatialDeriv_smooth hχ j).continuous
  have hdcχ (j : Fin 3) : HasCompactSupport (spatialDeriv χ j) :=
    hasCompactSupport_spatialDeriv hχc j
  have hconv (j : Fin 3) : Integrable
      (fun w : ParabolicPoint ↦ u w i * u w j * spatialDeriv χ j w.1) μ := by
    have huu : MemLp (fun w ↦ u w i * u w j) 1 μ := (hu.eval i).mul (hu.eval j)
    obtain ⟨C, hC⟩ := (hdcχ j).exists_bound_of_continuous (hdχ j)
    exact (huu.integrable (by norm_num)).mul_bdd
      ((hdχ j).measurable.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun w ↦ hC w.1)
  have hdiff (j : Fin 3) : Integrable
      (fun w : ParabolicPoint ↦ Du w i j * spatialDeriv χ j w.1) μ := by
    obtain ⟨C, hC⟩ := (hdcχ j).exists_bound_of_continuous (hdχ j)
    exact (((hd.eval i).eval j).integrable (by norm_num)).mul_bdd
      ((hdχ j).measurable.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun w ↦ hC w.1)
  have hpressure : Integrable
      (fun w : ParabolicPoint ↦ p w * spatialDeriv χ i w.1) μ := by
    obtain ⟨C, hC⟩ := (hdcχ i).exists_bound_of_continuous (hdχ i)
    exact hp.mul_bdd ((hdχ i).measurable.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun w ↦ hC w.1)
  exact ⟨hmean, ((integrable_finsetSum Finset.univ fun j _ ↦ hconv j).sub
    (integrable_finsetSum Finset.univ fun j _ ↦ hdiff j)).add hpressure⟩

/-- The actual weighted mean has the spatially integrated momentum flux as
its one-dimensional weak time derivative. -/
theorem suitable_weighted_mean_hasWeakDerivOn
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b))
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin 3) :
    LocallyIntegrableOn (weightedVelocityMean B χ u i) (Ioo a b) volume ∧
      IntegrableOn (fun t ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, t))
        (Ioo a b) volume ∧
      HasWeakDerivOn (Ioo a b) (weightedVelocityMean B χ u i)
        (fun t ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, t)) := by
  obtain ⟨hF, hG⟩ := suitable_weighted_momentum_terms_integrable hsol hbox hχ hχc i
  have hprod : (volume : Measure ParabolicPoint).restrict (spaceTimeSet B (Ioo a b)) =
      (volume.restrict B).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  rw [hprod] at hF hG
  exact weakContL3_productWeakDeriv (volume.restrict B) hF hG
    (suitable_weighted_momentum_identity hsol hbox hχ hχc hχs i)

/-- The actual weighted velocity mean has a continuous absolutely continuous
representative, with the actual integrated momentum flux as its derivative.
The primitive includes both endpoint traces. -/
theorem exists_suitable_weighted_mean_absolutelyContinuous
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b)) (hab : a < b)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin 3) :
    ∃ m : ℝ → ℝ, Continuous m ∧ AbsolutelyContinuousOnInterval m a b ∧
      (weightedVelocityMean B χ u i =ᵐ[volume.restrict (Ioo a b)] m) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt m
        (∫ x in B, weightedMomentumFlux χ u Du p i (x, t)) t) ∧
      ∀ s t : ℝ, m t - m s = ∫ τ in s..t,
        (Ioo a b).indicator
          (fun τ ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, τ)) τ := by
  let g : ℝ → ℝ := fun t ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, t)
  let g₀ := (Ioo a b).indicator g
  let t₀ : ℝ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := ⟨by dsimp [t₀]; linarith, by dsimp [t₀]; linarith⟩
  obtain ⟨hf, hg, hw⟩ := suitable_weighted_mean_hasWeakDerivOn hsol hbox hχ hχc hχs i
  have hg₀ : Integrable g₀ volume := hg.integrable_indicator measurableSet_Ioo
  have hw₀ : HasWeakDerivOn (Ioo a b) (weightedVelocityMean B χ u i) g₀ := by
    intro η hη
    rw [show (∫ t in Ioo a b, g₀ t * η t) = ∫ t in Ioo a b, g t * η t from by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp only [g₀, indicator_of_mem ht]]
    exact hw η hη
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hab ht₀ hf
    (hg₀.locallyIntegrable.locallyIntegrableOn _) hw₀
  let m : ℝ → ℝ := fun t ↦ C + ∫ τ in t₀..t, g₀ τ
  have hmcont : Continuous m := continuous_const.add (hg₀.continuous_primitive t₀)
  have hmac : AbsolutelyContinuousOnInterval m a b := by
    have hprimInt : IntervalIntegrable g₀ volume a b := hg₀.intervalIntegrable
    have hprim := hprimInt.absolutelyContinuousOnInterval_intervalIntegral
      (by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self ht₀)
    have htrans : Isometry (fun x : ℝ ↦ C + x) :=
      Isometry.of_dist_eq fun x y ↦ by simp only [Real.dist_eq, add_sub_add_left_eq_sub]
    exact htrans.lipschitzWith.comp_absolutelyContinuousOnInterval hprim
  refine ⟨m, hmcont, hmac, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hC, ae_restrict_mem measurableSet_Ioo] with t ht htI
    exact ht htI
  · filter_upwards [ae_restrict_of_ae
      (LocallyIntegrable.ae_hasDerivAt_integral hg₀.locallyIntegrable),
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    have hder := (ht t₀).const_add C
    simpa only [m, g₀, indicator_of_mem htI] using hder
  · intro s t
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hg₀.intervalIntegrable : IntervalIntegrable g₀ volume t₀ s)
      (hg₀.intervalIntegrable : IntervalIntegrable g₀ volume s t)
    dsimp only [m]
    linarith only [hsplit]

/-- Integrating over a finite spatial box preserves every finite exponent
strictly larger than one. This is the slice Hölder estimate plus Tonelli. -/
theorem memLp_spatial_integral_of_memLp
    {B : Set Vec3} {J : Set ℝ} (hB : volume B < ∞)
    {a c : ℝ} (hac : a.HolderConjugate c) {F : Vec3 × ℝ → ℝ}
    (hF : MemLp F (ENNReal.ofReal a)
      ((volume.restrict B).prod (volume.restrict J))) :
    MemLp (fun t ↦ ∫ x in B, F (x, t)) (ENNReal.ofReal a) (volume.restrict J) := by
  have hapos := hac.pos
  have hcpos := hac.symm.pos
  have hFm := hF.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun t ↦ ∫ x in B, F (x, t))
      (volume.restrict J) := hFm.prod_swap.integral_prod_right'
  have hp : (∫⁻ w, ‖F w‖ₑ ^ a
      ∂((volume.restrict B).prod (volume.restrict J))) < ∞ := by
    have hp := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.mpr hac.pos).ne' ENNReal.ofReal_ne_top hF.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofReal hac.pos.le] using hp
  let C : ℝ≥0∞ := (volume B ^ (1 / c)) ^ a
  have hC : C < ∞ := ENNReal.rpow_lt_top_of_nonneg hac.pos.le
    (ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1 / c) hB.ne).ne
  have hpower : (∫⁻ t in J, ‖∫ x in B, F (x, t)‖ₑ ^ a) < ∞ := by
    have hle : (∫⁻ t in J, ‖∫ x in B, F (x, t)‖ₑ ^ a) ≤
        ∫⁻ t in J, (∫⁻ x in B, ‖F (x, t)‖ₑ ^ a) * C := by
      apply lintegral_mono_ae
      filter_upwards [hFm.prodMk_right] with t ht
      have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict B) hac
        ht.aemeasurable.enorm (aemeasurable_const : AEMeasurable (fun _ : Vec3 ↦ (1 : ℝ≥0∞)) _)
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
        one_mul, Measure.restrict_apply_univ] at hh
      calc
        ‖∫ x in B, F (x, t)‖ₑ ^ a ≤
            ((∫⁻ x in B, ‖F (x, t)‖ₑ ^ a) ^ (1 / a) * volume B ^ (1 / c)) ^ a :=
          ENNReal.rpow_le_rpow ((enorm_integral_le_lintegral_enorm _).trans hh) hac.pos.le
        _ = (∫⁻ x in B, ‖F (x, t)‖ₑ ^ a) * C := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hac.pos.le, ← ENNReal.rpow_mul,
            show 1 / a * a = 1 by exact div_mul_cancel₀ _ hac.pos.ne', ENNReal.rpow_one]
    apply hle.trans_lt
    rw [lintegral_mul_const' C _ hC.ne,
      ← lintegral_prod_symm _ (hFm.aemeasurable.enorm.pow_const a)]
    exact ENNReal.mul_lt_top hp hC
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hac.pos).ne' ENNReal.ofReal_ne_top hgm,
    ENNReal.toReal_ofReal hac.pos.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hpower.ne

/-- The actual momentum flux has the `3/2` space-time exponent. This uses
cubic velocity integrability from the energy class, quadratic gradient
integrability, and the solution's supplied `3/2` pressure. -/
theorem suitable_weighted_momentum_flux_memLp_threeHalves
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (i : Fin 3) :
    MemLp (weightedMomentumFlux χ u Du p i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet B J)) := by
  let Q := spaceTimeSet B J
  let K := spaceTimeSet (closure B) (closure J)
  let μ := (volume : Measure ParabolicPoint).restrict Q
  have hBfinite : volume B < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  have hJfinite : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  let : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    change volume (B ×ˢ J) ≠ ∞
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact (ENNReal.mul_lt_top hBfinite hJfinite).ne
  have hK : IsCompact K := parabolicHomeomorph.isCompact_preimage.mpr
    (hbox.2.1.prod hbox.2.2.2.2.1)
  have hKsub : K ⊆ spaceTimeSet Ω I := prod_mono hbox.2.2.1 hbox.2.2.2.2.2
  have hu : MemLp u (ENNReal.ofReal (3 : ℝ)) μ :=
    (velocity_memLp_three_on_compact_of_data hsol.toData hK hKsub).mono_measure
      (Measure.restrict_mono_set volume (prod_mono subset_closure subset_closure))
  have he := hsol.toData.energy_lintegral_lt_top hbox
  have hd : MemLp Du 2 μ := memLp_two_of_finite_energy
    (hsol.toData.aestronglyMeasurable_gradient hbox)
    ((lintegral_mono fun _ ↦ le_add_of_nonneg_left (by positivity)).trans_lt he)
  have hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) μ := hsol.toData.memLp_pressure hbox
  have hw (j : Fin 3) : MemLp (fun w : ParabolicPoint ↦ spatialDeriv χ j w.1) ∞ μ := by
    have hm := (contDiff_spatialDeriv_smooth hχ j).continuous.measurable
    obtain ⟨C, hC⟩ := (hasCompactSupport_spatialDeriv hχc j).exists_bound_of_continuous
      (contDiff_spatialDeriv_smooth hχ j).continuous
    exact MemLp.of_bound (hm.comp measurable_fst).aestronglyMeasurable C
      (Eventually.of_forall fun w ↦ hC w.1)
  let : ENNReal.HolderTriple (ENNReal.ofReal (3 : ℝ)) (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : Real.HolderTriple 3 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have hc (j : Fin 3) : MemLp
      (fun w : ParabolicPoint ↦ u w i * u w j * spatialDeriv χ j w.1)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    have hpair : MemLp (fun w ↦ u w i * u w j) (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
      (hu.eval i).mul (hu.eval j)
    exact hpair.mul (hw j)
  have hdiff (j : Fin 3) : MemLp
      (fun w : ParabolicPoint ↦ Du w i j * spatialDeriv χ j w.1)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    have hDj : MemLp (fun w ↦ Du w i j) (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
      ((hd.eval i).eval j).mono_exponent (by norm_num)
    exact hDj.mul (hw j)
  have hpressure : MemLp (fun w : ParabolicPoint ↦ p w * spatialDeriv χ i w.1)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := hp.mul (hw i)
  have hcSum := memLp_finsetSum' Finset.univ (fun j _ ↦ hc j)
  have hdSum := memLp_finsetSum' Finset.univ (fun j _ ↦ hdiff j)
  apply ((hcSum.sub hdSum).add hpressure).ae_eq
  exact Eventually.of_forall fun w ↦ by
    simp only [weightedMomentumFlux, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]

/-- At every fixed positive interior scale, the actual weighted mean's
acceleration belongs to `L^(3/2)` in time. -/
theorem suitable_weighted_mean_acceleration_memLp_threeHalves
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (i : Fin 3) :
    MemLp (fun t ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, t))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J) := by
  have hF := suitable_weighted_momentum_flux_memLp_threeHalves hsol hbox hχ hχc i
  have hprod : (volume : Measure ParabolicPoint).restrict (spaceTimeSet B J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  rw [hprod] at hF
  have hBfinite : volume B < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  exact memLp_spatial_integral_of_memLp hBfinite
    (by norm_num [Real.holderConjugate_iff] : (3 / 2 : ℝ).HolderConjugate 3) hF

/-- The actual weighted mean admits a `W^(1,3/2)` representative through both
endpoint traces, expressed using its ordinary derivative and genuine flux. -/
theorem exists_suitable_weighted_mean_derivative_memLp_threeHalves
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b)) (hab : a < b)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin 3) :
    ∃ m : ℝ → ℝ, Continuous m ∧ AbsolutelyContinuousOnInterval m a b ∧
      MemLp (deriv m) (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (Ioo a b)) ∧
      (weightedVelocityMean B χ u i =ᵐ[volume.restrict (Ioo a b)] m) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt m
        (∫ x in B, weightedMomentumFlux χ u Du p i (x, t)) t) := by
  obtain ⟨m, hmc, hma, hme, hmd, _hinc⟩ :=
    exists_suitable_weighted_mean_absolutelyContinuous hsol hbox hab hχ hχc hχs i
  have hg := suitable_weighted_mean_acceleration_memLp_threeHalves hsol hbox hχ hχc i
  have hd : deriv m =ᵐ[volume.restrict (Ioo a b)]
      (fun t ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, t)) :=
    hmd.mono fun _ ht ↦ ht.deriv
  exact ⟨m, hmc, hma, hg.ae_eq hd.symm, hme, hmd⟩

/-- The divergence-free condition removes the diagonal weak-gradient term
when the actual convection tensor is paired with a scalar spatial weight. -/
theorem weighted_convection_pairing_eq_gradient
    {B : Set Vec3} (hB : IsOpen B) {v : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hv : ∀ i, MemLp (fun x ↦ v x i) 2 (volume.restrict B))
    (hD : ∀ i j, MemLp (fun x ↦ D x i j) 2 (volume.restrict B))
    (hw : ∀ i, HasWeakGradientOn B (fun x ↦ v x i) (fun x ↦ D x i))
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ B → ∫ x in B, ∑ j, v x j * spatialDeriv ψ j x = 0)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin 3) :
    (∫ x in B, ∑ j, v x i * v x j * spatialDeriv χ j x) =
      -(∫ x in B, χ x * ∑ j, v x j * D x i j) := by
  let : ENNReal.HolderTriple 2 2 1 := ENNReal.HolderConjugate.instTwoTwo
  obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχ.continuous
  have hl (j : Fin 3) : Integrable
      (fun x ↦ v x i * v x j * spatialDeriv χ j x) (volume.restrict B) := by
    have hp : MemLp (fun x ↦ v x i * v x j) 1 (volume.restrict B) := (hv i).mul (hv j)
    obtain ⟨Cd, hCd⟩ := (hasCompactSupport_spatialDeriv hχc j).exists_bound_of_continuous
      (contDiff_spatialDeriv_smooth hχ j).continuous
    exact (memLp_one_iff_integrable.mp hp).mul_bdd
      (contDiff_spatialDeriv_smooth hχ j).continuous.aestronglyMeasurable
      (Eventually.of_forall hCd)
  have hr (j : Fin 3) : Integrable
      (fun x ↦ (D x i j * v x j + v x i * D x j j) * χ x) (volume.restrict B) := by
    have hp : MemLp (fun x ↦ D x i j * v x j) 1 (volume.restrict B) := (hD i j).mul (hv j)
    have hq : MemLp (fun x ↦ v x i * D x j j) 1 (volume.restrict B) := (hv i).mul (hD j j)
    exact (memLp_one_iff_integrable.mp (hp.add hq)).mul_bdd hχ.continuous.aestronglyMeasurable
      (Eventually.of_forall hC)
  have hparts (j : Fin 3) :
      (∫ x in B, v x i * v x j * spatialDeriv χ j x) =
        -(∫ x in B, (D x i j * v x j + v x i * D x j j) * χ x) :=
    HasWeakGradientOn.mul_of_memLp_two hB (hv i) (hv j) (hD i) (hD j) (hw i) (hw j)
      j χ hχ hχc hχs
  have ht := weak_gradient_trace_eq_zero_ae hB hv hD hw hdiv
  calc
    _ = ∑ j, ∫ x in B, v x i * v x j * spatialDeriv χ j x :=
      integral_finsetSum Finset.univ (fun j _ ↦ hl j)
    _ = -(∑ j, ∫ x in B, (D x i j * v x j + v x i * D x j j) * χ x) := by
      simp only [hparts, Finset.sum_neg_distrib]
    _ = -(∫ x in B, ∑ j, (D x i j * v x j + v x i * D x j j) * χ x) := by
      rw [integral_finsetSum Finset.univ (fun j _ ↦ hr j)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ht] with x hx
      change (∑ j, D x j j) = 0 at hx
      calc
        _ = ∑ j, (χ x * (v x j * D x i j) + v x i * χ x * D x j j) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = χ x * (∑ j, v x j * D x i j) + v x i * χ x * (∑ j, D x j j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = _ := by rw [hx, mul_zero, add_zero]

/-- Genuine suitable velocity and its supplied weak gradient satisfy the
weighted convection identity on almost every time slice of each local box. -/
theorem suitable_weighted_convection_eq_gradient
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin 3) :
    ∀ᵐ t ∂volume.restrict J,
      (∫ x in B, ∑ j, u (x, t) i * u (x, t) j * spatialDeriv χ j x) =
        -(∫ x in B, χ x * ∑ j, u (x, t) j * Du (x, t) i j) := by
  have hBΩ : B ⊆ Ω := subset_closure.trans hbox.2.2.1
  have hJI : J ⊆ I := subset_closure.trans hbox.2.2.2.2.2
  have hmem := slice_memLp_ae_of_sws hsol hbox
  have hgrad := (hsol.2.2.2.2.2.1 B J hbox).2.2.2.2.2.2.2.2
  have hgradAll : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn B (fun x ↦ u (x, t) i) (fun x ↦ Du (x, t) i) :=
    ae_all_iff.mpr hgrad
  have hloc : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      LocallyIntegrableOn (fun x ↦ u (x, t) j) B volume := by
    filter_upwards [hmem] with t ht j
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ht.1.eval j).locallyIntegrable (by norm_num))
  have hdiv := ae_slice_divergence_zero_of_forall_test hbox.1 hloc (by
    intro ψ hψ hψc hψB
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI
      (divfree_slice_weak_of_suitable hsol ψ hψ hψc (hψB.trans hBΩ))] with t ht
    have hz (x : Vec3) (hx : x ∉ tsupport ψ) :
        (∑ j, u (x, t) j * (fderiv ℝ ψ x) (basisVec j)) = 0 := by
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
      simp only [zero_apply, mul_zero, Finset.sum_const_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ hz x (fun h ↦ hx (hψB h))),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ hz x (fun h ↦ hx (hBΩ (hψB h))))]
    exact ht)
  filter_upwards [hmem, hgradAll, hdiv] with t hm hw hd
  exact weighted_convection_pairing_eq_gradient hbox.1 (fun j ↦ hm.1.eval j)
    (fun j k ↦ (hm.2.eval j).eval k) hw hd hχ hχc hχs i

/-- Replacing the actual convection tensor and pressure pairings by their
weak-gradient forms gives the acceleration formula used by the charge bound. -/
theorem suitable_weighted_flux_eq_gradient
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J)
    (hDp : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakPartialDerivOn B i (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t) i))
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin 3) :
    ∀ᵐ t ∂volume.restrict J,
      (∫ x in B, weightedMomentumFlux χ u Du p i (x, t)) =
        -(∫ x in B, ∑ j, Du (x, t) i j * spatialDeriv χ j x) -
          (∫ x in B, χ x * ∑ j, u (x, t) j * Du (x, t) i j) -
          (∫ x in B, Dp (x, t) i * χ x) := by
  have hBfinite : volume B < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  have hJfinite : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfinite.ne
  let : IsFiniteMeasure ((volume : Measure ParabolicPoint).restrict (spaceTimeSet B J)) := by
    apply isFiniteMeasure_restrict.mpr
    change volume (B ×ˢ J) ≠ ∞
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact (ENNReal.mul_lt_top hBfinite hJfinite).ne
  have hp := (hsol.toData.memLp_pressure hbox).integrable (by norm_num)
  have hprod : (volume : Measure ParabolicPoint).restrict (spaceTimeSet B J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  rw [hprod] at hp
  filter_upwards [suitable_weighted_convection_eq_gradient hsol hbox hχ hχc hχs i,
    slice_memLp_ae_of_sws hsol hbox, hp.prod_left_ae, hDp] with t hc hm hp hd
  have hdc (j : Fin 3) : Continuous (spatialDeriv χ j) :=
    (contDiff_spatialDeriv_smooth hχ j).continuous
  have hdcc (j : Fin 3) : HasCompactSupport (spatialDeriv χ j) :=
    hasCompactSupport_spatialDeriv hχc j
  have hcj (j : Fin 3) : Integrable
      (fun x ↦ u (x, t) i * u (x, t) j * spatialDeriv χ j x) (volume.restrict B) := by
    have hpair : MemLp (fun x ↦ u (x, t) i * u (x, t) j) 1 (volume.restrict B) :=
      (hm.1.eval i).mul (hm.1.eval j)
    obtain ⟨C, hC⟩ := (hdcc j).exists_bound_of_continuous (hdc j)
    exact (memLp_one_iff_integrable.mp hpair).mul_bdd (hdc j).aestronglyMeasurable
      (Eventually.of_forall hC)
  have hdj (j : Fin 3) : Integrable
      (fun x ↦ Du (x, t) i j * spatialDeriv χ j x) (volume.restrict B) := by
    obtain ⟨C, hC⟩ := (hdcc j).exists_bound_of_continuous (hdc j)
    exact (((hm.2.eval i).eval j).integrable (by norm_num)).mul_bdd
      (hdc j).aestronglyMeasurable (Eventually.of_forall hC)
  have hpi : Integrable (fun x ↦ p (x, t) * spatialDeriv χ i x) (volume.restrict B) := by
    obtain ⟨C, hC⟩ := (hdcc i).exists_bound_of_continuous (hdc i)
    exact hp.mul_bdd (hdc i).aestronglyMeasurable (Eventually.of_forall hC)
  have hcs := integrable_finsetSum Finset.univ (fun j _ ↦ hcj j)
  have hds := integrable_finsetSum Finset.univ (fun j _ ↦ hdj j)
  have hpressure := hd i χ hχ hχc hχs
  change (∫ x in B, p (x, t) * spatialDeriv χ i x) =
    -(∫ x in B, Dp (x, t) i * χ x) at hpressure
  change (∫ x in B,
    (∑ j, u (x, t) i * u (x, t) j * spatialDeriv χ j x) -
      (∑ j, Du (x, t) i j * spatialDeriv χ j x) + p (x, t) * spatialDeriv χ i x) = _
  have hAdd := integral_add (hcs.sub hds) hpi
  have hSub := integral_sub hcs hds
  simp only [Pi.sub_apply] at hAdd
  rw [hAdd, hSub, hc, hpressure]
  ring

/-- The full weak-gradient acceleration formula on an interior cylinder,
with its actual `5/4` pressure gradient constructed from suitability. -/
theorem exists_suitable_weighted_pressure_gradient_acceleration
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ vec3Ball z₀.1 (R / 2))
    (i : Fin 3) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (vec3Ball z₀.1 (R / 2) ×ˢ
          Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4))) ∧
      ∀ᵐ t ∂volume.restrict (Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)),
        (∫ x in vec3Ball z₀.1 (R / 2), weightedMomentumFlux χ u Du p i (x, t)) =
          -(∫ x in vec3Ball z₀.1 (R / 2), ∑ j, Du (x, t) i j * spatialDeriv χ j x) -
            (∫ x in vec3Ball z₀.1 (R / 2), χ x * ∑ j, u (x, t) j * Du (x, t) i j) -
            (∫ x in vec3Ball z₀.1 (R / 2), Dp (x, t) i * χ x) := by
  have hboxBig := CKN.Core.Endgame.localBox_of_parabolic_ball hR hdom
  have hhalf : 0 < R / 2 := by positivity
  have htime : z₀.2 - R ^ 2 / 4 < z₀.2 + R ^ 2 / 4 := by nlinarith [sq_pos_of_pos hR]
  have hbox : localBox Ω I (vec3Ball z₀.1 (R / 2))
      (Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)) := by
    refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hhalf,
      (closure_mono (vec3Ball_mono (by linarith))).trans hboxBig.2.2.1,
      ordConnected_Ioo, ?_, ?_⟩
    · rw [closure_Ioo htime.ne]
      exact isCompact_Icc
    · rw [closure_Ioo htime.ne]
      intro t ht
      apply hboxBig.2.2.2.2.2
      rw [closure_Ioo (by nlinarith [sq_pos_of_pos hR] :
        z₀.2 - R ^ 2 ≠ z₀.2 + R ^ 2)]
      constructor <;> linarith [ht.1, ht.2, sq_nonneg R]
  obtain ⟨Dp, hDpm, hDpLp, hDpw⟩ :=
    exists_suitable_pressure_gradient_memLp_fiveFourths hsol z₀ hR hdom
  exact ⟨Dp, hDpm, hDpLp, suitable_weighted_flux_eq_gradient hsol hbox
    (hDpw.mono fun _ ht j ↦ (ht j).2) hχ hχc hχs i⟩

end FluidSingularSets
