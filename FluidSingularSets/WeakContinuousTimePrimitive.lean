-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.WeakTimePressure
public import CKN.Foundation.WeakDerivOneDim
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Actual continuous primitives of weak Banach-valued time derivatives

Bochner integration constructs the primitive of the genuine integrable weak
derivative. Scalar weak-derivative uniqueness identifies its integration
constant by the actual average of the original field minus that primitive.
A countable family of separating evaluations gives one joint AE equality in
the Banach space. Compact continuous spatial fields supply this family from
a countably dense spatial set and the three velocity coordinates.
-/

@[expose] public section

open MeasureTheory Set Filter CKN TopologicalSpace
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every actual integrable Banach-valued density has an absolutely continuous
Bochner interval primitive. -/
theorem banach_intervalIntegral_absolutelyContinuous
    {g : ℝ → E} {a b c : ℝ} (hg : IntervalIntegrable g volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ s in c..t, g s) a b := by
  open AbsolutelyContinuousOnInterval in
  let S := fun Q : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range Q.1, uIoc (Q.2 i).1 (Q.2 i).2
  have hz : Tendsto (fun Q ↦ ∫⁻ t in S Q, ‖g t‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero (ne_of_lt (intervalIntegrable_iff.mp hg).hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have hz' := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hz
  refine squeeze_zero' ?_ ?_ hz'
  · filter_upwards with Q
    exact Finset.sum_nonneg (fun i hi ↦ dist_nonneg)
  have hm : ∀ᶠ Q : ℕ × (ℕ → ℝ × ℝ) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      Q ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hm] with Q hQ
  obtain ⟨hQ₁, hQ₂⟩ := mem_ofPred_eq ▸ hQ
  simp only [Function.comp_apply, S]
  rw [← integral_norm_eq_lintegral_enorm (hg.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hQ₂]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
      (by apply IntervalIntegrable.mono_set' hg; grind [uIoc, uIcc])
      (by apply IntervalIntegrable.mono_set' hg; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hQ (Finset.mem_range.mp hi)),
      intervalIntegral.integral_symm, norm_neg, intervalIntegral.norm_intervalIntegral_eq]
    exact norm_integral_le_integral_norm _
  · intro i hi
    unfold IntegrableOn
    have hs := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hQ
      (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hs]
    exact (IntegrableOn.mono_set hg.def'.norm hs).integrable

/-- A scalar continuous linear evaluation of the true weak field equals the
actual averaged integration constant plus its Bochner primitive. -/
theorem weakTimeDerivative_scalar_ae_primitive
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Ioo a b)
    {f g : ℝ → E} (hf : IntegrableOn f (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) (L : E →L[ℝ] ℝ) :
    (fun t ↦ L (f t)) =ᵐ[volume.restrict (Ioo a b)]
      (fun t ↦ L (average (volume.restrict (Ioo a b))
        (fun s ↦ f s - ∫ τ in c..s, (Ioo a b).indicator g τ)) +
          L (∫ s in c..t, (Ioo a b).indicator g s)) := by
  let J := Ioo a b
  let g₀ := J.indicator g
  let P : ℝ → E := fun t ↦ ∫ s in c..t, g₀ s
  have hg₀ : Integrable g₀ volume := hg.integrable_indicator measurableSet_Ioo
  have hw₀ : HasWeakTimeDerivativeOn J f g₀ := by
    apply hw.congr_ae EventuallyEq.rfl
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [g₀, J, indicator_of_mem ht]
  have hwL := hw₀.continuousLinearMap hf hg₀.integrableOn L
  have hws : HasWeakDerivOn J (fun t ↦ L (f t)) (fun t ↦ L (g₀ t)) := by
    intro η hη
    have h := hwL η hη.1 hη.2.1 hη.2.2
    simpa only [smul_eq_mul, mul_comm] using h
  have hfL : IntegrableOn (fun t ↦ L (f t)) J volume := L.integrable_comp hf
  have hgL : Integrable (fun t ↦ L (g₀ t)) volume := L.integrable_comp hg₀
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hab hc
    (IntegrableOn.locallyIntegrableOn hfL)
    (hgL.locallyIntegrable.locallyIntegrableOn J) hws
  have hP : Continuous P := hg₀.continuous_primitive c
  have hH : IntegrableOn (fun t ↦ f t - P t) J volume :=
    hf.sub (hP.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  have hCa : (fun t ↦ L (f t - P t)) =ᵐ[volume.restrict J] fun _ ↦ C := by
    filter_upwards [ae_restrict_of_ae hC, ae_restrict_mem measurableSet_Ioo] with t ht htJ
    have ht' := ht htJ
    have hi := L.intervalIntegral_comp_comm (hg₀.intervalIntegrable :
      IntervalIntegrable g₀ volume c t)
    rw [hi] at ht'
    rw [map_sub]
    change L (f t) - L (P t) = C
    linarith
  let : IsFiniteMeasure (volume.restrict J) :=
    isFiniteMeasure_restrict.mpr (by dsimp [J]; rw [Real.volume_Ioo]; finiteness)
  have hJ : volume J ≠ 0 := by
    dsimp [J]
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by linarith : 0 < b - a)).ne'
  let : NeZero (volume J) := ⟨hJ⟩
  have havg : L (average (volume.restrict J) (fun t ↦ f t - P t)) = C := by
    have hh := (average_congr hCa).trans (average_const (volume.restrict J) C)
    rw [average_eq] at hh ⊢
    rw [map_smul, ← L.integral_comp_comm hH]
    exact hh
  filter_upwards [hCa] with t ht
  change L (f t) = L (average (volume.restrict J) (fun s ↦ f s - P s)) + L (P t)
  rw [havg]
  rw [map_sub] at ht
  linarith

/-- A countable separating family of true scalar evaluations yields one actual
Banach-valued AE primitive representation. -/
theorem weakTimeDerivative_ae_primitive_of_countable_separating
    {A : Type*} [Countable A] (L : A → E →L[ℝ] ℝ)
    (hsep : ∀ v w : E, (∀ α, L α v = L α w) → v = w)
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Ioo a b)
    {f g : ℝ → E} (hf : IntegrableOn f (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) :
    f =ᵐ[volume.restrict (Ioo a b)] (fun t ↦
      average (volume.restrict (Ioo a b))
        (fun s ↦ f s - ∫ τ in c..s, (Ioo a b).indicator g τ) +
      ∫ s in c..t, (Ioo a b).indicator g s) := by
  have hall : ∀ α, ∀ᵐ t ∂volume.restrict (Ioo a b),
      L α (f t) = L α (average (volume.restrict (Ioo a b))
        (fun s ↦ f s - ∫ τ in c..s, (Ioo a b).indicator g τ)) +
          L α (∫ s in c..t, (Ioo a b).indicator g s) :=
    fun α ↦ weakTimeDerivative_scalar_ae_primitive hab hc hf hg hw (L α)
  filter_upwards [ae_all_iff.mpr hall] with t ht
  apply hsep
  intro α
  rw [map_add]
  exact ht α

/-- An actual weak time derivative and actual Bochner integrability give a
continuous absolutely continuous representative, with both endpoint traces,
the genuine AE derivative and the exact primitive difference identity. -/
theorem exists_continuous_absolutelyContinuous_of_weakTimeDerivative
    {A : Type*} [Countable A] (L : A → E →L[ℝ] ℝ)
    (hsep : ∀ v w : E, (∀ α, L α v = L α w) → v = w)
    {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hf : IntegrableOn f (Ioo a b) volume) (hg : IntegrableOn g (Ioo a b) volume)
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) :
    ∃ m : ℝ → E, Continuous m ∧ AbsolutelyContinuousOnInterval m a b ∧
      f =ᵐ[volume.restrict (Ioo a b)] m ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt m (g t) t) ∧
      ∀ s t : ℝ, m t - m s = ∫ τ in s..t, (Ioo a b).indicator g τ := by
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  let g₀ := (Ioo a b).indicator g
  have hg₀ : Integrable g₀ volume := hg.integrable_indicator measurableSet_Ioo
  let C := average (volume.restrict (Ioo a b)) (fun s ↦ f s - ∫ τ in c..s, g₀ τ)
  let m : ℝ → E := fun t ↦ C + ∫ τ in c..t, g₀ τ
  have hm : Continuous m := continuous_const.add (hg₀.continuous_primitive c)
  have hmAC : AbsolutelyContinuousOnInterval m a b := by
    have hp := banach_intervalIntegral_absolutelyContinuous (a := a) (b := b) (c := c)
      hg₀.intervalIntegrable
      (by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hc)
    have htrans : Isometry (fun x : E ↦ C + x) :=
      Isometry.of_dist_eq fun x y ↦ by simp only [dist_eq_norm, add_sub_add_left_eq_sub]
    exact htrans.lipschitzWith.comp_absolutelyContinuousOnInterval hp
  refine ⟨m, hm, hmAC, ?_, ?_, ?_⟩
  · exact weakTimeDerivative_ae_primitive_of_countable_separating L hsep hab hc hf hg hw
  · filter_upwards [ae_restrict_of_ae
      (LocallyIntegrable.ae_hasDerivAt_integral hg₀.locallyIntegrable),
      ae_restrict_mem measurableSet_Ioo] with t ht htJ
    have hd := (ht c).const_add C
    simpa only [m, g₀, indicator_of_mem htJ] using hd
  · intro s t
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hg₀.intervalIntegrable : IntervalIntegrable g₀ volume c s)
      (hg₀.intervalIntegrable : IntervalIntegrable g₀ volume s t)
    dsimp only [m]
    rw [← hi]
    abel

end Banach

/-- Compact continuous velocity-valued fields have an actual continuous AC
representative whenever their actual weak time derivative is Bochner integrable.
The countable separating evaluations are derived from spatial separability. -/
theorem exists_continuousMap_absolutelyContinuous_of_weakTimeDerivative
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeparableSpace K]
    {a b : ℝ} (hab : a < b) {f g : ℝ → C(K, CKN.Foundation.Parabolic.Vec3)}
    (hf : IntegrableOn f (Ioo a b) volume) (hg : IntegrableOn g (Ioo a b) volume)
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) :
    ∃ m : ℝ → C(K, CKN.Foundation.Parabolic.Vec3),
      Continuous m ∧ AbsolutelyContinuousOnInterval m a b ∧
      f =ᵐ[volume.restrict (Ioo a b)] m ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt m (g t) t) ∧
      ∀ s t : ℝ, m t - m s = ∫ τ in s..t, (Ioo a b).indicator g τ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  let : Countable D := hDc.to_subtype
  let L : (D × Fin 3) → C(K, CKN.Foundation.Parabolic.Vec3) →L[ℝ] ℝ :=
    fun α ↦ (ContinuousLinearMap.proj α.2 : CKN.Foundation.Parabolic.Vec3 →L[ℝ] ℝ).comp
      (ContinuousMap.evalCLM ℝ (α.1 : K))
  apply exists_continuous_absolutelyContinuous_of_weakTimeDerivative L ?_ hab hf hg hw
  intro v w h
  apply ContinuousMap.coe_injective
  apply hDd.denseRange_val.equalizer v.continuous w.continuous
  funext x
  apply funext
  intro i
  exact h (x, i)

end FluidSingularSets
