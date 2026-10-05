-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PressureGradientUniqueness
public import FluidSingularSets.PressureForceTime
public import CKN.Foundation.Sobolev.WeakGradientGluingTMeasurable
public import CKN.Core.Step4.PressureGradientGluedUnion

/-!
# Actual pressure derivatives on arbitrary local boxes

A compact local box has a finite cover by genuine pressure-gradient patches.
Their actual weak derivatives glue on a common exceptional time set. Joint
selection and overlap uniqueness then retain the true pressure-gradient class,
without prescribing a spatial or future-time collar size.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Original suitability supplies a weak pressure derivative on an entire
arbitrary local spatial carrier, on a single common good time set. -/
theorem suitable_pressure_slice_derivative_localBox
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J) (i : Fin 3) :
    ∀ᵐ t ∂volume.restrict J, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧
      HasWeakPartialDerivOn B i (fun x ↦ p (x, t)) g := by
  classical
  let K : Set ParabolicPoint := closure B ×ˢ closure J
  have hK : IsCompact K := parabolicHomeomorph.isCompact_preimage.mpr
    (hbox.2.1.prod hbox.2.2.2.2.1)
  have hKdom : K ⊆ spaceTimeSet Ω I := prod_mono hbox.2.2.1 hbox.2.2.2.2.2
  obtain ⟨P, s, _hP, hcover⟩ := exists_finite_suitable_pressure_gradient_cover hsol hK hKdom
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top).ne
  have hp := spatial_memLp_ae_of_joint_memLp (by norm_num : (0 : ℝ) < 3 / 2)
    (hsol.toData.memLp_pressure hbox)
  have hfamily (k : s) : ∀ᵐ t ∂volume.restrict J,
      t ∈ Ioo ((P k.1).center.2 - (P k.1).radius ^ 2)
        ((P k.1).center.2 + (P k.1).radius ^ 2) →
      ∀ j : Fin 3,
        LocallyIntegrableOn (fun x ↦ (P k.1).gradient (x, t) j)
          (vec3Ball (P k.1).center.1 (P k.1).radius) volume ∧
        HasWeakPartialDerivOn (vec3Ball (P k.1).center.1 (P k.1).radius) j
          (fun x ↦ p (x, t)) (fun x ↦ (P k.1).gradient (x, t) j) :=
    ae_restrict_of_ae (ae_imp_of_ae_restrict (P k.1).gradient_weak)
  have hJ : MeasurableSet J := hbox.2.2.2.1.measurableSet
  filter_upwards [hp, ae_all_iff.mpr hfamily, ae_restrict_mem hJ] with t hpt ht htJ
  have hpint : IntegrableOn (fun x ↦ p (x, t)) B volume := hpt.integrable (by norm_num)
  apply exists_weakPartialDerivOn_of_local hbox.1 hpint.locallyIntegrableOn
  intro x hx
  have hz : ((x, t) : ParabolicPoint) ∈ K :=
    ⟨subset_closure hx, subset_closure htJ⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover hz)
  obtain ⟨hks, hzk⟩ := mem_iUnion.mp hk
  have hzk' : x ∈ vec3Ball (P k).center.1 (P k).radius ∧
      t ∈ Ioo ((P k).center.2 - (P k).radius ^ 2)
        ((P k).center.2 + (P k).radius ^ 2) := by
    rw [PressureGradientPatch.carrier, metricBall_eq_parabolicBall] at hzk
    exact ⟨hzk.1, hzk.2⟩
  let V := B ∩ vec3Ball (P k).center.1 (P k).radius
  have hV : IsOpen V := hbox.1.inter (isOpen_vec3Ball _ _)
  have hg := ht ⟨k, hks⟩ hzk'.2 i
  refine ⟨V, hV, ⟨hx, hzk'.1⟩, inter_subset_left,
    fun y ↦ (P k).gradient (y, t) i, hg.1.mono_set inter_subset_right, ?_⟩
  exact hg.2.restrict hV inter_subset_right

/-- The real pressure on an arbitrary local box is jointly integrable. -/
theorem suitable_pressure_integrable_localBox
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J) : IntegrableOn p (B ×ˢ J) volume := by
  let K : Set ParabolicPoint := closure B ×ˢ closure J
  have hK : IsCompact K :=
    parabolicHomeomorph.isCompact_preimage.mpr (hbox.2.1.prod hbox.2.2.2.2.1)
  let : IsFiniteMeasure (volume.restrict (spaceTimeSet B J)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono (Set.prod_mono subset_closure subset_closure)).trans_lt
        hK.measure_lt_top).ne
  exact (hsol.toData.memLp_pressure hbox).integrable (by norm_num)

/-- The actual pressure has a joint measurable weak spatial gradient on any
local box, with the original time interval retained exactly. -/
theorem exists_suitable_measurable_pressure_gradient_localBox
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
        LocallyIntegrableOn (fun x ↦ Dp (x, t) i) B volume ∧
        HasWeakPartialDerivOn B i (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t) i) := by
  obtain ⟨W, _δ, _hδ, hW, hBW, hWc, hWΩ, _hballs⟩ :=
    exists_open_between_of_isCompact hbox.2.1 hsol.1 hbox.2.2.1
  have hWbox : localBox Ω I W J := ⟨hW, hWc, hWΩ, hbox.2.2.2⟩
  have hJ : MeasurableSet J := hbox.2.2.2.1.measurableSet
  obtain ⟨Dp, hDp, hweak⟩ := exists_measurable_weakGradient_on_time_union
    hW hbox.1 hbox.2.1 hBW (J := fun _ : ℕ ↦ J) (fun _ ↦ hJ)
    (by simp only [iUnion_const])
    (fun _ ↦ suitable_pressure_integrable_localBox hsol hWbox)
    (suitable_pressure_slice_derivative_localBox hsol hWbox)
  exact ⟨Dp, hDp, hweak.mono fun _ ht i ↦ ⟨(ht i).1, (ht i).2.1⟩⟩

/-- Every genuine joint weak gradient of the original suitable pressure has
the actual local `L^(5/4)` class. The finite patch bounds transfer by weak
derivative uniqueness, so the result is independent of the selected gradient. -/
theorem suitable_pressure_gradient_memLp_localBox
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J) {Dp : ParabolicPoint → Vec3} (hDp : Measurable Dp)
    (hweak : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ Dp (x, t) i) B volume ∧
      HasWeakPartialDerivOn B i (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t) i)) :
    MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict (spaceTimeSet B J)) := by
  classical
  let K : Set ParabolicPoint := closure B ×ˢ closure J
  have hK : IsCompact K := parabolicHomeomorph.isCompact_preimage.mpr
    (hbox.2.1.prod hbox.2.2.2.2.1)
  have hKdom : K ⊆ spaceTimeSet Ω I := prod_mono hbox.2.2.1 hbox.2.2.2.2.2
  obtain ⟨P, s, _hP, hcover⟩ := exists_finite_suitable_pressure_gradient_cover hsol hK hKdom
  let F : s → ParabolicPoint → Vec3 := fun k ↦ (P k.1).carrier.indicator (P k.1).gradient
  have hF (k : s) : MemLp (F k) (ENNReal.ofReal (5 / 4 : ℝ)) volume :=
    (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet).mpr (P k.1).gradient_memLp
  have hsum : MemLp (fun z ↦ ∑ k : s, ‖F k z‖) (ENNReal.ofReal (5 / 4 : ℝ)) volume :=
    memLp_finsetSum Finset.univ (fun k _ ↦ (hF k).norm)
  have hBJ : MeasurableSet (spaceTimeSet B J) :=
    hbox.1.measurableSet.prod hbox.2.2.2.1.measurableSet
  have heq (k : s) : ∀ᵐ z ∂volume.restrict (spaceTimeSet B J),
      z ∈ (P k.1).carrier → Dp z = (P k.1).gradient z := by
    have h := pressureGradient_ae_eq_on_overlap hbox.1 (isOpen_vec3Ball _ _)
      hDp (P k.1).gradient_measurable hweak (P k.1).gradient_weak
    have h' : Dp =ᵐ[volume.restrict (spaceTimeSet B J ∩ (P k.1).carrier)]
        (P k.1).gradient := by
      simpa only [PressureGradientPatch.carrier, metricBall_eq_parabolicBall, spaceTimeSet]
        using h
    filter_upwards [ae_restrict_mem hBJ, ae_restrict_of_ae (ae_imp_of_ae_restrict h')]
      with z hz ht hzP
    exact ht ⟨hz, hzP⟩
  apply (hsum.mono_measure Measure.restrict_le_self).of_le hDp.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hBJ, ae_all_iff.mpr heq] with z hz ht
  have hzK : z ∈ K := ⟨subset_closure hz.1, subset_closure hz.2⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover hzK)
  obtain ⟨hks, hzk⟩ := mem_iUnion.mp hk
  have hident : ‖Dp z‖ = ‖F ⟨k, hks⟩ z‖ := by
    rw [ht ⟨k, hks⟩ hzk]
    simp only [F, indicator_of_mem hzk]
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ norm_nonneg (F k z)), hident]
  exact Finset.single_le_sum (fun k _ ↦ norm_nonneg (F k z))
    (Finset.mem_univ (⟨k, hks⟩ : s))

/-- Arbitrary local boxes have a genuine jointly measurable pressure gradient
in the box exponent, differentiating the supplied pressure on almost every slice. -/
theorem exists_suitable_pressure_gradient_memLp_localBox
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict (spaceTimeSet B J)) ∧
      ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
        LocallyIntegrableOn (fun x ↦ Dp (x, t) i) B volume ∧
        HasWeakPartialDerivOn B i (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t) i) := by
  obtain ⟨Dp, hDp, hweak⟩ := exists_suitable_measurable_pressure_gradient_localBox hsol hbox
  exact ⟨Dp, hDp, suitable_pressure_gradient_memLp_localBox hsol hbox hDp hweak, hweak⟩

end FluidSingularSets
