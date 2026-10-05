-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.CompactBoxDensity
public import FluidSingularSets.MeanMotionBound

@[expose] public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Slice weak-gradient uniqueness and genuine joint measurability identify
the entire spatial pressure gradient almost everywhere on a space-time box. -/
theorem pressureGradient_ae_eq_on_box
    {U : Set Vec3} {J : Set ℝ} (hU : IsOpen U)
    {p : ParabolicPoint → ℝ} {D E : ParabolicPoint → Vec3}
    (hD : Measurable D) (hE : Measurable E)
    (hDw : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ D (x, t) i) U volume ∧
      HasWeakPartialDerivOn U i (fun x ↦ p (x, t)) (fun x ↦ D (x, t) i))
    (hEw : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ E (x, t) i) U volume ∧
      HasWeakPartialDerivOn U i (fun x ↦ p (x, t)) (fun x ↦ E (x, t) i)) :
    D =ᵐ[volume.restrict (spaceTimeSet U J)] E := by
  have hDprod : Measurable (fun w : Vec3 × ℝ ↦ D (w.1, w.2)) :=
    hD.comp parabolicHomeomorph.symm.continuous.measurable
  have hEprod : Measurable (fun w : Vec3 × ℝ ↦ E (w.1, w.2)) :=
    hE.comp parabolicHomeomorph.symm.continuous.measurable
  have heq : MeasurableSet {w : Vec3 × ℝ | D (w.1, w.2) = E (w.1, w.2)} :=
    measurableSet_eq_fun hDprod hEprod
  have hslices : ∀ᵐ t ∂volume.restrict J, ∀ᵐ x ∂volume.restrict U,
      D (x, t) = E (x, t) := by
    filter_upwards [hDw, hEw] with t htD htE
    have hcoords : ∀ i : Fin 3, (fun x ↦ D (x, t) i) =ᵐ[volume.restrict U]
        (fun x ↦ E (x, t) i) := fun i ↦
      HasWeakPartialDerivOn.ae_eq hU (htD i).1 (htE i).1 (htD i).2 (htE i).2
    filter_upwards [ae_all_iff.mpr hcoords] with x hx
    exact funext hx
  have hjoint : ∀ᵐ w ∂(volume.restrict U).prod (volume.restrict J),
      D (w.1, w.2) = E (w.1, w.2) :=
    (Measure.ae_prod_iff_ae_ae heq).mpr ((Measure.ae_ae_comm heq).mpr hslices)
  change ∀ᵐ w ∂volume.restrict (U ×ˢ J), D w = E w
  rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
  simpa only [ParabolicPoint, Prod.eta] using hjoint

/-- Independently constructed pressure gradients coincide on the overlap of
their open spatial patches and measurable time windows. -/
theorem pressureGradient_ae_eq_on_overlap
    {U V : Set Vec3} {J K : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    {p : ParabolicPoint → ℝ} {D E : ParabolicPoint → Vec3}
    (hD : Measurable D) (hE : Measurable E)
    (hDw : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ D (x, t) i) U volume ∧
      HasWeakPartialDerivOn U i (fun x ↦ p (x, t)) (fun x ↦ D (x, t) i))
    (hEw : ∀ᵐ t ∂volume.restrict K, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ E (x, t) i) V volume ∧
      HasWeakPartialDerivOn V i (fun x ↦ p (x, t)) (fun x ↦ E (x, t) i)) :
    D =ᵐ[volume.restrict (spaceTimeSet U J ∩ spaceTimeSet V K)] E := by
  rw [spaceTimeSet, spaceTimeSet, prod_inter_prod]
  apply pressureGradient_ae_eq_on_box (hU.inter hV) hD hE
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hDw] with t ht i
    exact ⟨(ht i).1.mono_set inter_subset_left,
      (ht i).2.restrict (hU.inter hV) inter_subset_left⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right hEw] with t ht i
    exact ⟨(ht i).1.mono_set inter_subset_right,
      (ht i).2.restrict (hU.inter hV) inter_subset_right⟩

/-- Genuine independently chosen pressure patches have identical gradients
almost everywhere wherever their actual carriers overlap. -/
theorem PressureGradientPatch.gradient_ae_eq_on_overlap
    {p : ParabolicPoint → ℝ} (P Q : PressureGradientPatch p) :
    P.gradient =ᵐ[volume.restrict (P.carrier ∩ Q.carrier)] Q.gradient := by
  have h := pressureGradient_ae_eq_on_overlap
    (isOpen_vec3Ball P.center.1 P.radius) (isOpen_vec3Ball Q.center.1 Q.radius)
    P.gradient_measurable Q.gradient_measurable P.gradient_weak Q.gradient_weak
  simpa only [PressureGradientPatch.carrier, metricBall_eq_parabolicBall,
    spaceTimeSet] using h

/-- A genuine fresh pressure gradient inherits the compact common measure's
charge bound. The equality with the independently chosen patch is proved
from weak derivatives, rather than imposed as a hypothesis. -/
theorem compactBoxMeasure_charge_le_of_weak_pressure_gradient
    {ι : Type*} {p : ParabolicPoint → ℝ}
    (S : Set ParabolicPoint) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (P : ι → PressureGradientPatch p) (t : Finset ι)
    {i : ι} (hi : i ∈ t) {A : Set ParabolicPoint}
    (hA : MeasurableSet A) (hAS : A ⊆ S) (hAP : A ⊆ (P i).carrier)
    {U : Set Vec3} {J : Set ℝ} (hU : IsOpen U)
    (hAQ : A ⊆ spaceTimeSet U J) {D : ParabolicPoint → Vec3} (hD : Measurable D)
    (hDw : ∀ᵐ s ∂volume.restrict J, ∀ k : Fin 3,
      LocallyIntegrableOn (fun x ↦ D (x, s) k) U volume ∧
      HasWeakPartialDerivOn U k (fun x ↦ p (x, s)) (fun x ↦ D (x, s) k)) :
    (∫⁻ w in A, (‖Du w‖ₑ ^ (2 : ℕ) + ‖u w‖ₑ ^ (10 / 3 : ℝ)) +
      ‖D w‖ₑ ^ (5 / 4 : ℝ)) ≤ compactBoxMeasure S u Du P t A := by
  have heq := pressureGradient_ae_eq_on_overlap hU
    (isOpen_vec3Ball (P i).center.1 (P i).radius) hD (P i).gradient_measurable
    hDw (P i).gradient_weak
  have hsub : A ⊆ spaceTimeSet U J ∩ spaceTimeSet
      (vec3Ball (P i).center.1 (P i).radius)
      (Ioo ((P i).center.2 - (P i).radius ^ 2)
        ((P i).center.2 + (P i).radius ^ 2)) := by
    intro w hw
    refine ⟨hAQ hw, ?_⟩
    have hp := hAP hw
    simpa only [PressureGradientPatch.carrier, metricBall_eq_parabolicBall,
      spaceTimeSet] using hp
  have heqA := ae_restrict_of_ae_restrict_of_subset hsub heq
  calc
    _ = ∫⁻ w in A, (‖Du w‖ₑ ^ (2 : ℕ) + ‖u w‖ₑ ^ (10 / 3 : ℝ)) +
        ‖(P i).gradient w‖ₑ ^ (5 / 4 : ℝ) :=
      lintegral_congr_ae (heqA.mono fun _ hw ↦ by rw [hw])
    _ ≤ _ := compactBoxMeasure_charge_le S u Du P t hi hA hAS hAP

/-- The genuine finite real mean-motion charge equals its nonnegative density
integral, with the exact native velocity and gradient norms. -/
theorem ofReal_meanMotionCharge_eq_lintegral
    {A : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {D : ParabolicPoint → Vec3}
    (hu : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict A))
    (hDu : MemLp Du 2 (volume.restrict A))
    (hD : MemLp D (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict A)) :
    ENNReal.ofReal (meanMotionCharge A u Du D) =
      ∫⁻ w in A, (‖Du w‖ₑ ^ (2 : ℕ) + ‖u w‖ₑ ^ (10 / 3 : ℝ)) +
        ‖D w‖ₑ ^ (5 / 4 : ℝ) := by
  have huInt : Integrable (fun w ↦ ‖u w‖ ^ (10 / 3 : ℝ)) (volume.restrict A) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3)] using
      hu.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  have hDuInt : Integrable (fun w ↦ ‖Du w‖ ^ (2 : ℝ)) (volume.restrict A) := by
    simpa only [ENNReal.toReal_ofNat] using hDu.integrable_norm_rpow
      (by norm_num) (by norm_num)
  have hDInt : Integrable (fun w ↦ ‖D w‖ ^ (5 / 4 : ℝ)) (volume.restrict A) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)] using
      hD.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  have hint : Integrable (fun w ↦ ‖Du w‖ ^ (2 : ℝ) + ‖u w‖ ^ (10 / 3 : ℝ) +
      ‖D w‖ ^ (5 / 4 : ℝ)) (volume.restrict A) := (hDuInt.add huInt).add hDInt
  unfold meanMotionCharge
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun _ ↦ by positivity)]
  apply lintegral_congr
  intro w
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  simp only [ofReal_norm, ENNReal.rpow_two]

/-- Actual compact suitable data and a freshly constructed genuine pressure
gradient give a real charge controlled by the fixed compact common measure.
Weak uniqueness proves compatibility with the independently chosen patch. -/
theorem meanMotionCharge_le_compactBoxMeasure_of_weak_pressure_gradient
    {ι : Type*} {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {S : Set ParabolicPoint} (hS : IsCompact S) (hSdom : S ⊆ spaceTimeSet Ω I)
    (P : ι → PressureGradientPatch p) (t : Finset ι) {i : ι} (hi : i ∈ t)
    {A : Set ParabolicPoint} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAP : A ⊆ (P i).carrier) {U : Set Vec3} {J : Set ℝ} (hU : IsOpen U)
    (hAQ : A ⊆ spaceTimeSet U J) {D : ParabolicPoint → Vec3} (hD : Measurable D)
    (hDmem : MemLp D (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict A))
    (hDw : ∀ᵐ s ∂volume.restrict J, ∀ k : Fin 3,
      LocallyIntegrableOn (fun x ↦ D (x, s) k) U volume ∧
      HasWeakPartialDerivOn U k (fun x ↦ p (x, s)) (fun x ↦ D (x, s) k)) :
    meanMotionCharge A u Du D ≤ (compactBoxMeasure S u Du P t A).toReal := by
  let := compactBoxMeasure_finite hsol hS hSdom P t
  have hu := (velocity_memLp_tenThirds_on_compact_of_data hsol.toData hS hSdom).mono_measure
    (Measure.restrict_mono_set volume hAS)
  have hDu := (gradient_memLp_two_on_compact_of_data hsol.toData hS hSdom).mono_measure
    (Measure.restrict_mono_set volume hAS)
  have hle := compactBoxMeasure_charge_le_of_weak_pressure_gradient S u Du P t hi
    hA hAS hAP hU hAQ hD hDw
  rw [← ofReal_meanMotionCharge_eq_lintegral hu hDu hDmem] at hle
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hle
  have hnonneg : 0 ≤ meanMotionCharge A u Du D := integral_nonneg fun _ ↦ by positivity
  simpa only [ENNReal.toReal_ofReal hnonneg] using hreal

/-- In particular the fresh gradient used by the actual mean-motion theorem
has its backward charge bounded by the fixed common measure of the
containing symmetric parabolic ball. -/
theorem meanMotionCharge_backward_ball_le_compactBoxMeasure
    {ι : Type*} {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {S : Set ParabolicPoint} (hS : IsCompact S) (hSdom : S ⊆ spaceTimeSet Ω I)
    (P : ι → PressureGradientPatch p) (t : Finset ι) {i : ι} (hi : i ∈ t)
    {z : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hBS : Metric.ball z (2 * R) ⊆ S) (hBP : Metric.ball z (2 * R) ⊆ (P i).carrier)
    {D : ParabolicPoint → Vec3} (hD : Measurable D)
    (hDmem : MemLp D (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball z.1 (2 * R))
        (Ioo (z.2 - (2 * R) ^ 2) z.2))))
    (hDw : ∀ᵐ s ∂volume.restrict (Ioo (z.2 - (2 * R) ^ 2) z.2), ∀ k : Fin 3,
      LocallyIntegrableOn (fun x ↦ D (x, s) k) (vec3Ball z.1 (2 * R)) volume ∧
      HasWeakPartialDerivOn (vec3Ball z.1 (2 * R)) k
        (fun x ↦ p (x, s)) (fun x ↦ D (x, s) k)) :
    meanMotionCharge (spaceTimeSet (vec3Ball z.1 (2 * R))
      (Ioo (z.2 - (2 * R) ^ 2) z.2)) u Du D ≤
        (compactBoxMeasure S u Du P t (Metric.ball z (2 * R))).toReal := by
  let := compactBoxMeasure_finite hsol hS hSdom P t
  have hQ : spaceTimeSet (vec3Ball z.1 (2 * R))
      (Ioo (z.2 - (2 * R) ^ 2) z.2) ⊆ Metric.ball z (2 * R) := by
    intro w hw
    rw [metricBall_eq_parabolicBall]
    exact ⟨hw.1, hw.2.1, lt_trans hw.2.2 (by nlinarith [sq_pos_of_pos hR])⟩
  exact (meanMotionCharge_le_compactBoxMeasure_of_weak_pressure_gradient hsol hS hSdom
    P t hi ((isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo)
    (hQ.trans hBS) (hQ.trans hBP) (isOpen_vec3Ball _ _) (subset_refl _) hD hDmem hDw).trans
      (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hQ))

end FluidSingularSets
