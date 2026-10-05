-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PressureGradientFiveFourths
public import FluidSingularSets.LocalizedGradientPatch
public import CKN.Foundation.Parabolic.BallDisplays

/-!
# A finite genuine density for the box covering argument

Actual suitability constructs a measurable pressure gradient on a neighborhood of
each interior point. A finite subcover of a compact set supplies a single finite
measure dominating the velocity, velocity-gradient and one local pressure-gradient
charge on every sufficiently small contained set. No pressure-gradient hypothesis
is imposed on the solution.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace FluidSingularSets

/-- Local pressure-gradient data, subsequently constructed from actual suitability. -/
structure PressureGradientPatch (p : ParabolicPoint → ℝ) where
  center : ParabolicPoint
  radius : ℝ
  radius_pos : 0 < radius
  gradient : ParabolicPoint → Vec3
  gradient_measurable : Measurable gradient
  gradient_memLp : MemLp gradient (ENNReal.ofReal (5 / 4 : ℝ))
    (volume.restrict (Metric.ball center radius))
  gradient_weak : ∀ᵐ s ∂volume.restrict
      (Ioo (center.2 - radius ^ 2) (center.2 + radius ^ 2)), ∀ i : Fin 3,
    LocallyIntegrableOn (fun x ↦ gradient (x, s) i) (vec3Ball center.1 radius) volume ∧
    CKN.HasWeakPartialDerivOn (vec3Ball center.1 radius) i
      (fun x ↦ p (x, s)) (fun x ↦ gradient (x, s) i)

/-- The geometric carrier of one actual pressure-gradient patch. -/
def PressureGradientPatch.carrier {p : ParabolicPoint → ℝ}
    (P : PressureGradientPatch p) : Set ParabolicPoint := Metric.ball P.center P.radius

/-- Its genuine finite pressure-gradient density measure. -/
def PressureGradientPatch.densityMeasure {p : ParabolicPoint → ℝ}
    (P : PressureGradientPatch p) : Measure ParabolicPoint :=
  (volume.restrict P.carrier).withDensity (fun z ↦ ‖P.gradient z‖ₑ ^ (5 / 4 : ℝ))

instance {p : ParabolicPoint → ℝ} (P : PressureGradientPatch p) :
    IsFiniteMeasure P.densityMeasure := by
  apply isFiniteMeasure_withDensity
  exact ((memLp_ofReal_iff_lintegral_enorm_rpow_lt_top (by norm_num)
    P.gradient_memLp.aestronglyMeasurable).1 P.gradient_memLp).ne

/-- Every point in the suitable solution's open carrier has an actual patch. -/
theorem exists_suitable_pressure_gradient_patch
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} (hz : z ∈ CKN.spaceTimeSet Ω I) :
    ∃ P : PressureGradientPatch p, P.center = z ∧ P.carrier ⊆ CKN.spaceTimeSet Ω I := by
  have hdom := isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hdom z hz
  have hR : 0 < δ / 2 := by positivity
  have hdouble : Metric.ball z (2 * (δ / 2)) ⊆ CKN.spaceTimeSet Ω I := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hball
  obtain ⟨D, hD, hmem, hweak⟩ :=
    exists_suitable_pressure_gradient_memLp_fiveFourths hsol z hR hdouble
  let P : PressureGradientPatch p :=
    { center := z
      radius := δ / 2 / 2
      radius_pos := by positivity
      gradient := D
      gradient_measurable := hD
      gradient_memLp := by
        rw [metricBall_eq_parabolicBall]
        simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hmem
      gradient_weak := by
        simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hweak }
  refine ⟨P, rfl, ?_⟩
  exact (Metric.ball_subset_ball (by dsimp [P]; linarith)).trans hball

/-- A finite subcover retains genuine gradients for the supplied pressure. -/
theorem exists_finite_suitable_pressure_gradient_cover
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    ∃ (P : K → PressureGradientPatch p) (t : Finset K),
      (∀ z, (P z).center = z.1 ∧ (P z).carrier ⊆ CKN.spaceTimeSet Ω I) ∧
      K ⊆ ⋃ z ∈ t, (P z).carrier := by
  classical
  choose P hP using fun z : K ↦ exists_suitable_pressure_gradient_patch hsol (hKsub z.2)
  have hcover : K ⊆ ⋃ z : K, (P z).carrier := by
    intro z hz
    apply mem_iUnion.mpr
    refine ⟨⟨z, hz⟩, ?_⟩
    change dist z (P ⟨z, hz⟩).center < (P ⟨z, hz⟩).radius
    rw [(hP ⟨z, hz⟩).1, dist_self]
    exact (P ⟨z, hz⟩).radius_pos
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K ↦ (P z).carrier)
    (fun _ ↦ Metric.isOpen_ball) hcover
  exact ⟨P, t, hP, ht⟩

/-- Density of the actual velocity and velocity gradient on a compact patch. -/
def compactBoxBaseMeasure (S : Set ParabolicPoint)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) :
    Measure ParabolicPoint :=
  (volume.restrict S).withDensity
    (fun z ↦ ‖Du z‖ₑ ^ (2 : ℕ) + ‖u z‖ₑ ^ (10 / 3 : ℝ))

/-- Actual suitability makes the base density finite on a compact interior patch. -/
theorem compactBoxBaseMeasure_finite
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {S : Set ParabolicPoint} (hS : IsCompact S) (hSsub : S ⊆ CKN.spaceTimeSet Ω I) :
    IsFiniteMeasure (compactBoxBaseMeasure S u Du) := by
  have hfinite := compact_velocity_pressure_gradient_charges hsol hS hSsub
  have hDu := CKN.gradient_memLp_two_on_compact_of_data hsol.toData hS hSsub
  apply isFiniteMeasure_withDensity
  rw [lintegral_add_left' (hDu.aestronglyMeasurable.enorm.pow_const 2)]
  exact (ENNReal.add_lt_top.2 ⟨hfinite.2.2, hfinite.1⟩).ne

/-- The patch measure gives exactly the supplied gradient charge on a contained set. -/
theorem PressureGradientPatch.densityMeasure_apply_of_subset
    {p : ParabolicPoint → ℝ} (P : PressureGradientPatch p)
    {A : Set ParabolicPoint} (hA : MeasurableSet A) (hAP : A ⊆ P.carrier) :
    P.densityMeasure A = ∫⁻ z in A, ‖P.gradient z‖ₑ ^ (5 / 4 : ℝ) := by
  rw [densityMeasure, withDensity_apply _ hA, Measure.restrict_restrict_of_subset hAP]

/-- The base measure gives exactly the actual velocity and gradient charge on a contained set. -/
theorem compactBoxBaseMeasure_apply_of_subset
    (S : Set ParabolicPoint) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    {A : Set ParabolicPoint} (hA : MeasurableSet A) (hAS : A ⊆ S) :
    compactBoxBaseMeasure S u Du A =
      ∫⁻ z in A, ‖Du z‖ₑ ^ (2 : ℕ) + ‖u z‖ₑ ^ (10 / 3 : ℝ) := by
  rw [compactBoxBaseMeasure, withDensity_apply _ hA,
    Measure.restrict_restrict_of_subset hAS]

/-- One finite measure records the actual base density and a finite family of pressure patches. -/
def compactBoxMeasure {ι : Type*} {p : ParabolicPoint → ℝ}
    (S : Set ParabolicPoint) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (P : ι → PressureGradientPatch p) (t : Finset ι) :
    Measure ParabolicPoint := compactBoxBaseMeasure S u Du + ∑ i ∈ t, (P i).densityMeasure

/-- Every contained actual three-term charge is dominated by that same measure. -/
theorem compactBoxMeasure_charge_le {ι : Type*} {p : ParabolicPoint → ℝ}
    (S : Set ParabolicPoint) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (P : ι → PressureGradientPatch p) (t : Finset ι)
    {i : ι} (hi : i ∈ t) {A : Set ParabolicPoint}
    (hA : MeasurableSet A) (hAS : A ⊆ S) (hAP : A ⊆ (P i).carrier) :
    (∫⁻ z in A, (‖Du z‖ₑ ^ (2 : ℕ) + ‖u z‖ₑ ^ (10 / 3 : ℝ)) +
        ‖(P i).gradient z‖ₑ ^ (5 / 4 : ℝ)) ≤ compactBoxMeasure S u Du P t A := by
  rw [lintegral_add_right' _ ((P i).gradient_measurable.enorm.pow_const _).aemeasurable,
    ← compactBoxBaseMeasure_apply_of_subset S u Du hA hAS,
    ← PressureGradientPatch.densityMeasure_apply_of_subset (P i) hA hAP,
    compactBoxMeasure, Measure.add_apply, Measure.finsetSum_apply]
  have hsum : (P i).densityMeasure A ≤ ∑ j ∈ t, (P j).densityMeasure A :=
    Finset.single_le_sum (fun j _ ↦ (show (0 : ℝ≥0∞) ≤ (P j).densityMeasure A from zero_le)) hi
  exact add_le_add le_rfl hsum

/-- The complete measure is finite for actual suitable data on a compact interior patch. -/
theorem compactBoxMeasure_finite {ι : Type*}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {S : Set ParabolicPoint} (hS : IsCompact S) (hSsub : S ⊆ CKN.spaceTimeSet Ω I)
    (P : ι → PressureGradientPatch p) (t : Finset ι) :
    IsFiniteMeasure (compactBoxMeasure S u Du P t) := by
  let := compactBoxBaseMeasure_finite hsol hS hSsub
  constructor
  rw [compactBoxMeasure, Measure.add_apply, Measure.finsetSum_apply]
  exact ENNReal.add_lt_top.2 ⟨measure_lt_top _ _,
    ENNReal.sum_lt_top.2 (fun _ _ ↦ measure_lt_top _ _)⟩

/-- An actual patch differentiates the supplied pressure on every smaller contained ball. -/
theorem PressureGradientPatch.weak_on_contained_ball
    {p : ParabolicPoint → ℝ} (P : PressureGradientPatch p)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) (hball : Metric.ball z r ⊆ P.carrier) :
    ∀ᵐ s ∂volume.restrict (Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)), ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ P.gradient (x, s) i) (vec3Ball z.1 r) volume ∧
      CKN.HasWeakPartialDerivOn (vec3Ball z.1 r) i
        (fun x ↦ p (x, s)) (fun x ↦ P.gradient (x, s) i) := by
  have hnon : (Metric.ball z r).Nonempty := ⟨z, Metric.mem_ball_self hr⟩
  rw [carrier, metricBall_eq_parabolicBall, metricBall_eq_parabolicBall] at hball
  rw [metricBall_eq_parabolicBall] at hnon
  obtain ⟨hspace, htime⟩ := Set.prod_subset_prod_iff' hnon |>.mp hball
  filter_upwards [ae_restrict_of_ae_restrict_of_subset htime P.gradient_weak] with s hs i
  exact ⟨(hs i).1.mono_set hspace, (hs i).2.restrict (isOpen_vec3Ball _ _) hspace⟩

/-- Compact actual solution data give a finite measure and a uniform radius: every ball
centered in the compact set and below that radius uses one genuine pressure gradient,
whose three-term charge is dominated by the same finite measure. -/
theorem exists_suitable_compact_box_measure
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    ∃ (S : Set ParabolicPoint) (P : K → PressureGradientPatch p) (t : Finset K) (R : ℝ),
      IsCompact S ∧ K ⊆ interior S ∧ S ⊆ CKN.spaceTimeSet Ω I ∧ 0 < R ∧
      IsFiniteMeasure (compactBoxMeasure S u Du P t) ∧
      ∀ z ∈ K, ∃ i ∈ t, ∀ r : ℝ, 0 < r → r ≤ R →
        Metric.ball z r ⊆ S ∧ Metric.ball z r ⊆ (P i).carrier ∧
        (∫⁻ w in Metric.ball z r,
          (‖Du w‖ₑ ^ (2 : ℕ) + ‖u w‖ₑ ^ (10 / 3 : ℝ)) +
            ‖(P i).gradient w‖ₑ ^ (5 / 4 : ℝ)) ≤ compactBoxMeasure S u Du P t (Metric.ball z r) ∧
        ∀ᵐ s ∂volume.restrict (Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)), ∀ k : Fin 3,
          LocallyIntegrableOn (fun x ↦ (P i).gradient (x, s) k) (vec3Ball z.1 r) volume ∧
          CKN.HasWeakPartialDerivOn (vec3Ball z.1 r) k
            (fun x ↦ p (x, s)) (fun x ↦ (P i).gradient (x, s) k) := by
  classical
  obtain ⟨S, hS, hKS, hSdom, -⟩ := exists_suitable_compact_gradient_patch hsol hK hKsub
  obtain ⟨P, t, -, hcover⟩ := exists_finite_suitable_pressure_gradient_cover hsol hK hKsub
  let U : t → Set ParabolicPoint := fun i ↦ (P i.1).carrier ∩ interior S
  have hU : ∀ i, IsOpen (U i) := fun _ ↦ Metric.isOpen_ball.inter isOpen_interior
  have hKU : K ⊆ ⋃ i : t, U i := by
    intro z hz
    obtain ⟨i, hit, hi⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion.mpr ⟨⟨i, hit⟩, hi, hKS hz⟩
  obtain ⟨R, hR, hballs⟩ := lebesgue_number_lemma_of_metric hK hU hKU
  refine ⟨S, P, t, R, hS, hKS, hSdom, hR, compactBoxMeasure_finite hsol hS hSdom P t, ?_⟩
  intro z hz
  obtain ⟨i, hi⟩ := hballs z hz
  refine ⟨i.1, i.2, fun r hr hrR ↦ ?_⟩
  have hb := (Metric.ball_subset_ball hrR).trans hi
  have hbP : Metric.ball z r ⊆ (P i.1).carrier := fun w hw ↦ (hb hw).1
  have hbS : Metric.ball z r ⊆ S := fun w hw ↦ interior_subset (hb hw).2
  exact ⟨hbS, hbP, compactBoxMeasure_charge_le S u Du P t i.2 measurableSet_ball hbS hbP,
    PressureGradientPatch.weak_on_contained_ball (P i.1) hr hbP⟩

end FluidSingularSets
