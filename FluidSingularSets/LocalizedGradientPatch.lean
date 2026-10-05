module

public import FluidSingularSets.CompactCharge
public import FluidSingularSets.ConcreteTraceAE
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# A genuine compact interior patch for the gradient trace

A compact subset of the suitable solution's open carrier has a compact interior
neighborhood still contained in that carrier. The actual gradient is measurable and
has finite dissipation there. Zero extension gives a globally measurable-in-the-almost-
everywhere-sense field, preserving every contained mixed mass and dissipation integral.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal Topology

noncomputable section

namespace FluidSingularSets

/-- Sufficiently small cells containing an interior point stay inside its patch,
uniformly over all sixteen adjacent grids. -/
theorem exists_small_containing_cells_subset_of_mem_interior
    {S : Set ParabolicPoint} {z : ParabolicPoint} (hz : z ∈ interior S) :
    ∃ R : ℝ, 0 < R ∧ ∀ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (r : ℝ),
      0 < r → r ≤ R → dyadicScale Q.scale < r / 16 →
        z ∈ shiftedParabolicDyadicCell g Q → shiftedParabolicDyadicCell g Q ⊆ S := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  refine ⟨R, hR, fun g Q r hr hrR hside hzQ ↦ ?_⟩
  have hsmall : 4 * dyadicScale Q.scale < R := by nlinarith
  exact ((shiftedParabolicDyadicCell_subset_ball g Q hzQ).trans
    (Metric.ball_subset_ball hsmall.le)).trans (hball.trans interior_subset)

/-- A zero extension preserves every mixed activity on a contained cell. -/
theorem dyadicMixedGradientActivity_indicator_eq_on_cell
    {E : Type*} [NormedAddCommGroup E] (D : ParabolicPoint → E)
    (S : Set ParabolicPoint) (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (hQ : shiftedParabolicDyadicCell g Q ⊆ S) :
    dyadicMixedGradientActivity g (S.indicator D) Q = dyadicMixedGradientActivity g D Q :=
  dyadicMixedGradientActivity_congr_on_cell g Q
    (fun _z hz ↦ Set.indicator_of_mem (hQ hz) D)

/-- A zero extension preserves dissipation on every contained measurable set. -/
theorem gradient_dissipation_indicator_eq_on_subset
    {E : Type*} [NormedAddCommGroup E] (D : ParabolicPoint → E)
    (S : Set ParabolicPoint) {A : Set ParabolicPoint}
    (hA : MeasurableSet A) (hAS : A ⊆ S) :
    (∫⁻ z in A, ‖S.indicator D z‖ₑ ^ (2 : ℕ)) =
      ∫⁻ z in A, ‖D z‖ₑ ^ (2 : ℕ) := by
  apply setLIntegral_congr_fun hA
  intro z hz
  dsimp only
  rw [Set.indicator_of_mem (hAS hz) D]

/-- Zero extension turns the patch dissipation into a finite global integral. -/
theorem gradient_dissipation_indicator_integral
    {E : Type*} [NormedAddCommGroup E] (D : ParabolicPoint → E)
    {S : Set ParabolicPoint} (hS : MeasurableSet S) :
    (∫⁻ z, ‖S.indicator D z‖ₑ ^ (2 : ℕ)) = ∫⁻ z in S, ‖D z‖ₑ ^ (2 : ℕ) := by
  have hpoint : (fun z ↦ ‖S.indicator D z‖ₑ ^ (2 : ℕ)) =
      S.indicator (fun z ↦ ‖D z‖ₑ ^ (2 : ℕ)) := by
    funext z
    by_cases hz : z ∈ S <;> simp [hz]
  rw [hpoint, lintegral_indicator hS]

/-- The actual suitable solution supplies a compact patch around an arbitrary compact
interior set, a finite global zero-extended gradient, and exact contained-cell identities. -/
theorem exists_suitable_compact_gradient_patch
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    ∃ S : Set ParabolicPoint, IsCompact S ∧ K ⊆ interior S ∧ S ⊆ CKN.spaceTimeSet Ω I ∧
      AEStronglyMeasurable Du (volume.restrict S) ∧
      (∫⁻ z in S, ‖Du z‖ₑ ^ (2 : ℕ)) < ⊤ ∧
      AEStronglyMeasurable (S.indicator Du) volume ∧
      (∫⁻ z, ‖S.indicator Du z‖ₑ ^ (2 : ℕ)) < ⊤ ∧
      (∀ g Q, shiftedParabolicDyadicCell g Q ⊆ S →
        dyadicMixedGradientActivity g (S.indicator Du) Q =
          dyadicMixedGradientActivity g Du Q) ∧
      (∀ A : Set ParabolicPoint, MeasurableSet A → A ⊆ S →
        (∫⁻ z in A, ‖S.indicator Du z‖ₑ ^ (2 : ℕ)) =
          ∫⁻ z in A, ‖Du z‖ₑ ^ (2 : ℕ)) ∧
      (∀ z ∈ K, ∃ R : ℝ, 0 < R ∧
        ∀ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (r : ℝ),
          0 < r → r ≤ R → dyadicScale Q.scale < r / 16 →
            z ∈ shiftedParabolicDyadicCell g Q → shiftedParabolicDyadicCell g Q ⊆ S) := by
  let : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isOpenEmbedding.locallyCompactSpace
  have hdom : IsOpen (CKN.spaceTimeSet Ω I) := isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1
  obtain ⟨S, hS, hKS, hSdom⟩ := exists_compact_between hK hdom hKsub
  have hSmeas := hS.isClosed.measurableSet
  have hDu := CKN.gradient_memLp_two_on_compact_of_data hsol.toData hS hSdom
  have hfinite := (compact_velocity_pressure_gradient_charges hsol hS hSdom).2.2
  have hzero := (aestronglyMeasurable_indicator_iff hSmeas).2 hDu.aestronglyMeasurable
  refine ⟨S, hS, hKS, hSdom, hDu.aestronglyMeasurable, hfinite, hzero, ?_, ?_, ?_, ?_⟩
  · rw [gradient_dissipation_indicator_integral Du hSmeas]
    exact hfinite
  · intro g Q hQ
    exact dyadicMixedGradientActivity_indicator_eq_on_cell Du S g Q hQ
  · intro A hA hAS
    exact gradient_dissipation_indicator_eq_on_subset Du S hA hAS
  · intro z hz
    exact exists_small_containing_cells_subset_of_mem_interior (hKS hz)

end FluidSingularSets
