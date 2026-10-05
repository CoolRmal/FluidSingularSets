module

public import FluidSingularSets.MassRatioStopping

/-!
# The trace estimate with zero masses allowed

Real division by zero gives the intended zero-cost convention on cells with zero
dissipation. Removing these cells from finite subfamilies lets the stopping argument
apply without positivity assumptions on individual cell masses or on either total mass.
-/

@[expose] public section

open MeasureTheory Set Finset

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- The finite trace estimate includes zero total mass and zero-dissipation cells. -/
theorem finite_laminar_mass_ratio_trace_allow_zero {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P : Finset (Set X)) (β : Set X → ℝ) {C : ℝ}
    (hmeas : ∀ A ∈ P, MeasurableSet A)
    (hlam : ∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hβ : ∀ A ∈ P, 0 ≤ β A) (hC : 0 ≤ C)
    (hcar : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), β B) ≤ C * (ν A).toReal) :
    (∑ A ∈ P, β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) ≤
      2 * C * Real.sqrt ((μ univ).toReal * (ν univ).toReal) := by
  classical
  by_cases hμ : μ univ = 0
  · have hμA : ∀ A : Set X, μ A = 0 := fun A ↦
      le_antisymm ((measure_mono (subset_univ A)).trans_eq hμ) bot_le
    simp only [hμA, ENNReal.toReal_zero, zero_div, Real.sqrt_zero, mul_zero,
      sum_const_zero, zero_mul, le_refl]
  by_cases hν : ν univ = 0
  · have hνA : ∀ A : Set X, ν A = 0 := fun A ↦
      le_antisymm ((measure_mono (subset_univ A)).trans_eq hν) bot_le
    simp only [hνA, ENNReal.toReal_zero, div_zero, Real.sqrt_zero, mul_zero,
      sum_const_zero, le_refl]
  let Q := P.filter (fun A ↦ ν A ≠ 0)
  have hQP : Q ⊆ P := filter_subset _ _
  have hcarQ : ∀ A ∈ Q, (∑ B ∈ Q.filter (fun B ↦ B ⊆ A), β B) ≤
      C * (ν A).toReal := by
    intro A hA
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hQP) ?_).trans
      (hcar A (hQP hA))
    intro B hB _
    exact hβ B ((filter_subset _ _) hB)
  have htrace := finite_laminar_mass_ratio_trace μ ν Q β
    (fun A hA ↦ hmeas A (hQP hA))
    (fun A hA B hB ↦ hlam A (hQP hA) B (hQP hB))
    (fun A hA ↦ hβ A (hQP hA)) hC hμ hν
    (fun A hA ↦ (mem_filter.1 hA).2) hcarQ
  have heq : (∑ A ∈ Q, β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) =
      ∑ A ∈ P, β A * Real.sqrt ((μ A).toReal / (ν A).toReal) := by
    apply sum_subset hQP
    intro A hA hnot
    have hzero : ν A = 0 := by
      by_contra hne
      exact hnot (mem_filter.2 ⟨hA, hne⟩)
    simp only [hzero, ENNReal.toReal_zero, div_zero, Real.sqrt_zero, mul_zero]
  rwa [heq] at htrace

/-- The complete trace series is summable under descendant Carleson bounds, using zero cost
on every cell of zero dissipation mass. -/
theorem laminar_mass_ratio_trace_summable_allow_zero {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (𝒟 : Set (Set X)) (β : Set X → ℝ) {C : ℝ}
    (hmeas : ∀ A ∈ 𝒟, MeasurableSet A)
    (hlam : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hβ : ∀ A ∈ 𝒟, 0 ≤ β A) (hC : 0 ≤ C)
    (hcar : ∀ A ∈ 𝒟, ∀ P : Finset (Set X), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), β B) ≤ C * (ν A).toReal) :
    Summable (fun A : 𝒟 ↦ β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) ∧
      (∑' A : 𝒟, β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) ≤
        2 * C * Real.sqrt ((μ univ).toReal * (ν univ).toReal) := by
  classical
  have hnonneg : ∀ A : 𝒟, 0 ≤ β A * Real.sqrt ((μ A).toReal / (ν A).toReal) :=
    fun A ↦ mul_nonneg (hβ A A.property) (Real.sqrt_nonneg _)
  have hbound (P : Finset 𝒟) :
      (∑ A ∈ P, β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) ≤
        2 * C * Real.sqrt ((μ univ).toReal * (ν univ).toReal) := by
    let Q : Finset (Set X) := P.image Subtype.val
    have hQD : ∀ A ∈ Q, A ∈ 𝒟 := by
      intro A hA
      obtain ⟨B, _, rfl⟩ := mem_image.1 hA
      exact B.property
    have htrace := finite_laminar_mass_ratio_trace_allow_zero μ ν Q β
      (fun A hA ↦ hmeas A (hQD A hA))
      (fun A hA B hB ↦ hlam A (hQD A hA) B (hQD B hB))
      (fun A hA ↦ hβ A (hQD A hA)) hC (fun A hA ↦ hcar A (hQD A hA) Q hQD)
    have heq : (∑ A ∈ Q, β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) =
        ∑ A ∈ P, β A * Real.sqrt ((μ A).toReal / (ν A).toReal) :=
      sum_image (fun _ _ _ _ h ↦ Subtype.ext h)
    rwa [heq] at htrace
  have hsum := summable_of_sum_le hnonneg hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end FluidSingularSets
