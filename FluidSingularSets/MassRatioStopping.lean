module

public import FluidSingularSets.CarlesonEmbedding
public import FluidSingularSets.TraceLayerCake

/-!
# Stopping at a mass ratio

Maximal cells above a mass-ratio threshold are disjoint. A descendant Carleson estimate
therefore gives the tail bound needed by the square-root layer-cake estimate.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- A structural mass-ratio tail bound for a finite laminar family. The coefficient hypothesis
is only a descendant Carleson bound, with respect to the second measure. -/
theorem finite_laminar_mass_ratio_tail {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (P : Finset (Set X)) (α : Set X → ℝ≥0∞) {C : ℝ≥0∞}
    (hmeas : ∀ A ∈ P, MeasurableSet A)
    (hlam : ∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hcar : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * ν A)
    {s : ℝ} (hs : 0 < s) :
    (∑ A ∈ P.filter (fun A ↦ ENNReal.ofReal s * ν A < μ A), α A) ≤
      C * min (ν univ) (μ univ / ENNReal.ofReal s) := by
  classical
  let S := P.filter (fun A ↦ ENNReal.ofReal s * ν A < μ A)
  let R := S.filter (fun A ↦ Maximal (fun B ↦ B ∈ S) A)
  have hSP : S ⊆ P := filter_subset _ _
  have hRS : R ⊆ S := filter_subset _ _
  have hRP : R ⊆ P := hRS.trans hSP
  have hroots : ∀ A ∈ S, ∃ B ∈ R, A ⊆ B := by
    intro A hA
    obtain ⟨B, hAB, hB⟩ := S.exists_le_maximal hA
    exact ⟨B, mem_filter.2 ⟨hB.1, hB⟩, hAB⟩
  have hdisj : (R : Set (Set X)).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain hAB | hBA | hd := hlam A (hRP hA) B (hRP hB)
    · have heq : A = B := Subset.antisymm hAB ((mem_filter.1 hA).2.2 (hRS hB) hAB)
      exact (hne heq).elim
    · have heq : A = B := Subset.antisymm ((mem_filter.1 hB).2.2 (hRS hA) hBA) hBA
      exact (hne heq).elim
    · exact hd
  have hunion : (⋃ A ∈ S, A) = ⋃ B ∈ R, B := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨B, hB, hAB⟩ := hroots A hA
      exact Set.mem_iUnion₂.2 ⟨B, hB, hAB hxA⟩
    · intro x hx
      obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion₂.2 ⟨B, hRS hB, hxB⟩
  have hmeasure (ρ : Measure X) : ρ (⋃ B ∈ R, B) = ∑ B ∈ R, ρ B := by
    simpa only [id_eq] using
      measure_biUnion_finset hdisj (fun B hB ↦ hmeas B (hRP hB))
  have hratio : ν (⋃ A ∈ S, A) ≤ μ univ / ENNReal.ofReal s := by
    rw [hunion]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_ne_zero_iff.2 hs)) (Or.inl ENNReal.ofReal_ne_top)).2
    rw [hmeasure ν, sum_mul]
    calc
      (∑ B ∈ R, ν B * ENNReal.ofReal s) ≤ ∑ B ∈ R, μ B := by
        apply sum_le_sum
        intro B hB
        simpa only [mul_comm] using (mem_filter.1 (hRS hB)).2.le
      _ = μ (⋃ B ∈ R, B) := (hmeasure μ).symm
      _ ≤ μ univ := measure_mono (subset_univ _)
  have hbound : ν (⋃ A ∈ S, A) ≤ min (ν univ) (μ univ / ENNReal.ofReal s) :=
    le_min (measure_mono (subset_univ _)) hratio
  have hresult := (finite_laminar_carleson_sum_le ν P S α hSP hmeas hlam hcar).trans
    (mul_le_mul_of_nonneg_left hbound bot_le)
  convert hresult using 1
  exact congrArg (fun T : Finset (Set X) ↦ ∑ A ∈ T, α A) (by ext A; simp [S])

/-- The full finite square-root mass-ratio trace estimate, derived from descendant Carleson
bounds rather than a tail-bound hypothesis. -/
theorem finite_laminar_mass_ratio_trace {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P : Finset (Set X)) (β : Set X → ℝ) {C : ℝ}
    (hmeas : ∀ A ∈ P, MeasurableSet A)
    (hlam : ∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hβ : ∀ A ∈ P, 0 ≤ β A) (hC : 0 ≤ C)
    (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0) (hνA : ∀ A ∈ P, ν A ≠ 0)
    (hcar : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), β B) ≤ C * (ν A).toReal) :
    (∑ A ∈ P, β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) ≤
      2 * C * Real.sqrt ((μ univ).toReal * (ν univ).toReal) := by
  classical
  have hcarE : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), ENNReal.ofReal (β B)) ≤
      ENNReal.ofReal C * ν A := by
    intro A hA
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun B hB ↦ hβ B ((filter_subset _ _) hB))]
    have hbound := ENNReal.ofReal_le_ofReal (hcar A hA)
    rwa [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal (measure_ne_top ν A)] at hbound
  apply finite_mass_ratio_trace P β (fun A ↦ (μ A).toReal) (fun A ↦ (ν A).toReal)
    hβ (fun A hA ↦ ENNReal.toReal_pos (hνA A hA) (measure_ne_top ν A)) hC
    (ENNReal.toReal_pos hμ (measure_ne_top μ univ))
    (ENNReal.toReal_pos hν (measure_ne_top ν univ))
  intro s hs
  have hratio (A : Set X) : ENNReal.ofReal s * ν A < μ A ↔
      s * (ν A).toReal < (μ A).toReal := by
    rw [← ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν A))
      (measure_ne_top μ A), ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le]
  have hbound := finite_laminar_mass_ratio_tail μ ν P (fun A ↦ ENNReal.ofReal (β A))
    hmeas hlam hcarE hs
  simp only [sum_filter, hratio] at hbound
  have hright : ENNReal.ofReal
      (C * min (ν univ).toReal ((μ univ).toReal / s)) =
      ENNReal.ofReal C * min (ν univ) (μ univ / ENNReal.ofReal s) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_min, ENNReal.ofReal_div_of_pos hs,
      ENNReal.ofReal_toReal (measure_ne_top μ univ),
      ENNReal.ofReal_toReal (measure_ne_top ν univ)]
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC
    (le_min ENNReal.toReal_nonneg (div_nonneg ENNReal.toReal_nonneg hs.le)))).1
  rw [ENNReal.ofReal_sum_of_nonneg (fun A hA ↦ hβ A ((filter_subset _ _) hA)), hright]
  simpa only [sum_filter] using hbound

/-- The trace series over a possibly infinite laminar family is summable when every finite
descendant coefficient sum satisfies the Carleson estimate. -/
theorem laminar_mass_ratio_trace_summable {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (𝒟 : Set (Set X)) (β : Set X → ℝ) {C : ℝ}
    (hmeas : ∀ A ∈ 𝒟, MeasurableSet A)
    (hlam : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hβ : ∀ A ∈ 𝒟, 0 ≤ β A) (hC : 0 ≤ C)
    (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0) (hνA : ∀ A ∈ 𝒟, ν A ≠ 0)
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
    have htrace := finite_laminar_mass_ratio_trace μ ν Q β
      (fun A hA ↦ hmeas A (hQD A hA))
      (fun A hA B hB ↦ hlam A (hQD A hA) B (hQD B hB))
      (fun A hA ↦ hβ A (hQD A hA)) hC hμ hν
      (fun A hA ↦ hνA A (hQD A hA)) (fun A hA ↦ hcar A (hQD A hA) Q hQD)
    have hsum : (∑ A ∈ Q, β A * Real.sqrt ((μ A).toReal / (ν A).toReal)) =
        ∑ A ∈ P, β A * Real.sqrt ((μ A).toReal / (ν A).toReal) := by
      exact sum_image (fun _ _ _ _ h ↦ Subtype.ext h)
    rwa [hsum] at htrace
  have hsum := summable_of_sum_le hnonneg hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end FluidSingularSets
