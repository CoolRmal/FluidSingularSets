module

public import FluidSingularSets.CarlesonEmbedding

/-!
# Carleson embedding for the full dyadic family

The finite embedding passes to the entire family by taking the supremum over finite
subfamilies. Its explicit constant is finite for every exponent above one, so the associated
real series is summable. The statements also apply to families not assumed countable.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- The maximal-function constant used by the Carleson embedding is finite for `p > 1`. -/
theorem carleson_maximal_constant_ne_top {p : ℝ} (hp : 1 < p) :
    (64 : ℝ≥0∞) ^ p * maximalStrongConstant p ≠ ⊤ := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hpow (a : ℝ≥0∞) (ha : a ≠ ⊤) : a ^ p ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hp0 ha).ne
  apply ENNReal.mul_ne_top (hpow 64 (by norm_num))
  dsimp [maximalStrongConstant]
  apply ENNReal.div_ne_top
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (hpow 2 (by norm_num)) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_zero_iff.2 (sub_pos.2 hp)

/-- Actual dyadic descendant-Carleson bounds imply the full extended nonnegative `Lp`
embedding. No embedding or maximal-function estimate is included in the hypotheses. -/
theorem dyadic_carleson_embedding (𝒟 : Set (Set Vec3)) (α : Set Vec3 → ℝ≥0∞)
    (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} {p : ℝ} (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ p ∂volume < ⊤) :
    (∑' A : 𝒟, α A * (⨍⁻ x in A, f x ∂volume) ^ p) ≤
      C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p * ∫⁻ x, f x ^ p ∂volume := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro P
  let Q : Finset (Set Vec3) := P.image Subtype.val
  have hQD : ∀ A ∈ Q, A ∈ 𝒟 := by
    intro A hA
    obtain ⟨B, _, rfl⟩ := mem_image.1 hA
    exact B.property
  have hbound := finite_dyadic_carleson_embedding Q α f hC hp
    (fun A hA ↦ hdyadic A (hQD A hA))
    (fun A hA ↦ hcar A (hQD A hA) Q hQD) hf hfp
  have hsum : (∑ A ∈ Q, α A * (⨍⁻ x in A, f x ∂volume) ^ p) =
      ∑ A ∈ P, α A * (⨍⁻ x in A, f x ∂volume) ^ p := by
    exact sum_image (fun _ _ _ _ h ↦ Subtype.ext h)
  rwa [hsum] at hbound

/-- The full weighted dyadic `Lp` series is a summable real series, with the same explicit
bound as the extended nonnegative embedding. -/
theorem dyadic_carleson_embedding_summable (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ≥0∞) (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ p ∂volume < ⊤) :
    Summable (fun A : 𝒟 ↦ (α A * (⨍⁻ x in A, f x ∂volume) ^ p).toReal) ∧
      (∑' A : 𝒟, (α A * (⨍⁻ x in A, f x ∂volume) ^ p).toReal) ≤
        (C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
          ∫⁻ x, f x ^ p ∂volume).toReal := by
  have hbound := dyadic_carleson_embedding 𝒟 α f hC hp hdyadic hcar hf hfp
  have hB : C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
      (∫⁻ x, f x ^ p ∂volume) ≠ ⊤ := by
    rw [mul_assoc C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hC (carleson_maximal_constant_ne_top hp)) hfp.ne
  have hsum : (∑' A : 𝒟, α A * (⨍⁻ x in A, f x ∂volume) ^ p) ≠ ⊤ :=
    ne_top_of_le_ne_top hB hbound
  have hterm (A : 𝒟) : α A * (⨍⁻ x in A, f x ∂volume) ^ p ≠ ⊤ :=
    ne_top_of_le_ne_top hsum
      (ENNReal.le_tsum (f := fun B : 𝒟 ↦ α B * (⨍⁻ x in B, f x ∂volume) ^ p) A)
  refine ⟨ENNReal.summable_toReal hsum, ?_⟩
  rw [← ENNReal.tsum_toReal_eq hterm]
  exact (ENNReal.toReal_le_toReal hsum hB).2 hbound

/-- The full-family embedding at the dissipation-trace exponent `7/6`. -/
theorem dyadic_carleson_embedding_summable_seven_sixths (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ≥0∞) (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ (7 / 6 : ℝ) ∂volume < ⊤) :
    Summable (fun A : 𝒟 ↦ (α A * (⨍⁻ x in A, f x ∂volume) ^ (7 / 6 : ℝ)).toReal) ∧
      (∑' A : 𝒟, (α A * (⨍⁻ x in A, f x ∂volume) ^ (7 / 6 : ℝ)).toReal) ≤
        (C * (64 : ℝ≥0∞) ^ (7 / 6 : ℝ) * maximalStrongConstant (7 / 6) *
          ∫⁻ x, f x ^ (7 / 6 : ℝ) ∂volume).toReal :=
  dyadic_carleson_embedding_summable 𝒟 α f hC (by norm_num) hdyadic hcar hf hfp

end FluidSingularSets
