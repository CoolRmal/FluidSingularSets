module

public import FluidSingularSets.CountableCarleson
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Time integration of the spatial Carleson embedding

The spatial descendant coefficient bounds imply an embedding on almost every time slice.
Tonelli's theorem then bounds the complete integrated coefficient series.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- A family of cubes in the ordinary dyadic grid is countable. -/
theorem countable_dyadic_family (𝒟 : Set (Set Vec3))
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner) :
    𝒟.Countable := by
  apply (Set.countable_range (fun q : ℤ × (Fin 3 → ℤ) ↦ dyadicCube q.1 q.2)).mono
  intro A hA
  obtain ⟨Q, rfl⟩ := hdyadic A hA
  exact ⟨(Q.scale, Q.corner), rfl⟩

/-- Integrating the actual slice-wise dyadic embedding bounds the full coefficient series.
The time measure can be Lebesgue measure restricted to the time interval of a root. -/
theorem integrated_dyadic_carleson_embedding (τ : Measure ℝ) (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ → ℝ≥0∞) (f : ℝ → Vec3 → ℝ≥0∞)
    {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ᵐ t ∂τ, ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B t) ≤ C * volume A)
    (hf : ∀ᵐ t ∂τ, Measurable (f t))
    (hfp : ∀ᵐ t ∂τ, (∫⁻ x, f t x ^ p ∂volume) < ⊤)
    (hmeas : ∀ A : 𝒟, AEMeasurable
      (fun t ↦ α A t * (⨍⁻ x in A, f t x ∂volume) ^ p) τ) :
    (∑' A : 𝒟, ∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≤
      C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        ∫⁻ t, ∫⁻ x, f t x ^ p ∂volume ∂τ := by
  let : Countable 𝒟 := (countable_dyadic_family 𝒟 hdyadic).to_subtype
  rw [← lintegral_tsum hmeas]
  calc
    _ ≤ ∫⁻ t, C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        (∫⁻ x, f t x ^ p ∂volume) ∂τ := by
      apply lintegral_mono_ae
      filter_upwards [hcar, hf, hfp] with t htcar htf htfp
      exact dyadic_carleson_embedding 𝒟 (fun A ↦ α A t) (f t) hC hp
        hdyadic htcar htf htfp
    _ = _ := by
      apply lintegral_const_mul'
      rw [mul_assoc C]
      exact ENNReal.mul_ne_top hC (carleson_maximal_constant_ne_top hp)

/-- Joint measurability and a finite product-space `Lp` integral supply all slice hypotheses
for the integrated Carleson bound. The coefficient measurability is imposed before averaging. -/
theorem integrated_dyadic_carleson_embedding_prod (τ : Measure ℝ) (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ → ℝ≥0∞) (f : ℝ → Vec3 → ℝ≥0∞)
    {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ᵐ t ∂τ, ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B t) ≤ C * volume A)
    (hα : ∀ A ∈ 𝒟, Measurable (α A))
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume) < ⊤) :
    (∑' A : 𝒟, ∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≤
      C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        ∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume := by
  have hpow : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2 ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hf
  have hI : Measurable (fun t ↦ ∫⁻ x, f t x ^ p ∂volume) :=
    hpow.lintegral_prod_right'
  have hprod := lintegral_prod (μ := τ) (ν := volume)
    (fun z : ℝ × Vec3 ↦ f z.1 z.2 ^ p) hpow.aemeasurable
  have hIfinite : (∫⁻ t, ∫⁻ x, f t x ^ p ∂volume ∂τ) ≠ ⊤ := by
    rw [← hprod]
    exact hfp.ne
  have hslice : ∀ᵐ t ∂τ, Measurable (f t) := by
    filter_upwards [] with t
    exact hf.comp (measurable_const.prodMk measurable_id)
  have hsliceFinite : ∀ᵐ t ∂τ, (∫⁻ x, f t x ^ p ∂volume) < ⊤ :=
    ae_lt_top' hI.aemeasurable hIfinite
  have hweighted (A : 𝒟) : AEMeasurable
      (fun t ↦ α A t * (⨍⁻ x in A, f t x ∂volume) ^ p) τ := by
    have havg : Measurable (fun t ↦ ⨍⁻ x in A, f t x ∂volume) := by
      simp_rw [setLAverage_eq]
      exact (hf.lintegral_prod_right' (ν := volume.restrict A)).div measurable_const
    exact ((hα A A.property).mul
      (ENNReal.continuous_rpow_const.measurable.comp havg)).aemeasurable
  have hbound := integrated_dyadic_carleson_embedding τ 𝒟 α f hC hp hdyadic hcar
    hslice hsliceFinite hweighted
  rwa [← hprod] at hbound

/-- The integrated coefficients form a summable real series when the product-space `Lp`
mass is finite. The bound retains the explicit constant from the spatial embedding. -/
theorem integrated_dyadic_carleson_embedding_prod_summable (τ : Measure ℝ)
    (𝒟 : Set (Set Vec3)) (α : Set Vec3 → ℝ → ℝ≥0∞) (f : ℝ → Vec3 → ℝ≥0∞)
    {C : ℝ≥0∞} {p : ℝ} (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ᵐ t ∂τ, ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B t) ≤ C * volume A)
    (hα : ∀ A ∈ 𝒟, Measurable (α A))
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume) < ⊤) :
    Summable (fun A : 𝒟 ↦
      (∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ).toReal) ∧
      (∑' A : 𝒟, (∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ).toReal) ≤
        (C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
          ∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume).toReal := by
  have hbound := integrated_dyadic_carleson_embedding_prod τ 𝒟 α f hC hp
    hdyadic hcar hα hf hfp
  have hB : C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
      (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume) ≠ ⊤ := by
    rw [mul_assoc C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hC (carleson_maximal_constant_ne_top hp)) hfp.ne
  have hsum : (∑' A : 𝒟, ∫⁻ t,
      α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≠ ⊤ :=
    ne_top_of_le_ne_top hB hbound
  have hterm (A : 𝒟) : (∫⁻ t,
      α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum
      (ENNReal.le_tsum (f := fun B : 𝒟 ↦
        ∫⁻ t, α B t * (⨍⁻ x in B, f t x ∂volume) ^ p ∂τ) A)
  refine ⟨ENNReal.summable_toReal hsum, ?_⟩
  rw [← ENNReal.tsum_toReal_eq hterm]
  exact (ENNReal.toReal_le_toReal hsum hB).2 hbound

end FluidSingularSets
