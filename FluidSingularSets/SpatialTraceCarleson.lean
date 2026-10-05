module

public import FluidSingularSets.SpatialTraceCoefficients
public import FluidSingularSets.ShiftedSpatialRepresentation
public import FluidSingularSets.ShiftedCarleson

/-!
# Carleson bounds for the concrete slice coefficients

Unique cube representation identifies every contained cube with a genuine spatial
descendant. The actual finite-generation mass bound therefore applies to arbitrary
finite cube families, as required by the spatial maximal-function embedding.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- The concrete coefficient as a function of its spatial cube. -/
def spatialTraceSetCoefficient (μ : Measure ParabolicPoint) (F : ℤ → ℝ)
    (g : ParabolicGridShift) (A : Set Vec3) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (spatialTraceCoefficient μ F g (shiftedSpatialRepresentation g A).scale
    (shiftedSpatialRepresentation g A).corner t)

/-- Every concrete coefficient is measurable in time. -/
theorem measurable_spatialTraceSetCoefficient (μ : Measure ParabolicPoint) (F : ℤ → ℝ)
    (g : ParabolicGridShift) (A : Set Vec3) :
    Measurable (spatialTraceSetCoefficient μ F g A) :=
  ENNReal.measurable_ofReal.comp (measurable_spatialTraceCoefficient μ F g _ _)

/-- Every contained grid cube gives an actual descendant of the containing cube. -/
def spatialTraceDescendantRepresentation {g : ParabolicGridShift} {A B : Set Vec3}
    (hA : A ∈ shiftedSpatialGrid g) (hB : B ∈ shiftedSpatialGrid g) (hsub : B ⊆ A) :
    SpatialTraceDescendant g (shiftedSpatialRepresentation g A).scale
      (shiftedSpatialRepresentation g A).corner := by
  let Q := shiftedSpatialRepresentation g B
  let R := shiftedSpatialRepresentation g A
  have hscale : R.scale ≤ Q.scale := by
    apply shiftedDyadicCube_scale_le_of_subset g Q R
    simpa only [Q, R, shiftedSpatialRepresentation_cube hA,
      shiftedSpatialRepresentation_cube hB] using hsub
  let k := (Q.scale - R.scale).toNat
  have hk : R.scale + (k : ℤ) = Q.scale := by
    dsimp [k]
    rw [Int.toNat_of_nonneg (sub_nonneg.2 hscale)]
    omega
  refine ⟨k, Q.corner, ?_⟩
  apply (mem_shiftedSpatialDescendants_iff_subset g R.scale R.corner k Q.corner).2
  rw [hk]
  simpa only [Q, R, shiftedSpatialRepresentation_cube hA,
    shiftedSpatialRepresentation_cube hB] using hsub

/-- The descendant representation retains the fine cube's level. -/
theorem spatialTraceDescendantRepresentation_scale {g : ParabolicGridShift} {A B : Set Vec3}
    (hA : A ∈ shiftedSpatialGrid g) (hB : B ∈ shiftedSpatialGrid g) (hsub : B ⊆ A) :
    (shiftedSpatialRepresentation g A).scale +
      (spatialTraceDescendantRepresentation hA hB hsub).1 =
      (shiftedSpatialRepresentation g B).scale := by
  have hscale := shiftedDyadicCube_scale_le_of_subset g
    (shiftedSpatialRepresentation g B) (shiftedSpatialRepresentation g A)
    (by simpa only [shiftedSpatialRepresentation_cube hA,
      shiftedSpatialRepresentation_cube hB] using hsub)
  dsimp [spatialTraceDescendantRepresentation]
  rw [Int.toNat_of_nonneg (sub_nonneg.2 hscale)]
  omega

/-- The descendant representation retains the fine cube's corner. -/
theorem spatialTraceDescendantRepresentation_corner {g : ParabolicGridShift} {A B : Set Vec3}
    (hA : A ∈ shiftedSpatialGrid g) (hB : B ∈ shiftedSpatialGrid g) (hsub : B ⊆ A) :
    (spatialTraceDescendantRepresentation hA hB hsub).2.val =
      (shiftedSpatialRepresentation g B).corner := rfl

/-- The actual descendant bound supplies the finite-family Carleson hypothesis. -/
theorem finite_spatialTraceSetCoefficient_carleson (μ : Measure ParabolicPoint)
    [IsFiniteMeasure μ] (F : ℤ → ℝ) (g : ParabolicGridShift) {A : Set Vec3}
    (hA : A ∈ shiftedSpatialGrid g) (P : Finset (Set Vec3))
    (hP : ∀ B ∈ P, B ∈ shiftedSpatialGrid g) (t : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : 0 < F (shiftedSpatialRepresentation g A).scale)
    (hmono : ∀ k : ℕ, F (shiftedSpatialRepresentation g A).scale ≤
      F ((shiftedSpatialRepresentation g A).scale + k))
    (hgrowth : (μ (shiftedTraceCell g (shiftedSpatialRepresentation g A).scale
      (shiftedSpatialRepresentation g A).corner t)).toReal ≤
        M * dyadicScale (shiftedSpatialRepresentation g A).scale *
          F (shiftedSpatialRepresentation g A).scale) :
    (∑ B ∈ P.filter (fun B ↦ B ⊆ A), spatialTraceSetCoefficient μ F g B t) ≤
      ENNReal.ofReal (2 * Real.sqrt M) * volume A := by
  classical
  let R := shiftedSpatialRepresentation g A
  let S := P.filter (fun B ↦ B ⊆ A)
  let ι : ↥S → SpatialTraceDescendant g R.scale R.corner := fun B ↦
    spatialTraceDescendantRepresentation hA (hP B (mem_filter.1 B.property).1)
      (mem_filter.1 B.property).2
  have hi_scale (B : ↥S) : R.scale + (ι B).1 =
      (shiftedSpatialRepresentation g B).scale :=
    spatialTraceDescendantRepresentation_scale hA (hP B (mem_filter.1 B.property).1)
      (mem_filter.1 B.property).2
  have hi_corner (B : ↥S) : (ι B).2.val =
      (shiftedSpatialRepresentation g B).corner := rfl
  have hinj : Function.Injective ι := by
    intro B D hBD
    have hn : (shiftedSpatialRepresentation g B).scale =
        (shiftedSpatialRepresentation g D).scale := by
      rw [← hi_scale B, ← hi_scale D, hBD]
    have ha : (shiftedSpatialRepresentation g B).corner =
        (shiftedSpatialRepresentation g D).corner := by
      rw [← hi_corner B, ← hi_corner D, hBD]
    apply Subtype.ext
    rw [← shiftedSpatialRepresentation_cube (hP B (mem_filter.1 B.property).1),
      ← shiftedSpatialRepresentation_cube (hP D (mem_filter.1 D.property).1), hn, ha]
  let c : SpatialTraceDescendant g R.scale R.corner → ℝ≥0∞ := fun q ↦
    ENNReal.ofReal (spatialTraceCoefficient μ F g (R.scale + q.1) q.2 t)
  have hc (B : ↥S) : c (ι B) = spatialTraceSetCoefficient μ F g B t := by
    dsimp only [c, spatialTraceSetCoefficient]
    rw [hi_scale B, hi_corner B]
  calc
    _ = ∑' B : ↥S, c (ι B) := by
      calc
        _ = ∑' B : ↥S, spatialTraceSetCoefficient μ F g B t :=
          (Finset.tsum_subtype S (fun B ↦ spatialTraceSetCoefficient μ F g B t)).symm
        _ = _ := tsum_congr (fun B ↦ (hc B).symm)
    _ ≤ ∑' q, c q := ENNReal.tsum_comp_le_tsum_of_injective hinj c
    _ ≤ ENNReal.ofReal (2 * Real.sqrt M * dyadicScale R.scale ^ 3) :=
      ennreal_spatialTraceCoefficient_descendant_sum_le μ F g R.scale R.corner t
        hM hF hmono hgrowth
    _ = _ := by
      rw [← shiftedSpatialRepresentation_cube hA, volume_shiftedDyadicCube,
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Real.sqrt_nonneg M)),
        ENNReal.ofReal_pow (dyadicScale_pos _).le]

/-- Actual cell growth derives every descendant hypothesis of the integrated embedding.
Only the input density's finite product-space mass remains as an analytic hypothesis. -/
theorem integrated_spatialTraceSetCoefficient_embedding
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (F : ℤ → ℝ)
    (g : ParabolicGridShift) (τ : Measure ℝ) (𝒟 : Set (Set Vec3))
    (f : ℝ → Vec3 → ℝ≥0∞) {M p : ℝ} (hM : 0 ≤ M) (hp : 1 < p)
    (hgrid : ∀ A ∈ 𝒟, A ∈ shiftedSpatialGrid g)
    (hF : ∀ A ∈ 𝒟, 0 < F (shiftedSpatialRepresentation g A).scale)
    (hmono : ∀ A ∈ 𝒟, ∀ k : ℕ, F (shiftedSpatialRepresentation g A).scale ≤
      F ((shiftedSpatialRepresentation g A).scale + k))
    (hgrowth : ∀ t : ℝ, ∀ A ∈ 𝒟,
      (μ (shiftedTraceCell g (shiftedSpatialRepresentation g A).scale
        (shiftedSpatialRepresentation g A).corner t)).toReal ≤
          M * dyadicScale (shiftedSpatialRepresentation g A).scale *
            F (shiftedSpatialRepresentation g A).scale)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume) < ⊤) :
    (∑' A : 𝒟, ∫⁻ t, spatialTraceSetCoefficient μ F g A t *
      (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≤
      ENNReal.ofReal (2 * Real.sqrt M) * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        ∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume := by
  apply integrated_shifted_dyadic_carleson_embedding_prod g τ 𝒟
    (spatialTraceSetCoefficient μ F g) f ENNReal.ofReal_ne_top hp
  · intro A hA
    exact hgrid A hA
  · filter_upwards [] with t
    intro A hA P hP
    exact finite_spatialTraceSetCoefficient_carleson μ F g (hgrid A hA) P
      (fun B hB ↦ hgrid B (hP B hB)) t hM (hF A hA) (hmono A hA) (hgrowth t A hA)
  · intro A _hA
    exact measurable_spatialTraceSetCoefficient μ F g A
  · exact hf
  · exact hfp

end FluidSingularSets
