module

public import FluidSingularSets.SpatialTraceCarleson
public import FluidSingularSets.ShiftedCellRepresentation
public import FluidSingularSets.FrostmanCellGrowth

/-!
# The concrete parabolic trace Carleson estimate

At each time, distinct active parabolic cells have distinct spatial cubes. The spatial
Carleson embedding therefore controls the finite sum of their integrated coefficients.
The time measure and the spatial density can both be restricted to a root cell.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- A cell's spatial projection, with its actual level and corner. -/
def parabolicSpatialCube (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) : Set Vec3 :=
  shiftedDyadicCube g Q.scale Q.corner

/-- At a fixed time, the spatial projection is injective on the active cell family. -/
theorem parabolicSpatialCube_injOn_active (g : ParabolicGridShift) (t : ℝ) :
    Set.InjOn (parabolicSpatialCube g)
      {Q | t ∈ shiftedParabolicDyadicTime g Q.scale Q.timeCorner} := by
  intro Q hQ R hR hQR
  have hi : (⟨Q.scale, Q.corner⟩ : DyadicIndex) = ⟨R.scale, R.corner⟩ :=
    shiftedDyadicCube_index_injective g hQR
  have hn : Q.scale = R.scale := congrArg DyadicIndex.scale hi
  have ha : Q.corner = R.corner := congrArg DyadicIndex.corner hi
  have ht : Q.timeCorner = R.timeCorner :=
    shiftedGridInterval_corner_unique (dyadicScale_pos (2 * R.scale)) (hn ▸ hQ) hR
  cases Q
  cases R
  cases hn
  cases ha
  cases ht
  rfl

/-- The finite active cell sum is dominated by the spatial cube series. -/
theorem finite_active_parabolic_sum_le (g : ParabolicGridShift)
    (P : Finset ParabolicDyadicIndex) (𝒟 : Set (Set Vec3))
    (hP : ∀ Q ∈ P, parabolicSpatialCube g Q ∈ 𝒟)
    (θ : Set Vec3 → ℝ≥0∞) (t : ℝ) :
    (∑ Q ∈ P, (shiftedParabolicDyadicTime g Q.scale Q.timeCorner).indicator
      (fun _ ↦ θ (parabolicSpatialCube g Q)) t) ≤ ∑' A : 𝒟, θ A := by
  classical
  let S := P.filter (fun Q ↦ t ∈ shiftedParabolicDyadicTime g Q.scale Q.timeCorner)
  let j : ↥S → 𝒟 := fun Q ↦
    ⟨parabolicSpatialCube g Q, hP Q (mem_filter.1 Q.property).1⟩
  have hinj : Function.Injective j := by
    intro Q R hQR
    apply Subtype.ext
    exact parabolicSpatialCube_injOn_active g t (mem_filter.1 Q.property).2
      (mem_filter.1 R.property).2 (congrArg Subtype.val hQR)
  calc
    _ = ∑' Q : ↥S, θ (j Q) := by
      change _ = ∑' Q : ↥S, θ (parabolicSpatialCube g Q)
      rw [Finset.tsum_subtype S (fun Q ↦ θ (parabolicSpatialCube g Q))]
      simp only [S, Finset.sum_filter, Set.indicator_apply]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun A : 𝒟 ↦ θ A)

/-- The integrated parabolic coefficient obtained from the actual spatial trace weight. -/
def parabolicTraceCoefficient (μ : Measure ParabolicPoint) (F : ℤ → ℝ)
    (g : ParabolicGridShift) (f : ℝ → Vec3 → ℝ≥0∞) (p : ℝ)
    (Q : ParabolicDyadicIndex) : ℝ≥0∞ :=
  ∫⁻ t in shiftedParabolicDyadicTime g Q.scale Q.timeCorner,
    spatialTraceSetCoefficient μ F g (parabolicSpatialCube g Q) t *
      (⨍⁻ x in parabolicSpatialCube g Q, f t x ∂volume) ^ p

/-- All finite parabolic families are controlled by the integrated spatial series.
Only containment of their time intervals in the integration domain is required here. -/
theorem finite_parabolicTraceCoefficient_le_spatial_series
    (μ : Measure ParabolicPoint) (F : ℤ → ℝ) (g : ParabolicGridShift)
    (f : ℝ → Vec3 → ℝ≥0∞) (p : ℝ) (P : Finset ParabolicDyadicIndex)
    (𝒟 : Set (Set Vec3)) (J : Set ℝ)
    (hgrid : ∀ A ∈ 𝒟, A ∈ shiftedSpatialGrid g)
    (hP : ∀ Q ∈ P, parabolicSpatialCube g Q ∈ 𝒟)
    (hJ : ∀ Q ∈ P, shiftedParabolicDyadicTime g Q.scale Q.timeCorner ⊆ J)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2)) :
    (∑ Q ∈ P, parabolicTraceCoefficient μ F g f p Q) ≤
      ∑' A : 𝒟, ∫⁻ t in J, spatialTraceSetCoefficient μ F g A t *
        (⨍⁻ x in A, f t x ∂volume) ^ p := by
  classical
  let : Countable 𝒟 := (countable_shifted_dyadic_family g 𝒟 hgrid).to_subtype
  let w : Set Vec3 → ℝ → ℝ≥0∞ := fun A t ↦
    spatialTraceSetCoefficient μ F g A t * (⨍⁻ x in A, f t x ∂volume) ^ p
  have hw (A : Set Vec3) : Measurable (w A) := by
    have havg : Measurable (fun t ↦ ⨍⁻ x in A, f t x ∂volume) := by
      simp_rw [setLAverage_eq]
      exact (hf.lintegral_prod_right' (ν := volume.restrict A)).div measurable_const
    exact (measurable_spatialTraceSetCoefficient μ F g A).mul
      (ENNReal.continuous_rpow_const.measurable.comp havg)
  have hterm (Q : ParabolicDyadicIndex) (hQ : Q ∈ P) :
      parabolicTraceCoefficient μ F g f p Q =
        ∫⁻ t in J, (shiftedParabolicDyadicTime g Q.scale Q.timeCorner).indicator
          (w (parabolicSpatialCube g Q)) t := by
    have hI : MeasurableSet (shiftedParabolicDyadicTime g Q.scale Q.timeCorner) :=
      measurableSet_Ico
    rw [lintegral_indicator hI, Measure.restrict_restrict hI,
      Set.inter_eq_left.mpr (hJ Q hQ)]
    rfl
  calc
    _ = ∫⁻ t in J, ∑ Q ∈ P,
        (shiftedParabolicDyadicTime g Q.scale Q.timeCorner).indicator
          (w (parabolicSpatialCube g Q)) t := by
      rw [lintegral_finsetSum P (f := fun Q t ↦
        (shiftedParabolicDyadicTime g Q.scale Q.timeCorner).indicator
          (w (parabolicSpatialCube g Q)) t) (fun Q _ ↦ (hw _).indicator
            (show MeasurableSet (shiftedParabolicDyadicTime g Q.scale Q.timeCorner) from
              measurableSet_Ico))]
      exact Finset.sum_congr rfl hterm
    _ ≤ ∫⁻ t in J, ∑' A : 𝒟, w A t :=
      lintegral_mono (fun t ↦ finite_active_parabolic_sum_le g P 𝒟 hP (fun A ↦ w A t) t)
    _ = _ := lintegral_tsum (fun A ↦ (hw A).aemeasurable)

/-- Actual cell growth, rather than a parabolic Carleson premise, controls the finite
parabolic trace sum. Restricting `J` and `f` gives a bound on each individual root. -/
theorem finite_parabolicTraceCoefficient_embedding
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (F : ℤ → ℝ)
    (g : ParabolicGridShift) (f : ℝ → Vec3 → ℝ≥0∞)
    (P : Finset ParabolicDyadicIndex) (𝒟 : Set (Set Vec3)) (J : Set ℝ)
    {M p : ℝ} (hM : 0 ≤ M) (hp : 1 < p)
    (hgrid : ∀ A ∈ 𝒟, A ∈ shiftedSpatialGrid g)
    (hP : ∀ Q ∈ P, parabolicSpatialCube g Q ∈ 𝒟)
    (hJ : ∀ Q ∈ P, shiftedParabolicDyadicTime g Q.scale Q.timeCorner ⊆ J)
    (hF : ∀ A ∈ 𝒟, 0 < F (shiftedSpatialRepresentation g A).scale)
    (hmono : ∀ A ∈ 𝒟, ∀ k : ℕ, F (shiftedSpatialRepresentation g A).scale ≤
      F ((shiftedSpatialRepresentation g A).scale + k))
    (hgrowth : ∀ t : ℝ, ∀ A ∈ 𝒟,
      (μ (shiftedTraceCell g (shiftedSpatialRepresentation g A).scale
        (shiftedSpatialRepresentation g A).corner t)).toReal ≤
          M * dyadicScale (shiftedSpatialRepresentation g A).scale *
            F (shiftedSpatialRepresentation g A).scale)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂(volume.restrict J).prod volume) < ⊤) :
    (∑ Q ∈ P, parabolicTraceCoefficient μ F g f p Q) ≤
      ENNReal.ofReal (2 * Real.sqrt M) * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        ∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂(volume.restrict J).prod volume :=
  (finite_parabolicTraceCoefficient_le_spatial_series μ F g f p P 𝒟 J
    hgrid hP hJ hf).trans
      (integrated_spatialTraceSetCoefficient_embedding μ F g (volume.restrict J) 𝒟 f
        hM hp hgrid hF hmono hgrowth hf hfp)

/-- Cell containment implies containment of each of its two projections. -/
theorem parabolicCell_projection_subset {g : ParabolicGridShift}
    {Q R : ParabolicDyadicIndex}
    (hsub : shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R) :
    parabolicSpatialCube g Q ⊆ parabolicSpatialCube g R ∧
      shiftedParabolicDyadicTime g Q.scale Q.timeCorner ⊆
        shiftedParabolicDyadicTime g R.scale R.timeCorner :=
  (Set.prod_subset_prod_iff' (shiftedParabolicDyadicCell_nonempty g Q)).1 hsub

/-- The spatial cubes contained in one fixed parabolic root. -/
def rootTraceSpatialFamily (g : ParabolicGridShift) (R : ParabolicDyadicIndex) :
    Set (Set Vec3) := {A | A ∈ shiftedSpatialGrid g ∧ A ⊆ parabolicSpatialCube g R}

/-- The trace density cut off to the root's spatial cube. -/
def rootTraceDensity (g : ParabolicGridShift) (R : ParabolicDyadicIndex)
    (f : ℝ → Vec3 → ℝ≥0∞) (t : ℝ) (x : Vec3) : ℝ≥0∞ :=
  (parabolicSpatialCube g R).indicator (f t) x

/-- Spatial restriction preserves joint measurability. -/
theorem measurable_rootTraceDensity (g : ParabolicGridShift) (R : ParabolicDyadicIndex)
    (f : ℝ → Vec3 → ℝ≥0∞)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2)) :
    Measurable (fun z : ℝ × Vec3 ↦ rootTraceDensity g R f z.1 z.2) := by
  have hset : MeasurableSet ((Set.univ : Set ℝ) ×ˢ parabolicSpatialCube g R) :=
    MeasurableSet.univ.prod (shiftedDyadicCube_measurable g R.scale R.corner)
  convert hf.indicator hset using 1
  funext z
  by_cases hx : z.2 ∈ parabolicSpatialCube g R
  · simp [rootTraceDensity, Set.indicator_of_mem, hx]
  · simp [rootTraceDensity, Set.indicator_of_notMem, hx]

/-- The spatial cutoff does not alter the actual coefficients of any descendant cell. -/
theorem parabolicTraceCoefficient_rootTraceDensity_eq
    (μ : Measure ParabolicPoint) (F : ℤ → ℝ) (g : ParabolicGridShift)
    (R Q : ParabolicDyadicIndex) (f : ℝ → Vec3 → ℝ≥0∞) (p : ℝ)
    (hsub : parabolicSpatialCube g Q ⊆ parabolicSpatialCube g R) :
    parabolicTraceCoefficient μ F g (rootTraceDensity g R f) p Q =
      parabolicTraceCoefficient μ F g f p Q := by
  apply lintegral_congr
  intro t
  congr 2
  exact setLAverage_congr_fun (shiftedDyadicCube_measurable g Q.scale Q.corner)
    (fun x hx ↦ Set.indicator_of_mem (hsub hx) (f t))

/-- The product-space power mass of the root cutoff is exactly the native root mass. -/
theorem rootTraceDensity_power_integral_eq
    (g : ParabolicGridShift) (R : ParabolicDyadicIndex)
    (f : ℝ → Vec3 → ℝ≥0∞) {p : ℝ} (hp : 0 < p)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2)) :
    (∫⁻ z : ℝ × Vec3, rootTraceDensity g R f z.1 z.2 ^ p
      ∂(volume.restrict (shiftedParabolicDyadicTime g R.scale R.timeCorner)).prod volume) =
        ∫⁻ z in shiftedParabolicDyadicCell g R, f z.2 z.1 ^ p := by
  change _ = ∫⁻ z : Vec3 × ℝ in parabolicSpatialCube g R ×ˢ
    shiftedParabolicDyadicTime g R.scale R.timeCorner, f z.2 z.1 ^ p
  have hroot := measurable_rootTraceDensity g R f hf
  have hpowroot : Measurable (fun z : ℝ × Vec3 ↦ rootTraceDensity g R f z.1 z.2 ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hroot
  have hpow : Measurable (fun z : Vec3 × ℝ ↦ f z.2 z.1 ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (hf.comp measurable_swap)
  have hpoint (t : ℝ) :
      (fun x ↦ rootTraceDensity g R f t x ^ p) =
        (parabolicSpatialCube g R).indicator (fun x ↦ f t x ^ p) := by
    funext x
    by_cases hx : x ∈ parabolicSpatialCube g R
    · simp [rootTraceDensity, hx]
    · simp [rootTraceDensity, hx, ENNReal.zero_rpow_of_pos hp]
  rw [lintegral_prod _ hpowroot.aemeasurable]
  have hinner (t : ℝ) : (∫⁻ x, rootTraceDensity g R f t x ^ p) =
      ∫⁻ x in parabolicSpatialCube g R, f t x ^ p := by
    exact (lintegral_congr (congrFun (hpoint t))).trans
      (lintegral_indicator (show MeasurableSet (parabolicSpatialCube g R) from
        shiftedDyadicCube_measurable g R.scale R.corner) _)
  simp_rw [hinner]
  rw [← lintegral_prod_symm _ hpow.aemeasurable, Measure.prod_restrict]
  rw [← Measure.volume_eq_prod]

/-- Every actual descendant family satisfies the parabolic trace Carleson estimate,
with only the density's power mass inside the root on the right-hand side. -/
theorem finite_descendant_parabolicTraceCoefficient_bound
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (F : ℤ → ℝ)
    (g : ParabolicGridShift) (R : ParabolicDyadicIndex)
    (f : ℝ → Vec3 → ℝ≥0∞) (P : Finset ParabolicDyadicIndex)
    {M p : ℝ} (hM : 0 ≤ M) (hp : 1 < p)
    (hP : ∀ Q ∈ P, shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R)
    (hF : ∀ A ∈ rootTraceSpatialFamily g R,
      0 < F (shiftedSpatialRepresentation g A).scale)
    (hmono : ∀ A ∈ rootTraceSpatialFamily g R, ∀ k : ℕ,
      F (shiftedSpatialRepresentation g A).scale ≤
        F ((shiftedSpatialRepresentation g A).scale + k))
    (hgrowth : ∀ t : ℝ, ∀ A ∈ rootTraceSpatialFamily g R,
      (μ (shiftedTraceCell g (shiftedSpatialRepresentation g A).scale
        (shiftedSpatialRepresentation g A).corner t)).toReal ≤
          M * dyadicScale (shiftedSpatialRepresentation g A).scale *
            F (shiftedSpatialRepresentation g A).scale)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z in shiftedParabolicDyadicCell g R, f z.2 z.1 ^ p) < ⊤) :
    (∑ Q ∈ P, parabolicTraceCoefficient μ F g f p Q) ≤
      ENNReal.ofReal (2 * Real.sqrt M) * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        ∫⁻ z in shiftedParabolicDyadicCell g R, f z.2 z.1 ^ p := by
  have hPspace (Q : ParabolicDyadicIndex) (hQ : Q ∈ P) :
      parabolicSpatialCube g Q ∈ rootTraceSpatialFamily g R :=
    ⟨⟨⟨Q.scale, Q.corner⟩, rfl⟩, (parabolicCell_projection_subset (hP Q hQ)).1⟩
  have htime (Q : ParabolicDyadicIndex) (hQ : Q ∈ P) :
      shiftedParabolicDyadicTime g Q.scale Q.timeCorner ⊆
        shiftedParabolicDyadicTime g R.scale R.timeCorner :=
    (parabolicCell_projection_subset (hP Q hQ)).2
  have hmass := rootTraceDensity_power_integral_eq g R f (by linarith : 0 < p) hf
  have hfpRoot : (∫⁻ z : ℝ × Vec3, rootTraceDensity g R f z.1 z.2 ^ p
      ∂(volume.restrict (shiftedParabolicDyadicTime g R.scale R.timeCorner)).prod volume) < ⊤ :=
    hmass ▸ hfp
  have hbound := finite_parabolicTraceCoefficient_embedding μ F g (rootTraceDensity g R f)
    P (rootTraceSpatialFamily g R) (shiftedParabolicDyadicTime g R.scale R.timeCorner)
    hM hp (fun _ hA ↦ hA.1) hPspace htime hF hmono hgrowth
    (measurable_rootTraceDensity g R f hf) hfpRoot
  calc
    _ = ∑ Q ∈ P, parabolicTraceCoefficient μ F g (rootTraceDensity g R f) p Q := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact (parabolicTraceCoefficient_rootTraceDensity_eq μ F g R Q f p
        (parabolicCell_projection_subset (hP Q hQ)).1).symm
    _ ≤ _ := by simpa only [hmass] using hbound

/-- The slice coefficient uses precisely the original cell mass on its time interval. -/
theorem spatialTraceSetCoefficient_eq_on_cell_time
    (μ : Measure ParabolicPoint) (F : ℤ → ℝ) (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) {t : ℝ}
    (ht : t ∈ shiftedParabolicDyadicTime g Q.scale Q.timeCorner) :
    spatialTraceSetCoefficient μ F g (parabolicSpatialCube g Q) t =
      ENNReal.ofReal (dyadicScale Q.scale * Real.sqrt (dyadicScale Q.scale ^ 3 / F Q.scale) *
        Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal)) := by
  have htime : shiftedTimeCellSelector g Q.scale t = Q.timeCorner :=
    shiftedGridInterval_corner_unique (dyadicScale_pos (2 * Q.scale))
      (mem_shiftedTimeCellSelector g Q.scale t) ht
  unfold spatialTraceSetCoefficient parabolicSpatialCube
  rw [shiftedSpatialRepresentation_eq g (⟨Q.scale, Q.corner⟩ : DyadicIndex)]
  simp only [spatialTraceCoefficient, shiftedTraceCell, shiftedTraceIndex, htime]

/-- The spatial averaging normalization has exactly the mixed-gradient exponent. -/
theorem trace_scalar_normalization {ℓ F m : ℝ} (hℓ : 0 < ℓ) (hF : 0 < F) :
    (ℓ * Real.sqrt (ℓ ^ 3 / F) * Real.sqrt m) * ℓ ^ (-7 / 2 : ℝ) =
      Real.sqrt (m * ℓ / F) * ℓ ^ (-3 / 2 : ℝ) := by
  have hroot : Real.sqrt (ℓ ^ 3 / F) * Real.sqrt m =
      ℓ * Real.sqrt (m * ℓ / F) := by
    rw [← Real.sqrt_mul (div_nonneg (pow_nonneg hℓ.le _) hF.le)]
    have hid : ℓ ^ 3 / F * m = ℓ ^ 2 * (m * ℓ / F) := by ring
    rw [hid, Real.sqrt_mul (sq_nonneg ℓ), Real.sqrt_sq hℓ.le]
  calc
    _ = Real.sqrt (m * ℓ / F) * (ℓ ^ 2 * ℓ ^ (-7 / 2 : ℝ)) := by
      rw [mul_assoc ℓ, hroot]
      ring
    _ = _ := by
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_add hℓ]
      norm_num

/-- The reciprocal volume power of a spatial cube is the explicit mixed exponent. -/
theorem parabolicSpatialCube_inverse_volume_rpow (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) :
    (volume (parabolicSpatialCube g Q))⁻¹ ^ (7 / 6 : ℝ) =
      ENNReal.ofReal (dyadicScale Q.scale ^ (-7 / 2 : ℝ)) := by
  unfold parabolicSpatialCube
  rw [volume_shiftedDyadicCube, ← ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le,
    ← ENNReal.ofReal_inv_of_pos (pow_pos (dyadicScale_pos Q.scale) 3),
    ENNReal.ofReal_rpow_of_pos (inv_pos.2 (pow_pos (dyadicScale_pos Q.scale) 3))]
  congr 1
  rw [Real.inv_rpow (pow_nonneg (dyadicScale_pos Q.scale).le _),
    ← Real.rpow_natCast, ← Real.rpow_mul (dyadicScale_pos Q.scale).le]
  norm_num
  rw [Real.rpow_neg (dyadicScale_pos Q.scale).le]

/-- The actual normalized mixed mass on a parabolic dyadic cell. -/
def dyadicMixedActivity (g : ParabolicGridShift) (f : ℝ → Vec3 → ℝ≥0∞)
    (Q : ParabolicDyadicIndex) : ℝ≥0∞ :=
  ENNReal.ofReal (dyadicScale Q.scale ^ (-3 / 2 : ℝ)) *
    ∫⁻ t in shiftedParabolicDyadicTime g Q.scale Q.timeCorner,
      (∫⁻ x in parabolicSpatialCube g Q, f t x) ^ (7 / 6 : ℝ)

/-- The integrated trace coefficient is the literal square-root mass weight times
the actual mixed activity. No trace or embedding conclusion is assumed. -/
theorem parabolicTraceCoefficient_eq_mixedActivity
    (μ : Measure ParabolicPoint) (F : ℤ → ℝ) (g : ParabolicGridShift)
    (f : ℝ → Vec3 → ℝ≥0∞) (Q : ParabolicDyadicIndex) (hF : 0 < F Q.scale) :
    parabolicTraceCoefficient μ F g f (7 / 6) Q =
      ENNReal.ofReal (Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal *
        dyadicScale Q.scale / F Q.scale)) * dyadicMixedActivity g f Q := by
  let c := dyadicScale Q.scale * Real.sqrt (dyadicScale Q.scale ^ 3 / F Q.scale) *
    Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal)
  have hc : 0 ≤ c := by
    have hℓ := dyadicScale_pos Q.scale
    dsimp [c]
    positivity
  have hweight : ENNReal.ofReal c * (volume (parabolicSpatialCube g Q))⁻¹ ^ (7 / 6 : ℝ) =
      ENNReal.ofReal (Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal *
        dyadicScale Q.scale / F Q.scale)) *
          ENNReal.ofReal (dyadicScale Q.scale ^ (-3 / 2 : ℝ)) := by
    rw [parabolicSpatialCube_inverse_volume_rpow, ← ENNReal.ofReal_mul hc,
      trace_scalar_normalization (dyadicScale_pos Q.scale) hF,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  calc
    _ = ∫⁻ t in shiftedParabolicDyadicTime g Q.scale Q.timeCorner,
        (ENNReal.ofReal c * (volume (parabolicSpatialCube g Q))⁻¹ ^ (7 / 6 : ℝ)) *
          (∫⁻ x in parabolicSpatialCube g Q, f t x) ^ (7 / 6 : ℝ) := by
      apply setLIntegral_congr_fun measurableSet_Ico
      intro t ht
      dsimp only
      rw [spatialTraceSetCoefficient_eq_on_cell_time μ F g Q ht, setLAverage_eq,
        ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 7 / 6)]
      simp only [div_eq_mul_inv, ← ENNReal.inv_rpow]
      dsimp only [c]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = _ := by
      rw [hweight, lintegral_const_mul' _ _ (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
      exact mul_assoc _ _ _

/-- Actual Frostman ball growth supplies a uniform mixed trace Carleson bound on every
sufficiently fine root, with exactly that root's density power mass on the right. -/
theorem exists_frostman_mixed_trace_carleson
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (g : ParabolicGridShift) (f : ℝ → Vec3 → ℝ≥0∞)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2)) :
    ∃ n₀ : ℤ, ∀ R : ParabolicDyadicIndex, n₀ ≤ R.scale →
      ∀ P : Finset ParabolicDyadicIndex,
        (∀ Q ∈ P, shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R) →
        (∫⁻ z in shiftedParabolicDyadicCell g R, f z.2 z.1 ^ (7 / 6 : ℝ)) < ⊤ →
        (∑ Q ∈ P, ENNReal.ofReal
          (Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal * dyadicScale Q.scale /
            dyadicLogFactor k Q.scale)) * dyadicMixedActivity g f Q) ≤
          ENNReal.ofReal (2 * Real.sqrt (4 * C.toReal)) * (64 : ℝ≥0∞) ^ (7 / 6 : ℝ) *
            maximalStrongConstant (7 / 6) *
              ∫⁻ z in shiftedParabolicDyadicCell g R, f z.2 z.1 ^ (7 / 6 : ℝ) := by
  obtain ⟨n₀, hcut⟩ := exists_dyadicLogFactor_frostman_cutoff k hr₀ hρ
  refine ⟨n₀, fun R hR P hP hfp ↦ ?_⟩
  have htail (A : Set Vec3) (hA : A ∈ rootTraceSpatialFamily g R) :
      n₀ ≤ (shiftedSpatialRepresentation g A).scale := by
    apply hR.trans
    apply shiftedDyadicCube_scale_le_of_subset g (shiftedSpatialRepresentation g A)
      (⟨R.scale, R.corner⟩ : DyadicIndex)
    simpa only [shiftedSpatialRepresentation_cube hA.1, parabolicSpatialCube] using hA.2
  have hF (A : Set Vec3) (_hA : A ∈ rootTraceSpatialFamily g R) :
      0 < dyadicLogFactor k (shiftedSpatialRepresentation g A).scale :=
    zero_lt_one.trans_le (one_le_dyadicLogFactor _ _)
  have hmono (A : Set Vec3) (hA : A ∈ rootTraceSpatialFamily g R) (d : ℕ) :
      dyadicLogFactor k (shiftedSpatialRepresentation g A).scale ≤
        dyadicLogFactor k ((shiftedSpatialRepresentation g A).scale + d) :=
    (hcut _ (htail A hA)).2.2.2 d
  have hmass (t : ℝ) (A : Set Vec3) (hA : A ∈ rootTraceSpatialFamily g R) :
      (μ (shiftedTraceCell g (shiftedSpatialRepresentation g A).scale
        (shiftedSpatialRepresentation g A).corner t)).toReal ≤
          (4 * C.toReal) * dyadicScale (shiftedSpatialRepresentation g A).scale *
            dyadicLogFactor k (shiftedSpatialRepresentation g A).scale := by
    let Q := shiftedTraceIndex g (shiftedSpatialRepresentation g A).scale
      (shiftedSpatialRepresentation g A).corner t
    exact shiftedParabolicDyadicCell_real_mass_le_log_growth μ k hC hgrowth hdouble
      g Q (hcut _ (htail A hA)).1 (hcut _ (htail A hA)).2.1
  have hbound := finite_descendant_parabolicTraceCoefficient_bound μ (dyadicLogFactor k)
    g R f P (by positivity : 0 ≤ 4 * C.toReal) (by norm_num : (1 : ℝ) < 7 / 6)
    hP hF hmono hmass hf hfp
  calc
    _ = ∑ Q ∈ P, parabolicTraceCoefficient μ (dyadicLogFactor k) g f (7 / 6) Q := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      exact (parabolicTraceCoefficient_eq_mixedActivity μ (dyadicLogFactor k) g f Q
        (zero_lt_one.trans_le (one_le_dyadicLogFactor _ _))).symm
    _ ≤ _ := hbound

/-- The mixed activity of the actual gradient on a dyadic parabolic cell. -/
def dyadicMixedGradientActivity {E : Type*} [NormedAddCommGroup E]
    (g : ParabolicGridShift) (D : ParabolicPoint → E) (Q : ParabolicDyadicIndex) : ℝ≥0∞ :=
  dyadicMixedActivity g (fun t x ↦ ‖D (x, t)‖ₑ ^ (12 / 7 : ℝ)) Q

/-- The power in the mixed trace is exactly the dissipation power two. -/
theorem mixedGradient_trace_power {E : Type*} [NormedAddCommGroup E] (v : E) :
    (‖v‖ₑ ^ (12 / 7 : ℝ)) ^ (7 / 6 : ℝ) = ‖v‖ₑ ^ (2 : ℕ) := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Actual Frostman ball growth derives the descendant Carleson estimate for the
actual mixed-gradient coefficients, against the array-norm dissipation measure. -/
theorem exists_frostman_gradient_trace_carleson
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (g : ParabolicGridShift) (D : ParabolicPoint → E) (hD : Measurable D) :
    ∃ n₀ : ℤ, ∀ R : ParabolicDyadicIndex, n₀ ≤ R.scale →
      ∀ P : Finset ParabolicDyadicIndex,
        (∀ Q ∈ P, shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R) →
        (∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ)) < ⊤ →
        (∑ Q ∈ P, ENNReal.ofReal
          (Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal * dyadicScale Q.scale /
            dyadicLogFactor k Q.scale)) * dyadicMixedGradientActivity g D Q) ≤
          ENNReal.ofReal (2 * Real.sqrt (4 * C.toReal)) * (64 : ℝ≥0∞) ^ (7 / 6 : ℝ) *
            maximalStrongConstant (7 / 6) *
              ∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ) := by
  let f : ℝ → Vec3 → ℝ≥0∞ := fun t x ↦ ‖D (x, t)‖ₑ ^ (12 / 7 : ℝ)
  have hswap : Measurable (fun z : ℝ × Vec3 ↦ (z.2, z.1) : ℝ × Vec3 → ParabolicPoint) :=
    measurable_swap
  have hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2) :=
    (hD.comp hswap).enorm.pow_const (12 / 7 : ℝ)
  have hmass (R : ParabolicDyadicIndex) :
      (∫⁻ z in shiftedParabolicDyadicCell g R, f z.2 z.1 ^ (7 / 6 : ℝ)) =
        ∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ) := by
    apply lintegral_congr
    intro z
    exact mixedGradient_trace_power (D z)
  obtain ⟨n₀, hbound⟩ :=
    exists_frostman_mixed_trace_carleson μ k hC hr₀ hρ hgrowth hdouble g f hf
  refine ⟨n₀, fun R hR P hP hfinite ↦ ?_⟩
  have h := hbound R hR P hP (by simpa only [hmass] using hfinite)
  simpa only [hmass, dyadicMixedGradientActivity] using h

end FluidSingularSets
