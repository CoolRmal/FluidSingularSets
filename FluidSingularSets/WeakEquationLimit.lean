-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedLpStability
public import FluidSingularSets.StrongLpIntegrands
public import CKN.ClassEquivalence.DivergenceFreeIntegrand
public import CKN.ClassEquivalence.MomentumIntegrand

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A coordinate of a strongly convergent finite-dimensional array converges
strongly in the same exponent. -/
theorem tendsto_eLpNorm_pi_component_sub
    {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {g : α → ι → E} {gs : ℕ → α → ι → E}
    (hg : MemLp g p μ) (hgs : ∀ n, MemLp (gs n) p μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (gs n - g) p μ) atTop (𝓝 0)) (i : ι) :
    Tendsto (fun n ↦ eLpNorm (fun z ↦ gs n z i - g z i) p μ) atTop (𝓝 0) := by
  have hgi := memLp_pi_iff.mp hg i
  have hgsi := fun n ↦ memLp_pi_iff.mp (hgs n) i
  have hbound (n : ℕ) : eLpNorm (fun z ↦ gs n z i - g z i) p μ ≤
      eLpNorm (gs n - g) p μ :=
    eLpNorm_mono ((hgsi n).sub hgi).aestronglyMeasurable
      (fun z ↦ norm_le_pi_norm ((gs n - g) z) i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ ↦ bot_le) hbound

/-- Actual suitable data provide the divergence integrand's integrability,
while compact strong cubic velocity convergence preserves its zero pairing. -/
theorem suitable_divergence_of_strongLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {us : ℕ → ParabolicPoint → Vec3} {Ds : ℕ → ParabolicPoint → Fin 3 → Vec3}
    {ps : ℕ → ParabolicPoint → ℝ} {fs : ℕ → ParabolicPoint → Vec3}
    (hsols : ∀ n, IsSuitableWeakSolutionIntegrable Ω I q (us n) (Ds n) (ps n) (fs n))
    (hconv : ∀ K : Set ParabolicPoint, IsCompact K → K ⊆ spaceTimeSet Ω I →
      Tendsto (fun n ↦ eLpNorm (us n - u) 3 (volume.restrict K)) atTop (𝓝 0))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    IntegrableOn (fun z ↦ ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      (∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z) = 0 := by
  let K := tsupport (show ParabolicPoint → ℝ from ψ)
  have hK : IsCompact K := isCompact_tsupport_parabolic hψ.2.1
  have hKsub : K ⊆ spaceTimeSet Ω I := tsupport_parabolic_subset_spaceTimeSet hψ
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hu : MemLp u 3 (volume.restrict K) := by
    simpa using velocity_memLp_three_on_compact_of_data hdata hK hKsub
  have hus : ∀ n, MemLp (us n) 3 (volume.restrict K) := by
    intro n
    simpa using velocity_memLp_three_on_compact_of_data (hsols n).toData hK hKsub
  have huc := hconv K hK hKsub
  have hc (i : Fin 3) : MemLp (fun z : ParabolicPoint ↦ spatialPartial ψ i z) ⊤
      (volume.restrict K) := by
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
    exact MemLp.of_bound (spatialPartial_contDiff hψ.1 i).continuous.aestronglyMeasurable
      C (Eventually.of_forall hC)
  have hterms (i : Fin 3) :
      Tendsto (fun n ↦ ∫ z in K, us n z i * spatialPartial ψ i z) atTop
        (𝓝 (∫ z in K, u z i * spatialPartial ψ i z)) :=
    tendsto_integral_mul_bounded (by norm_num) (by norm_num)
      (memLp_pi_iff.mp hu i) (fun n ↦ memLp_pi_iff.mp (hus n) i) (hc i)
      (tendsto_eLpNorm_pi_component_sub hu hus huc i)
  have hInt (i : Fin 3) : Integrable (fun z ↦ u z i * spatialPartial ψ i z)
      (volume.restrict K) :=
    ((memLp_pi_iff.mp hu i).mul (r := 3) (hc i)).integrable (by norm_num)
  have hInts (n : ℕ) (i : Fin 3) : Integrable (fun z ↦ us n z i * spatialPartial ψ i z)
      (volume.restrict K) :=
    ((memLp_pi_iff.mp (hus n) i).mul (r := 3) (hc i)).integrable (by norm_num)
  have hsum : Tendsto (fun n ↦ ∫ z in K, ∑ i, us n z i * spatialPartial ψ i z) atTop
      (𝓝 (∫ z in K, ∑ i, u z i * spatialPartial ψ i z)) := by
    simp_rw [integral_finsetSum Finset.univ (fun i _ ↦ hInts _ i),
      integral_finsetSum Finset.univ (fun i _ ↦ hInt i)]
    exact tendsto_finsetSum Finset.univ (fun i _ ↦ hterms i)
  have hoff (w : ParabolicPoint → Vec3) (z : ParabolicPoint) (hz : z ∉ K) :
      (∑ i, w z i * spatialPartial ψ i z) = 0 := by
    change z ∉ tsupport (show ParabolicPoint → ℝ from ψ) at hz
    rw [tsupport_parabolic_eq] at hz
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [spatialPartial_eq_zero_off_tsupport hz i, mul_zero]
  have hDomEq (w : ParabolicPoint → Vec3) :
      (∫ z in spaceTimeSet Ω I, ∑ i, w z i * spatialPartial ψ i z) =
        ∫ z in K, ∑ i, w z i * spatialPartial ψ i z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦
      hoff w z (fun hmem ↦ hz (hKsub hmem))),
      setIntegral_eq_integral_of_forall_compl_eq_zero (hoff w)]
  have hnzero (n : ℕ) : (∫ z in K, ∑ i, us n z i * spatialPartial ψ i z) = 0 := by
    rw [← hDomEq]
    exact ((hsols n).2.2.2.2.2.2.1 ψ hψ).2
  have hzero : (∫ z in K, ∑ i, u z i * spatialPartial ψ i z) = 0 := by
    have hzeroLimit : Tendsto
        (fun n ↦ ∫ z in K, ∑ i, us n z i * spatialPartial ψ i z) atTop (𝓝 0) := by
      simp_rw [hnzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hsum hzeroLimit
  exact ⟨divergenceFree_integrand_integrableOn_of_data hdata hψ, (hDomEq u).trans hzero⟩

/-- The genuine weak momentum equation is closed under compact strong cubic
velocity, quadratic gradient, and three-halves pressure and force convergence.
The limit's analytic data are supplied separately, while the actual equations
of every approximant supply all zero weak pairings. -/
theorem suitable_momentum_of_strongLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {us : ℕ → ParabolicPoint → Vec3} {Ds : ℕ → ParabolicPoint → Fin 3 → Vec3}
    {ps : ℕ → ParabolicPoint → ℝ} {fs : ℕ → ParabolicPoint → Vec3}
    (hsols : ∀ n, IsSuitableWeakSolutionIntegrable Ω I q (us n) (Ds n) (ps n) (fs n))
    (hconv : ∀ K : Set ParabolicPoint, IsCompact K → K ⊆ spaceTimeSet Ω I →
      Tendsto (fun n ↦ eLpNorm (us n - u) 3 (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (Ds n - Du) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (ps n - p) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fs n - f) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict K)) atTop (𝓝 0))
    {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    IntegrableOn (frameMomentumDensity u Du p f φ) (tsupport φ) volume ∧
      (∫ z in spaceTimeSet Ω I, frameMomentumDensity u Du p f φ z) = 0 := by
  let K := tsupport (show ParabolicPoint → Vec3 from φ)
  have hK : IsCompact K := isCompact_tsupport_parabolic hφ.2.1
  have hKsub : K ⊆ spaceTimeSet Ω I := tsupport_parabolic_subset_spaceTimeSet hφ
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let r : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  have hr : 1 ≤ r := by norm_num [r]
  have hrfin : r ≠ ⊤ := ENNReal.ofReal_ne_top
  let : ENNReal.HolderTriple 3 3 r := by
    have h : Real.HolderTriple 3 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa [r] using h.ennrealOfReal
  have hqr : r ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal (by linarith [hdata.five_halves_lt_exponent])
  have hu : MemLp u 3 (volume.restrict K) := by
    simpa using velocity_memLp_three_on_compact_of_data hdata hK hKsub
  have hus : ∀ n, MemLp (us n) 3 (volume.restrict K) := by
    intro n
    simpa using velocity_memLp_three_on_compact_of_data (hsols n).toData hK hKsub
  have hD := gradient_memLp_two_on_compact_of_data hdata hK hKsub
  have hDs := fun n ↦ gradient_memLp_two_on_compact_of_data (hsols n).toData hK hKsub
  have hp : MemLp p r (volume.restrict K) :=
    pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub
  have hps : ∀ n, MemLp (ps n) r (volume.restrict K) := fun n ↦
    pressure_memLp_threeHalves_on_compact_of_data (hsols n).toData hK hKsub
  have hf : MemLp f r (volume.restrict K) :=
    (force_memLp_on_compact_of_data hdata hK hKsub).mono_exponent hqr
  have hfs : ∀ n, MemLp (fs n) r (volume.restrict K) := fun n ↦
    (force_memLp_on_compact_of_data (hsols n).toData hK hKsub).mono_exponent hqr
  obtain ⟨huconv, hDconv, hpconv, hfconv⟩ := hconv K hK hKsub
  have huc (i : Fin 3) := tendsto_eLpNorm_pi_component_sub hu hus huconv i
  have hDc (i j : Fin 3) := tendsto_eLpNorm_pi_component_sub (memLp_pi_iff.mp hD i)
    (fun n ↦ memLp_pi_iff.mp (hDs n) i)
    (tendsto_eLpNorm_pi_component_sub hD hDs hDconv i) j
  have hfc (i : Fin 3) := tendsto_eLpNorm_pi_component_sub hf hfs hfconv i
  have htime (i : Fin 3) : MemLp
      (fun z : ParabolicPoint ↦ timePartial (fun w ↦ φ w i) z) ⊤ (volume.restrict K) := by
    have hcomp := component_mem_spaceTimeTestFunction hφ i
    obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hcomp
    exact MemLp.of_bound (contDiff_timePartial hcomp.1).continuous.aestronglyMeasurable
      C (Eventually.of_forall hC)
  have hspace (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint ↦ spatialPartial (fun w ↦ φ w i) j z) ⊤
      (volume.restrict K) := by
    have hcomp := component_mem_spaceTimeTestFunction hφ i
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcomp j
    exact MemLp.of_bound (spatialPartial_contDiff hcomp.1 j).continuous.aestronglyMeasurable
      C (Eventually.of_forall hC)
  have hvalue (i : Fin 3) : MemLp (fun z : ParabolicPoint ↦ φ z i) ⊤
      (volume.restrict K) := by
    have hcomp := component_mem_spaceTimeTestFunction hφ i
    obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hcomp
    exact MemLp.of_bound hcomp.1.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  have hT (i : Fin 3) :
      Tendsto (fun n ↦ ∫ z in K, us n z i * timePartial (fun w ↦ φ w i) z) atTop
        (𝓝 (∫ z in K, u z i * timePartial (fun w ↦ φ w i) z)) :=
    tendsto_integral_mul_bounded (by norm_num) (by norm_num)
      (memLp_pi_iff.mp hu i) (fun n ↦ memLp_pi_iff.mp (hus n) i) (htime i) (huc i)
  have hN (i j : Fin 3) :
      Tendsto (fun n ↦ ∫ z in K,
        us n z i * us n z j * spatialPartial (fun w ↦ φ w i) j z) atTop
        (𝓝 (∫ z in K, u z i * u z j * spatialPartial (fun w ↦ φ w i) j z)) :=
    tendsto_integral_mul_mul_bounded (by norm_num) (by norm_num) hr hrfin
      (memLp_pi_iff.mp hu i) (memLp_pi_iff.mp hu j)
      (fun n ↦ memLp_pi_iff.mp (hus n) i) (fun n ↦ memLp_pi_iff.mp (hus n) j)
      (hspace i j) (huc i) (huc j)
  have hV (i j : Fin 3) :
      Tendsto (fun n ↦ ∫ z in K, Ds n z i j * spatialPartial (fun w ↦ φ w i) j z) atTop
        (𝓝 (∫ z in K, Du z i j * spatialPartial (fun w ↦ φ w i) j z)) :=
    tendsto_integral_mul_bounded (by norm_num) (by norm_num)
      (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j)
      (fun n ↦ memLp_pi_iff.mp (memLp_pi_iff.mp (hDs n) i) j) (hspace i j) (hDc i j)
  have hP (i : Fin 3) :
      Tendsto (fun n ↦ ∫ z in K, ps n z * spatialPartial (fun w ↦ φ w i) i z) atTop
        (𝓝 (∫ z in K, p z * spatialPartial (fun w ↦ φ w i) i z)) :=
    tendsto_integral_mul_bounded hr hrfin hp hps (hspace i i) hpconv
  have hF (i : Fin 3) :
      Tendsto (fun n ↦ ∫ z in K, fs n z i * φ z i) atTop
        (𝓝 (∫ z in K, f z i * φ z i)) :=
    tendsto_integral_mul_bounded hr hrfin
      (memLp_pi_iff.mp hf i) (fun n ↦ memLp_pi_iff.mp (hfs n) i) (hvalue i) (hfc i)
  have hIntegralExpand {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
      {pw : ParabolicPoint → ℝ} {fw : ParabolicPoint → Vec3}
      (hw : IsSuitableWeakSolutionData Ω I q w Dw pw fw) :
      (∫ z in K, frameMomentumDensity w Dw pw fw φ z) =
        -(∑ i, ∫ z in K, w z i * timePartial (fun x ↦ φ x i) z) -
          (∑ i, ∑ j, ∫ z in K, w z i * w z j * spatialPartial (fun x ↦ φ x i) j z) +
          (∑ i, ∑ j, ∫ z in K, Dw z i j * spatialPartial (fun x ↦ φ x i) j z) -
          (∑ i, ∫ z in K, pw z * spatialPartial (fun x ↦ φ x i) i z) -
          (∑ i, ∫ z in K, fw z i * φ z i) := by
    have hTI := momentum_timeTerm_integrableOn_of_data hw hK hKsub hφ
    have hNI := momentum_nonlinearTerm_integrableOn_of_data hw hK hKsub hφ
    have hVI := momentum_viscousTerm_integrableOn_of_data hw hK hKsub hφ
    have hPI := momentum_pressureTerm_integrableOn_of_data hw hK hKsub hφ
    have hFI := momentum_forceTerm_integrableOn_of_data hw hK hKsub hφ
    unfold frameMomentumDensity
    rw [integral_sub
      (f := fun z ↦ -(∑ i, w z i * timePartial (fun x ↦ φ x i) z) -
        (∑ i, ∑ j, w z i * w z j * spatialPartial (fun x ↦ φ x i) j z) +
        (∑ i, ∑ j, Dw z i j * spatialPartial (fun x ↦ φ x i) j z) -
        pw z * ∑ i, spatialPartial (fun x ↦ φ x i) i z)
      (g := fun z ↦ ∑ i, fw z i * φ z i) (((hTI.neg.sub hNI).add hVI).sub hPI) hFI,
      integral_sub
        (f := fun z ↦ -(∑ i, w z i * timePartial (fun x ↦ φ x i) z) -
          (∑ i, ∑ j, w z i * w z j * spatialPartial (fun x ↦ φ x i) j z) +
          (∑ i, ∑ j, Dw z i j * spatialPartial (fun x ↦ φ x i) j z))
        (g := fun z ↦ pw z * ∑ i, spatialPartial (fun x ↦ φ x i) i z)
        ((hTI.neg.sub hNI).add hVI) hPI,
      integral_add
        (f := fun z ↦ -(∑ i, w z i * timePartial (fun x ↦ φ x i) z) -
          (∑ i, ∑ j, w z i * w z j * spatialPartial (fun x ↦ φ x i) j z))
        (g := fun z ↦ ∑ i, ∑ j, Dw z i j * spatialPartial (fun x ↦ φ x i) j z)
        (hTI.neg.sub hNI) hVI,
      integral_sub
        (f := fun z ↦ -(∑ i, w z i * timePartial (fun x ↦ φ x i) z))
        (g := fun z ↦ ∑ i, ∑ j, w z i * w z j * spatialPartial (fun x ↦ φ x i) j z)
        hTI.neg hNI,
      integral_neg]
    have huTI (i : Fin 3) := (velocity_component_integrableOn_compact_of_data hw hK hKsub i)
    have hwtime (i : Fin 3) : IntegrableOn
        (fun z ↦ w z i * timePartial (fun x ↦ φ x i) z) K volume := by
      obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction
        (component_mem_spaceTimeTestFunction hφ i)
      exact (huTI i).mul_bdd (contDiff_timePartial
        (component_mem_spaceTimeTestFunction hφ i).1).continuous.aestronglyMeasurable
        (Eventually.of_forall hC)
    have hwpair (i j : Fin 3) : IntegrableOn
        (fun z ↦ w z i * w z j * spatialPartial (fun x ↦ φ x i) j z) K volume := by
      obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction
        (component_mem_spaceTimeTestFunction hφ i) j
      exact (velocity_pair_integrableOn_compact_of_data hw hK hKsub i j).mul_bdd
        ((spatialPartial_contDiff
          (component_mem_spaceTimeTestFunction hφ i).1 j).continuous.aestronglyMeasurable)
        (Eventually.of_forall hC)
    have hwgrad (i j : Fin 3) : IntegrableOn
        (fun z ↦ Dw z i j * spatialPartial (fun x ↦ φ x i) j z) K volume := by
      obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction
        (component_mem_spaceTimeTestFunction hφ i) j
      exact (gradient_entry_integrableOn_compact_of_data hw hK hKsub i j).mul_bdd
        ((spatialPartial_contDiff
          (component_mem_spaceTimeTestFunction hφ i).1 j).continuous.aestronglyMeasurable)
        (Eventually.of_forall hC)
    have hwpressure (i : Fin 3) : IntegrableOn
        (fun z ↦ pw z * spatialPartial (fun x ↦ φ x i) i z) K volume := by
      obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction
        (component_mem_spaceTimeTestFunction hφ i) i
      exact (pressure_integrableOn_compact_of_data hw hK hKsub).mul_bdd
        ((spatialPartial_contDiff
          (component_mem_spaceTimeTestFunction hφ i).1 i).continuous.aestronglyMeasurable)
        (Eventually.of_forall hC)
    have hwforce (i : Fin 3) : IntegrableOn (fun z ↦ fw z i * φ z i) K volume := by
      obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction
        (component_mem_spaceTimeTestFunction hφ i)
      exact (force_component_integrableOn_compact_of_data hw hK hKsub i).mul_bdd
        (component_mem_spaceTimeTestFunction hφ i).1.continuous.aestronglyMeasurable
        (Eventually.of_forall hC)
    simp only [Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hwtime i),
      integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum Finset.univ (fun j _ ↦ hwpair i j)),
      integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum Finset.univ (fun j _ ↦ hwgrad i j)),
      integral_finsetSum Finset.univ (fun i _ ↦ hwpressure i),
      integral_finsetSum Finset.univ (fun i _ ↦ hwforce i)]
    simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ hwpair _ j),
      integral_finsetSum Finset.univ (fun j _ ↦ hwgrad _ j)]
  have hlimit : Tendsto
      (fun n ↦ ∫ z in K, frameMomentumDensity (us n) (Ds n) (ps n) (fs n) φ z) atTop
      (𝓝 (∫ z in K, frameMomentumDensity u Du p f φ z)) := by
    simp_rw [hIntegralExpand (hsols _).toData, hIntegralExpand hdata]
    exact (((tendsto_finsetSum Finset.univ (fun i _ ↦ hT i)).neg.sub
      (tendsto_finsetSum Finset.univ (fun i _ ↦
        tendsto_finsetSum Finset.univ (fun j _ ↦ hN i j)))).add
      (tendsto_finsetSum Finset.univ (fun i _ ↦
        tendsto_finsetSum Finset.univ (fun j _ ↦ hV i j)))).sub
      (tendsto_finsetSum Finset.univ (fun i _ ↦ hP i)) |>.sub
      (tendsto_finsetSum Finset.univ (fun i _ ↦ hF i))
  have hDomEq (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
      (pw : ParabolicPoint → ℝ) (fw : ParabolicPoint → Vec3) :
      (∫ z in spaceTimeSet Ω I, frameMomentumDensity w Dw pw fw φ z) =
        ∫ z in K, frameMomentumDensity w Dw pw fw φ z := by
    have hoff (z : ParabolicPoint) (hz : z ∉ K) : frameMomentumDensity w Dw pw fw φ z = 0 :=
      frameMomentumDensity_eq_zero_off_tsupport w Dw pw fw hz
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz ↦ hoff z (fun hmem ↦ hz (hKsub hmem))),
      setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
  have hnzero (n : ℕ) :
      (∫ z in K, frameMomentumDensity (us n) (Ds n) (ps n) (fs n) φ z) = 0 := by
    rw [← hDomEq]
    exact ((hsols n).2.2.2.2.2.2.2.1 φ hφ).2
  have hzeroLimit : Tendsto
      (fun n ↦ ∫ z in K, frameMomentumDensity (us n) (Ds n) (ps n) (fs n) φ z)
      atTop (𝓝 0) := by
    simp_rw [hnzero]
    exact tendsto_const_nhds
  have hzero := tendsto_nhds_unique hlimit hzeroLimit
  refine ⟨?_, (hDomEq u Du p f).trans hzero⟩
  exact momentum_integrand_integrableOn_of_data hdata hφ

end FluidSingularSets
