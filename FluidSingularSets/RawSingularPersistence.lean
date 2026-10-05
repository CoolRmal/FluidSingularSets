module

public import FluidSingularSets.ActualEnergyControl
public import FluidSingularSets.RegularSet

/-!
# The physical singular set in the native parabolic coordinates

The coordinate pullback preserves the actual solution, compact interior localizations,
and the combined cubic velocity-pressure charge. The uniform small-scale singular-point
lower bound is transported together with closure containment in the solution domain.
-/

@[expose] public section

open Set MeasureTheory CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

noncomputable section

namespace FluidSingularSets

/-- The independently defined physical singular set in native parabolic coordinates. -/
def rawPhysicalSingularSet (Ω : Set Space) (I : Set ℝ) (u : SpaceTime → Space) :
    Set ParabolicPoint :=
  CKNChallenge.parabolicToEuclideanHomeomorph.symm '' CKNChallenge.singularSet Ω I u

/-- A compact interior localization of the physical singular set in native coordinates. -/
def rawCompactSingularSet (Ω : Set Space) (I : Set ℝ) (u : SpaceTime → Space)
    (K : Set SpaceTime) : Set ParabolicPoint :=
  CKNChallenge.parabolicToEuclideanHomeomorph.symm '' (CKNChallenge.singularSet Ω I u ∩ K)

/-- The pulled-back physical domain is exactly the raw CKN product domain. -/
theorem rawSpaceTime_preimage_domain (Ω : Set Space) (I : Set ℝ) :
    CKNChallenge.parabolicToEuclideanHomeomorph ⁻¹' (Ω ×ˢ I) =
      CKN.spaceTimeSet (CKNChallenge.rawSpace Ω) I := by
  ext z
  rfl

/-- Membership in the pulled singular set is membership after the coordinate map. -/
theorem mem_rawPhysicalSingularSet {Ω : Set Space} {I : Set ℝ}
    {u : SpaceTime → Space} {z : ParabolicPoint} :
    z ∈ rawPhysicalSingularSet Ω I u ↔
      CKNChallenge.parabolicToEuclideanHomeomorph z ∈ CKNChallenge.singularSet Ω I u := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Homeomorph.apply_symm_apply] using hw
  · intro hz
    exact ⟨CKNChallenge.parabolicToEuclideanHomeomorph z, hz,
      CKNChallenge.parabolicToEuclideanHomeomorph.symm_apply_apply z⟩

/-- Compact localized singular sets remain compact under the coordinate homeomorphism. -/
theorem isCompact_rawCompactSingularSet {Ω : Set Space} {I : Set ℝ}
    (u : SpaceTime → Space) {K : Set SpaceTime} (hK : IsCompact K) (hKsub : K ⊆ Ω ×ˢ I) :
    IsCompact (rawCompactSingularSet Ω I u K) :=
  (isCompact_singularSet_inter u hK hKsub).image
    CKNChallenge.parabolicToEuclideanHomeomorph.symm.continuous

/-- The native localized singular set consists of interior points of the raw domain. -/
theorem rawCompactSingularSet_subset_domain {Ω : Set Space} {I : Set ℝ}
    (u : SpaceTime → Space) (K : Set SpaceTime) :
    rawCompactSingularSet Ω I u K ⊆ CKN.spaceTimeSet (CKNChallenge.rawSpace Ω) I := by
  rintro z ⟨w, hw, rfl⟩
  rw [← rawSpaceTime_preimage_domain]
  simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hw.1.1

/-- A localized pulled-back singular set is contained in the full pulled-back singular set. -/
theorem rawCompactSingularSet_subset_singular {Ω : Set Space} {I : Set ℝ}
    (u : SpaceTime → Space) (K : Set SpaceTime) :
    rawCompactSingularSet Ω I u K ⊆ rawPhysicalSingularSet Ω I u :=
  image_mono inter_subset_left

/-- The actual unforced physical solution gives an unforced integrable CKN solution. -/
theorem raw_unforced_suitableWeakSolutionIntegrable
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0} (hq : 5 / 2 < (q : ℝ))
    (sol : CKNChallenge.LocalWeakNSESolution Ω I q) (hf : sol.f = 0) :
    CKN.IsSuitableWeakSolutionIntegrable (CKNChallenge.rawSpace Ω) I (q : ℝ)
      (CKNChallenge.pullVelocity sol.u) (CKNChallenge.pullGradient sol.Dxu)
      (CKNChallenge.pullScalar sol.p) (fun _ ↦ 0) := by
  have hraw := CKN.isSuitableWeakSolution_iff_integrable.mp
    (CKNChallenge.rawSuitableWeakSolution hq sol)
  have hzero : CKNChallenge.pullVelocity sol.f = (fun _ ↦ 0) := by
    ext z
    simp [CKNChallenge.pullVelocity, hf]
  rwa [hzero] at hraw

/-- At every pulled-back physical singular point, all sufficiently small raw cylinders
have a uniform positive actual charge and closure inside the solution domain. -/
theorem raw_singular_symmetric_l3_activity_eventually
    (q : ℝ≥0) (hq : 5 / 2 < (q : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Space} {I : Set ℝ}
      (sol : CKNChallenge.LocalWeakNSESolution Ω I q), sol.f = 0 →
      ∀ z ∈ rawPhysicalSingularSet Ω I sol.u,
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
        ε ≤ rawSymmetricL3Activity (CKNChallenge.pullVelocity sol.u)
          (CKNChallenge.pullScalar sol.p) z r ∧
        closure (rawSymmetricL3Cylinder z r) ⊆
          CKN.spaceTimeSet (CKNChallenge.rawSpace Ω) I := by
  obtain ⟨ε, hε, hpositive⟩ := singular_symmetric_l3_activity_eventually q hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I sol hf z hz
  have hsing := mem_rawPhysicalSingularSet.mp hz
  have hfpoint : ∀ a, sol.f a = 0 := by
    intro a
    simpa only [Pi.zero_apply] using congrFun hf a
  obtain ⟨R₁, hR₁, hcharge⟩ := hpositive sol hfpoint
    (CKNChallenge.parabolicToEuclideanHomeomorph z) hsing
  obtain ⟨R₂, hR₂, hdomain⟩ := exists_symmetricCylinder_domain_radius
    sol.isOpenSpace sol.isOpenTime hsing.1
  refine ⟨min R₁ R₂, lt_min hR₁ hR₂, ?_⟩
  intro r hr hrR
  constructor
  · rw [rawSymmetricL3Activity_pull_eq]
    exact (hcharge r hr (hrR.trans (min_le_left _ _))).le
  · rw [closure_rawSymmetricL3Cylinder, ← rawSpaceTime_preimage_domain]
    exact preimage_mono (hdomain r hr (hrR.trans (min_le_right _ _)))

/-- Cubic-force-exponent data provides the compact raw singular set and all the genuine
solution and persistence inputs used in its localization. -/
theorem exists_raw_compact_singular_persistence
    {Ω : Set Space} {I : Set ℝ} (sol : CKNChallenge.LocalWeakNSESolution Ω I 3)
    (hf : sol.f = 0) {K : Set SpaceTime} (hK : IsCompact K) (hKsub : K ⊆ Ω ×ˢ I) :
    CKN.IsSuitableWeakSolutionIntegrable (CKNChallenge.rawSpace Ω) I 3
      (CKNChallenge.pullVelocity sol.u) (CKNChallenge.pullGradient sol.Dxu)
      (CKNChallenge.pullScalar sol.p) (fun _ ↦ 0) ∧
    IsCompact (rawCompactSingularSet Ω I sol.u K) ∧
    rawCompactSingularSet Ω I sol.u K ⊆ CKN.spaceTimeSet (CKNChallenge.rawSpace Ω) I ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ rawCompactSingularSet Ω I sol.u K,
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
        ε ≤ rawSymmetricL3Activity (CKNChallenge.pullVelocity sol.u)
          (CKNChallenge.pullScalar sol.p) z r ∧
        closure (rawSymmetricL3Cylinder z r) ⊆
          CKN.spaceTimeSet (CKNChallenge.rawSpace Ω) I := by
  have hq : 5 / 2 < ((3 : ℝ≥0) : ℝ) := by norm_num
  obtain ⟨ε, hε, hpersist⟩ := raw_singular_symmetric_l3_activity_eventually 3 hq
  refine ⟨raw_unforced_suitableWeakSolutionIntegrable hq sol hf,
    isCompact_rawCompactSingularSet sol.u hK hKsub,
    rawCompactSingularSet_subset_domain sol.u K, ε, hε, ?_⟩
  intro z hz
  exact hpersist sol hf z (rawCompactSingularSet_subset_singular sol.u K hz)

end FluidSingularSets
