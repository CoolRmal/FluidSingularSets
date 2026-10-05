module

public import FluidSingularSets.ScaleRegularity
public import CKN.Core.Caccioppoli.Finiteness
public import CKN.Setting.Finiteness
public import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Finite real velocity-pressure activity

The local energy class makes the velocity cubic integral finite. Together with the pressure
integrability, this allows the singular-point epsilon charge to be converted from an extended
nonnegative real number to a finite real activity at every sufficiently small scale.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

noncomputable section

namespace FluidSingularSets

/-- The combined cubic velocity and three-halves pressure charge is finite on every backward
cylinder whose closure is contained in the domain of an actual suitable weak solution. -/
theorem raw_velocity_pressure_integral_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (parabolicCylinder z.1 z.2 r) ⊆ CKN.spaceTimeSet Ω I) :
    (∫⁻ a in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
        ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)) < ⊤ := by
  have hu : AEStronglyMeasurable u (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    obtain ⟨Ω', J, hbox, hcyl⟩ := CKN.exists_localBox_of_closure_subset
      hsol.1 hsol.2.1 hr hdom
    obtain ⟨hu, -, -, -, -, -, -, -, -⟩ := hsol.2.2.2.2.2.1 Ω' J hbox
    exact hu.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have humeas : AEMeasurable (fun a ↦ ENNReal.ofReal (vec3EuclideanNorm (u a)))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu).aemeasurable
  rw [lintegral_add_left' (humeas.pow_const (3 : ℝ))]
  exact ENNReal.add_lt_top.2
    ⟨(CKN.caccioppoli_velocity_integral_ne_top hsol hr hdom).lt_top,
      CKN.sws_pressure_integral_lt_top hsol hr hdom⟩

/-- Finiteness of the physical velocity-pressure charge for the independently stated local
suitable weak solution class. No forcing restriction is needed for this finiteness statement. -/
theorem velocity_pressure_integral_lt_top {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0}
    (hq : 5 / 2 < (q : ℝ)) (sol : CKNChallenge.LocalWeakNSESolution Ω I q)
    {z : SpaceTime} {r : ℝ} (hr : 0 < r)
    (hdom : closure (CKNChallenge.Q r z) ⊆ Ω ×ˢ I) :
    (∫⁻ a in CKNChallenge.Q r z,
      ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
  let ζ := CKNChallenge.parabolicToEuclideanHomeomorph.symm z
  have hζ : CKNChallenge.parabolicToEuclideanHomeomorph ζ = z :=
    CKNChallenge.parabolicToEuclideanHomeomorph.apply_symm_apply z
  have hrawdom : closure (parabolicCylinder ζ.1 ζ.2 r) ⊆
      CKN.spaceTimeSet (CKNChallenge.rawSpace Ω) I := by
    intro a ha
    have haphys := (CKNChallenge.mem_closure_cylinder_iff_mem_closure_Q hr ζ a).1 ha
    change CKNChallenge.rawSpaceTimeToEuclidean a ∈
      closure (CKNChallenge.Q r (CKNChallenge.parabolicToEuclideanHomeomorph ζ)) at haphys
    rw [hζ] at haphys
    exact hdom haphys
  have hraw := raw_velocity_pressure_integral_lt_top
    (CKN.isSuitableWeakSolution_iff_integrable.1
      (CKNChallenge.rawSuitableWeakSolution hq sol)) hr hrawdom
  rw [velocity_pressure_integral_transport sol.u sol.p ζ r, hζ] at hraw
  exact hraw

/-- The closure of a symmetric cylinder is the closed spatial ball times its closed time
interval. -/
theorem closure_symmetricL3Cylinder {r : ℝ} (hr : 0 < r) (z : SpaceTime) :
    closure (symmetricL3Cylinder z r) =
      Metric.closedBall z.1 r ×ˢ Icc (z.2 - r ^ 2) (z.2 + r ^ 2) := by
  rw [symmetricL3Cylinder, closure_prod_eq, closure_ball z.1 hr.ne',
    closure_Ioo (by nlinarith [sq_pos_of_pos hr])]

/-- Two backward cylinders of the same radius cover the symmetric cylinder. -/
theorem symmetricL3Cylinder_subset_two_backward (z : SpaceTime) {r : ℝ} (_hr : 0 < r) :
    symmetricL3Cylinder z r ⊆
      CKNChallenge.Q r z ∪ CKNChallenge.Q r (z.1, z.2 + r ^ 2) := by
  rintro a ⟨hx, htlow, hthigh⟩
  by_cases ht : a.2 ≤ z.2
  · exact Or.inl ⟨hx, htlow, ht⟩
  · refine Or.inr ⟨hx, ?_, hthigh.le⟩
    dsimp
    linarith

/-- Both backward cylinders used in the symmetric cover have closures inside the symmetric
closure. -/
theorem two_backward_closure_subset_symmetric (z : SpaceTime) {r : ℝ} (hr : 0 < r) :
    closure (CKNChallenge.Q r z) ⊆ closure (symmetricL3Cylinder z r) ∧
      closure (CKNChallenge.Q r (z.1, z.2 + r ^ 2)) ⊆
        closure (symmetricL3Cylinder z r) := by
  rw [closure_symmetricL3Cylinder hr z, CKNChallenge.closure_Q hr z,
    CKNChallenge.closure_Q hr (z.1, z.2 + r ^ 2)]
  constructor
  · rintro a ⟨hx, hlow, hhigh⟩
    exact ⟨hx, hlow, hhigh.trans (by nlinarith [sq_nonneg r])⟩
  · rintro a ⟨hx, hlow, hhigh⟩
    refine ⟨hx, ?_, hhigh⟩
    dsimp at hlow ⊢
    nlinarith [sq_nonneg r]

/-- The combined velocity-pressure charge is finite on a symmetric cylinder with closure in
the solution domain. -/
theorem symmetric_velocity_pressure_integral_lt_top {Ω : Set Space} {I : Set ℝ}
    {q : ℝ≥0} (hq : 5 / 2 < (q : ℝ)) (sol : CKNChallenge.LocalWeakNSESolution Ω I q)
    {z : SpaceTime} {r : ℝ} (hr : 0 < r)
    (hdom : closure (symmetricL3Cylinder z r) ⊆ Ω ×ˢ I) :
    (∫⁻ a in symmetricL3Cylinder z r,
      ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
  have hclosures := two_backward_closure_subset_symmetric z hr
  calc
    _ ≤ ∫⁻ a in CKNChallenge.Q r z ∪ CKNChallenge.Q r (z.1, z.2 + r ^ 2),
        ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ) :=
      lintegral_mono_set (symmetricL3Cylinder_subset_two_backward z hr)
    _ ≤ (∫⁻ a in CKNChallenge.Q r z,
          ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ)) +
        ∫⁻ a in CKNChallenge.Q r (z.1, z.2 + r ^ 2),
          ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ) :=
      lintegral_union_le _ _ _
    _ < ⊤ := ENNReal.add_lt_top.2
      ⟨velocity_pressure_integral_lt_top hq sol hr (hclosures.1.trans hdom),
        velocity_pressure_integral_lt_top hq sol hr (hclosures.2.trans hdom)⟩

/-- The dimensionless symmetric cubic velocity-pressure activity as a real number. -/
def symmetricL3Activity (u : SpaceTime → Space) (p : SpaceTime → ℝ)
    (z : SpaceTime) (r : ℝ) : ℝ :=
  (ENNReal.ofReal (r⁻¹ ^ 2) * ∫⁻ a in symmetricL3Cylinder z r,
    ‖u a‖ₑ ^ (3 : ℝ) + ‖p a‖ₑ ^ (3 / 2 : ℝ)).toReal

/-- The real activity has the ordinary scale factor `r⁻²`. -/
theorem symmetricL3Activity_eq (u : SpaceTime → Space) (p : SpaceTime → ℝ)
    (z : SpaceTime) (r : ℝ) :
    symmetricL3Activity u p z r = r⁻¹ ^ 2 *
      (∫⁻ a in symmetricL3Cylinder z r,
        ‖u a‖ₑ ^ (3 : ℝ) + ‖p a‖ₑ ^ (3 / 2 : ℝ)).toReal := by
  rw [symmetricL3Activity, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r⁻¹)]

/-- Every singular point of an unforced suitable weak solution has uniformly positive real
activity at every sufficiently small scale. All extended charges used here are finite. -/
theorem singular_symmetric_l3_activity_eventually (q : ℝ≥0) (hq : 5 / 2 < (q : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Space} {I : Set ℝ}
      (sol : CKNChallenge.LocalWeakNSESolution Ω I q), (∀ z, sol.f z = 0) →
      ∀ z ∈ CKNChallenge.singularSet Ω I sol.u,
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
        ε < symmetricL3Activity sol.u sol.p z r := by
  obtain ⟨ε, hε, hcriterion⟩ := singular_symmetric_l3_charge_lower_bound q hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I sol hf z hz
  obtain ⟨hzdom, hzsing⟩ := hz
  obtain ⟨R, hR, hdom⟩ := exists_symmetricCylinder_domain_radius
    sol.isOpenSpace sol.isOpenTime hzdom
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  have hfinite := ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := r⁻¹ ^ 2))
    (symmetric_velocity_pressure_integral_lt_top hq sol hr (hdom r hr hrR))
  have hlower := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite.ne).2
    (hcriterion sol hf z hzsing hr (hdom r hr hrR))
  rwa [ENNReal.toReal_ofReal hε.le] at hlower

end FluidSingularSets
