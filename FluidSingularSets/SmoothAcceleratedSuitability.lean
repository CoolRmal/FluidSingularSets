module

public import FluidSingularSets.AcceleratedData
public import FluidSingularSets.AcceleratedEnergy

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- An actual suitable solution stays suitable in every smooth accelerating
frame contained in its domain. The spatially affine acceleration pressure
comes from the momentum and relative-energy identities, while all data and
weak-gradient clauses come from the source solution on compact image tubes. -/
theorem suitable_smooth_accelerated_frame
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hXm : ∀ t, HasDerivAt X (m t) t) (hma : ∀ t, HasDerivAt m (a t) t)
    (hB : IsOpen B) (hJ : IsOpen J) (hJord : OrdConnected J)
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet Ω I) :
    IsSuitableWeakSolutionIntegrable B J q (acceleratedVelocity X m u)
      (acceleratedGradient X Du) (acceleratedPressure X a p) (acceleratedForce X f) := by
  have hdata := suitable_accelerated_data hsol hX.continuous hm.continuous ha.continuous
    hB hJ hJord htube
  have htube' : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I := htube
  refine ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2.1,
    hdata.2.2.2.2.2, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact suitable_accelerated_divergence hsol hX hm htube' hψ
  · intro φ hφ
    exact suitable_accelerated_momentum hsol hX hm ha hXm hma htube' hφ
  · intro ψ hψ hψnonneg
    exact suitable_accelerated_local_energy hsol hX hm ha hXm hma htube' hψ hψnonneg

end FluidSingularSets
