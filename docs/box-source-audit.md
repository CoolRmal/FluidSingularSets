# Automated source review of the box proof

An independent proof agent reviewed the completed support path on 2026-10-06.
This is an automated source review, not external human mathematical peer review.
It found no concrete mathematical, finiteness or circularity defect. Lean and
the external Comparator remain the mechanical proof checks.

The conclusion is upper **parabolic** box dimension on every compact interior
patch. The gauge theorem covers the full interior singular set. Countable
compact exhaustion does not extend an upper box bound to arbitrary unbounded
sets, so no such extension is claimed.

The independent [specification](../FluidSingularSets/Specification.lean) defines
ordinary local energy, distributional momentum and the local energy inequality,
then the actual AE Hölder regular set. Its box dimension uses external parabolic
coverings and the infimum of polynomial covering growth rates.

The review checked these substantive steps:

- [Raw suitability](../FluidSingularSets/RawSingularPersistence.lean) is derived
  from the independently supplied solution data. The uniform analytic criterion
  is proved internally, rather than added as a target hypothesis.
- [PressureGradientFiveFourths](../FluidSingularSets/PressureGradientFiveFourths.lean)
  constructs an actual measurable spatial weak pressure gradient in L⁵ᐟ⁴.
  [Uniqueness](../FluidSingularSets/PressureGradientUniqueness.lean) identifies fresh
  gradients with the fixed finite patch charges.
- [CompactBoxDensity](../FluidSingularSets/CompactBoxDensity.lean) constructs a
  finite common pressure-gradient measure and a common positive compact-patch radius.
- [Packing](../FluidSingularSets/Packing.lean) proves packing and covering finiteness
  before converting extended natural covering numbers to ordinary naturals.
- The exponent 25/23 follows from the proved weighted mean-motion estimate and
  [MovingScale](../FluidSingularSets/MovingScale.lean)'s exact scaling identity.
- [BoxChargeReduction](../FluidSingularSets/BoxChargeReduction.lean) uses a strict
  positive future-time shift smaller than the inner cylinder's time depth. The
  original terminal singular point then lies in an open regularity neighborhood.
- [FullBallScaledEndpointSequence](../FluidSingularSets/FullBallScaledEndpointSequence.lean)
  proves each actual iteration quantity finite and bounds extended projected
  energy by the real sequence, avoiding any use of the value of an infinite
  quantity under `toReal`.
- [EndpointOriginRegularity](../FluidSingularSets/EndpointOriginRegularity.lean)
  retains the reciprocal interpolation factor and the actual harmonic-gradient
  correction limit before applying CKN regularity.
- [UniformEndpointVelocityCriterion](../FluidSingularSets/UniformEndpointVelocityCriterion.lean)
  supplies a positive universal threshold and radius one eighth. Its common
  essential velocity bound may depend on the solution, as the criterion requires.
- [CompactBoxCriterion](../FluidSingularSets/CompactBoxCriterion.lean) transports
  the positive reverse charge by the exact parabolic isometry at scale one
  quarter of the covering radius, then applies the independent dimension definition.

The reviewed dependency closure contained 299 local modules with no missing
imports, import cycles, source proof holes, custom axioms, `native_decide`, or
`unsafe` declarations. No support module depends on the final box target.
The final target is the assembly of the proved criterion and compact charge theorem.
