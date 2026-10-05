# Proof status

The target family is

$$
h_k(r)=r\prod_{i=1}^k[\log^{\circ i}(1/r)]^2
$$

near zero, for every fixed finite natural number $$k$$. The box target is local:

$$
\overline{\dim}_{B,\mathrm{par}}(S\cap K)\le25/23
$$

for every compact interior patch $$K$$. The solution class is unforced, local,
three-dimensional and suitable, as independently specified in `Challenge.lean`.

The following tables distinguish the proved gauge theorem and supporting statements from the open box
proof. A theorem about abstract coefficients is used only after deriving its hypotheses
from the solution. Those hypotheses are not added to either target theorem.

| Gauge argument | Status | Modules |
| --- | --- | --- |
| Independent solution class and parabolic measure | Proved bridge to CKN | Specification, CKNBridge |
| Zero logarithmic factors for actual solutions | Proved | CKNBaseline |
| Gauge identities, small-radius formula and limit zero | Proved | Gauge, IteratedGauge |
| Small-radius monotonicity and doubling | Proved | LogGaugeRegularity |
| Successive factors dominate a repeated deepest factor | Proved near zero | LogProductComparison |
| Literal repeated-deepest gauge singular-set nullity | Proved for every finite depth | RepeatedLogGauge |
| Divergent reciprocal weights at every finite depth | Proved | IteratedLogSeries |
| Affine change of scale index | Proved | IteratedScaling |
| Persistent recurrence forces divergent weighted cost | Proved scalar implication | PersistentActivity, WeightedActivity, IteratedActivity |
| Critical Sobolev estimate for weak gradients | Proved with a lower-order term | CriticalSobolev |
| Mixed-gradient cost controlled by dissipation | Proved for actual solutions | MixedGradient |
| Remove lower-order term by mean subtraction | Proved for genuine local weak gradients | CriticalPoincare |
| Singular points have positive symmetric charge at every small scale | Proved for actual solutions | ScaleRegularity |
| Finite real velocity-pressure activity | Proved for actual solutions | RealCharge |
| Mean-subtracted cubic charge and mixed-gradient pressure decay | Proved for actual solutions | MixedPressure |
| Velocity and pressure decay on arbitrary smaller time windows | Proved for actual solutions | MixedVelocityDecay |
| Combined real velocity-pressure window decay | Proved for actual solutions | SymmetricMixedDecay, CombinedWindowDecay |
| Symmetric charge decay with the actual mixed oscillation source | Proved for actual solutions | SymmetricChargeDecay |
| Local energy controlled by symmetric activity | Proved for actual solutions | ActualEnergyControl |
| Actual backward-cylinder dissipation controlled by symmetric activity | Proved with admissible terminal time | GradientEnergyControl |
| Mixed-gradient PDE recurrence | Proved for actual suitable solutions, with uniform dyadic contraction | FixedScaleRecurrence |
| Descendant Carleson bounds imply the dyadic embedding | Proved, finite and infinite families | CarlesonEmbedding, CountableCarleson |
| Growth and descendant count give coefficient bounds | Proved scalar implication | FrostmanCarleson |
| Actual slice-cell masses give descendant coefficient bounds | Proved, including infinite series | SpatialTraceCoefficients |
| Finite cube families satisfy the concrete spatial Carleson bound | Proved from cell growth | SpatialTraceCarleson |
| Joint measurability of actual activity and mixed-gradient masses | Proved for actual solutions | ActivityMeasurability |
| Mass-ratio stopping and trace summation, including zero masses | Proved, finite and infinite families | TraceLayerCake, MassRatioStopping, MassRatioTrace |
| Time integration of the spatial embedding | Proved from measurable coefficients | IntegratedCarleson |
| Instantiate concrete dissipation coefficients | Proved, including measurable representatives and real finite sums | ConcreteTraceCarleson, ConcreteTraceAE |
| Parabolic dyadic partitions and laminarity | Proved | ParabolicDyadic |
| Adjacent interval containment | Proved | AdjacentIntervals |
| Sixteen shifted grids and parabolic ball containment | Proved | ShiftedParabolicDyadic |
| Exact refinement, descendant count and measurable time selector | Proved | ParabolicRefinement |
| Spatial and time-integrated embedding in adjacent grids | Proved | ShiftedCarleson |
| Concrete cost and mass-ratio identities | Proved, including zero masses | TraceCost |
| Compare cylinder and box dissipation costs | Proved for actual suitable solutions, including zero masses | CylinderCellComparison, SymmetricCellMixedComparison, TraceActivityComparison |
| Positive gauge content gives uniform finite tree capacity and atomic measures | Proved abstract construction | GaugeFrostman |
| Compact weak limit preserving eventual open-ball bounds | Proved abstract limit construction | GaugeFrostmanLimit |
| Actual cell tree, grouped atomic masses and uniform ball bounds | Proved | ParabolicFrostmanGeometry, GaugeFrostmanApproximations |
| Gauge Frostman measure on any compact set of positive gauge measure | Proved under local gauge regularity | GaugeFrostmanConstruction |
| Frostman measure for every finite iterated-log gauge | Proved | IteratedFrostman |
| Frostman ball growth gives actual refined-cell growth | Proved with one level cutoff | FrostmanCellGrowth |
| Full integrated spatial coefficient series is finite | Proved from actual Frostman growth | FrostmanTraceEmbedding |
| Finite trace excludes a persistent set of positive mass | Proved abstract implication | ActivityTrace |
| Actual mass-ratio trace is summable | Proved from Frostman growth and finite gradient energy | ConcreteMassRatioTrace |
| Pointwise cell costs are summable in all sixteen grids | Proved almost everywhere for the Frostman measure | PointwiseGradientTrace |
| Exact divergent weights on dyadic arithmetic progressions | Proved at every positive logarithmic depth | DyadicLogWeights |
| Cell activity is finite, and zero dissipation gives zero activity | Proved from actual quadratic energy | CellMixedDissipation |
| Transfer every gauge between parabolic carriers | Proved on every set | GaugeTransport |
| Compact interior nullity implies full-domain nullity | Proved | CompactLocalization |
| Apply all pieces to the solution, then exhaust the domain | Proved for every finite depth | GaugeTraceExclusion, CompactGaugeNullity, SuitableGaugeNullity, Solution |

| Box argument | Status | Modules |
| --- | --- | --- |
| Exact exponent balance and moving-scale displacement | Proved scalar implications | MovingScale |
| Uniform ball charge implies covering and dimension bounds | Proved | Packing, BoxFromCharge, BoxDimension |
| Compactness of the localized singular set | Proved | RegularSet |
| Pressure-gradient local integrability | Proved actual weak gradient in local L^(5/4) | PressureGradientFiveFourths |
| Weighted Poincare around the actual normalized mean | Proved from suitable slices | WeightedVelocityPoincare |
| Canonical normalized smooth weight and universal scaled bounds | Proved, including the actual mixed Poincare estimate | NormalizedWeightedCutoff |
| Actual mean evolution, AC representative and L^(3/2) acceleration | Proved | WeightedMeanMotion |
| Quantitative scale-explicit bound for actual mean motion | Proved from suitability and actual pressure gradient | MeanMotionBound |
| Finite compact density including actual pressure gradients | Proved | CompactBoxDensity |
| Actual local pressure-gradient choice independence and common charge domination | Proved with joint almost-everywhere equality | PressureGradientUniqueness |
| Moving-frame geometry, smooth tests and genuine weak divergence/momentum | Proved | AcceleratedFrame |
| Pointwise relative-energy expansion | Proved | AcceleratedEnergyAlgebra |
| Moving-frame actual local data for continuous or time L^(3/2) acceleration | Proved | AcceleratedData, AcceleratedPressureLp |
| Genuine relative local energy inequality and full smooth-frame suitability | Proved | AcceleratedEnergy, SmoothAcceleratedSuitability |
| Strong local convergence under uniform moving translations | Proved for actual solution fields | AcceleratedLpStability |
| Smooth approximation of the actual AC mean, acceleration and path | Proved with common supports and bounds | MeanSmoothApprox |
| Compact common source tube for moving approximants | Proved from compactness and uniform convergence | AcceleratedTubeLimit |
| Strong Holder products and actual tested integral convergence | Proved | StrongLpProducts, StrongLpIntegrands |
| Actual divergence, momentum and local energy pass to strong limits | Proved with genuine limit data | WeakEquationLimit, LocalEnergyLimit |
| Strong affine acceleration pressure and mean-subtracted velocity limits | Proved | AcceleratedPressureLimit |
| Actual moving relative velocity endpoint cost | Proved with normalized bound at exponent 25/23 | MovingRelativeVelocity |
| Full suitability for the actual AC mean frame | Proved, with arbitrary spatial offsets and anchor times | AbsolutelyContinuousFrame |
| Full-neighborhood regularity transfer through actual moving frames | Proved without a Hölder mean hypothesis | AcceleratedRegularity |
| Strict actual mixed-cost bound persists under small terminal shifts | Proved from actual finite measurable time density | SlidingMixedCost |
| Local variational Stokes velocity and energy bound | Proved on actual completed gradient space | LocalStokesEnergy |
| Genuine zero-boundary test Poincare estimate | Proved | StokesTestPoincare |
| Actual velocity reconstruction on completed gradient space | Proved in L², with true weak gradient and test agreement | StokesEnergyVelocity |
| Weighted-gradient divergence identities and linear-source inverse | Proved for genuine smooth fields | WeightedBallDivergence |
| Genuine finite-degree polynomial inverse and smooth ball divergence field | Proved up to an explicit spatial constant | FischerPolynomial, BallPolynomialInverse, PolynomialBallDivergence |
| Identify the polynomial constant with the actual ball average | Proved, including zero-integral sources | BallBoundaryApproximation, PolynomialBallMeanInverse |
| Actual zero-boundary polynomial fields belong to the Hilbert completion | Proved by strong gradient approximation | HilbertBallBoundary, PolynomialBallEnergy |
| Uniform polynomial ball divergence inverse | Proved, with norm-square constant 3 independent of degree | PolynomialBallRellich |
| Hilbert pressure recovery from genuine bounded divergence lifts | Proved, including actual integrable test equation | StokesPressureRecovery |
| Extend genuine bounded Hilbert lifts from dense data | Proved with a continuous linear right inverse | DenseHilbertLifts |
| Actual polynomial density in ball L² and its mean-zero subspace | Proved | PolynomialBallDensity, PolynomialBallMeanDensity |
| Bounded divergence right inverse on all actual mean-zero ball L² data | Proved with operator norm at most 2 | BallDivergenceInverse |
| Actual bounded mean-zero Stokes pressure for arbitrary energy forces | Proved with physical sign, norm bound and literal weak test equation | UnitBallStokesPressure |
| Actual continuous pressure operators and gradient fixing | Proved with bounded pointwise estimates, idempotence and mean-zero uniqueness | RealHilbertDual, StokesPressureProjection, UnitBallPressureProjection |
| Actual harmonic ball pressure for divergence-free source data | Proved from genuine Hessian testing on the completion | StokesGradientTest, UnitBallPressureHarmonic |
| First derivatives of actual C¹ harmonic representatives are weakly harmonic | Proved from actual local integration by parts | LocalHarmonicDerivatives |
| Actual continuous vector force with literal source equation | Proved from actual reconstructed velocity | StokesVectorForce, StokesVectorForceLinear |
| Actual C² harmonic pressure representatives | Proved with true weak derivative identities | HarmonicC2, UnitBallPressureC2, StokesVectorPressureC2 |
| Actual pressure gradient and Hessian bounds | Proved with universal force/source constants | UnitBallPressureBounds, StokesVectorPressureBounds |
| Actual convective and viscous ball pressures | Proved from genuine tensors, with literal equations and raw-gradient convention | StokesNonlinearPressure |
| Genuine spatial Lp class curves and mixed time moments | Proved from joint measurable data, with actual Tonelli identities | SliceLpMeasurable, SliceLpMoments |
| Actual centered pressure in the energy dual | Proved from suitable pressure and weak gradients, with finite time 5/4 moment | PressureEnergyDual, PressureEnergyForces |
| Actual nonlinear and viscous pressure time classes | Proved at time 4/3 and 2 from actual suitable energy data | StokesPressureTimeIntegrability, StokesPressureCurves |
| Canonical harmonic gradient and Hessian operators | Proved with actual Riesz pairings, joint gradient measurability and weak derivatives | UnitBallHarmonicGradient, UnitBallHarmonicGradientPairing, UnitBallHarmonicGradientMeasurable, LocalHessianCalculus, UnitBallHarmonicHessian |
| Energy-dual evolution from true compact suitable momentum tests | Proved for actual integrable forces with literal pairings | StokesMomentumTime, WeakTimePressure |
| Actual suitable pressure-correction weak time equation | Proved from ordinary unforced suitability with true force and pressure classes | ActualPressureCurve, SuitableProjectedPressureTime |
| Actual harmonic gradient on energy-dual forces | Proved via true orthogonal projection, with exact source compatibility | UnitBallHarmonicForceGradient, UnitBallHarmonicForceExtension, UnitBallHarmonicGradientCompatibility |
| Actual harmonic-gradient time evolution and AC representative | Proved from suitable momentum, true closed-subspace differentiation and Bochner primitives | WeakDerivativeGradientFree, WeakContinuousTimePrimitive, SuitableHarmonicGradientTime |
| Genuine weak-gradient, convection, momentum and pressure correction cancellations | Proved for actual smooth corrections and compact energy tests | HarmonicCorrectionCrossTerms, SmoothProjectedDivergence, SmoothHarmonicMomentum, SmoothProjectedPressureCancellation |
| Smooth harmonic spatial and square energy cancellations | Proved from actual suitable weak gradients and true compact-test integration by parts | SmoothHarmonicEnergy, HarmonicScalarEnergyCancellation |
| Actual harmonic-preserving time approximations | Proved by smoothing genuine force derivatives and their exact operator-image primitives, with uniform field and strong derivative convergence | HarmonicTimeSmoothApprox |
| Actual harmonic-preserving spatial approximations | Proved by smoothing the canonical pressure with true harmonicity, divergence and derivative convergence on interior balls | HarmonicSpatialSmoothApprox |
| Actual scalar pressure-value operator and uniform mixed class limits | Proved with the genuine force norm bound, Lipschitz evaluation kernel, and derived good spatial slices | CanonicalForcePressureValues, UniformMixedSlices |
| Actual joint smooth harmonic pressure corrections | Proved with exact time-gradient compatibility, interior harmonicity/divergence and quantitative smoothing errors | HarmonicJointSmoothApprox |
| Actual force Hessian operator and strong operator-curve limits | Proved with true force norm bounds and Bochner dominated convergence, including varying input curves | UnitBallHarmonicForceHessian, StrongOperatorCurveLimits |
| Projected local energy for actual smooth harmonic corrections | Proved from the original suitable momentum, divergence, weak gradient and energy equations; actual nonsmooth correction limit remains | ProjectedEnergyAlgebra, SmoothProjectedLocalEnergy |
| Actual time L∞ velocity and harmonic correction bounds | Proved quantitatively from the genuine S1 slice energy bound | SuitableVelocityTimeBound |
| Genuine pressure-velocity integral limits | Proved for true spatial L² classes with time L¹/L∞ bounds and strong convergence | StrongMixedPairings, MixedSlicePairings |
| Actual endpoint cubic interpolation | Proved with constant one and powers 3/4, 1/4, 3/4 of energy, time measure and mixed cost | EndpointVelocityInterpolation |
| Genuine full projected-energy strong limit | Proved for the actual energy density, pressure pairing, true spatial classes, and uniform tested velocity limits | ProjectedEnergyStrongLimit, MixedWeightedVelocity |
| Endpoint absorption and bounded radius iteration | Proved with explicit geometric radii and contraction; actual cutoff estimate remains | ProjectedCaccioppoliAlgebra |
| Actual full-ball harmonic force pressure | Proved with whole-ball C² representatives and explicit derivative bounds on every interior ball | FullBallHarmonicRegularity |
| Actual suitable harmonic correction smooth sequence | Proved with full-force AE primitive agreement, common force bounds, exact joint differential identities, uniform gradients, and strong true pressure classes | SuitableHarmonicSmoothApprox |
| Uniform true Hessian smoothing along compact force trajectories | Proved with a common bounded force operator and genuine fixed-force and moving-trajectory convergence | HarmonicHessianSmoothApprox |
| Actual tensor-pressure Poisson and viscous harmonic identities | Proved from the genuine variational projection, literal velocity products and actual weak derivatives/divergence | StokesTensorPressurePoisson |
| Genuine endpoint projected convection estimates | Proved with actual spatial/time Hölder interpolation, integrability, and a bounded cutoff gradient | ProjectedCutoffConvection |
| Arbitrary-ball Stokes projection | Proved actual physical compact-test equations, zero mean and uniform norm four through affine energy transport | BallStokesPressureProjection |
| Genuine harmonic pressure decay | Proved actual centered L² pressure oscillation with radius exponent five halves from weak harmonicity | HarmonicPressureOscillation |
| Local suitable viscous pressure harmonicity | Proved on a common full time set in arbitrary local boxes using the actual weak gradient and divergence | SuitableViscousPressureHarmonic |
| Genuine bounded joint slice classes | Proved actual spatial L² good slices and time L∞ class bounds from joint L∞ on finite spatial measure | JointTopSliceClasses |
| Actual cubed-cutoff Sobolev estimate | Proved global weak product gradients and L⁶ control by the actual weighted gradient and cutoff energy | ProjectedCutoffSobolev |
| Sharp weighted projected convection | Proved literal sixth-cutoff convection integrability and bound with the weighted cubed-cutoff velocity L⁶ moment | ProjectedWeightedConvection |
| Actual nonsmooth suitable projected local energy | Proved from suitability and actual compact tests; all joint approximation, good-slice, mixed-pressure and strong-limit inputs are discharged | SuitableProjectedLocalEnergy |
| Genuine weighted mixed cutoff energy | Proved from actual Sobolev slices by Tonelli, with canonical radius-gap cutoffs and suitable-data wrappers | ProjectedCutoffMixedEnergy |
| Actual arbitrary-ball pressure sources | Proved true tensor/nonlinear Poisson, viscous harmonicity and radius-uniform Stokes source bounds | BallStokesPressureSources |
| Quadratic mixed source pairing | Proved actual source L¹ spatial L² control and integrable pressure/velocity pairing with a quadratic mixed source bound | MixedQuadraticSources |
| Actual projected pressure identification | Proved the energy pressure equals the literal nonlinear and viscous Stokes pressures plus the original spatial average | SuitableProjectedPressureIdentification |
| Velocity-only single-scale regularity criterion | Open | Formalize cited Li–Wang–Zhou result |
| Uniform singular lower charge from the velocity-only criterion | Proved conditional reduction, with actual terminal/frame geometry | BoxChargeReduction |
| Discharge the velocity-only criterion in the actual box target | Open | Projected energy and its estimates needed |
| Apply charge bound to every compact interior patch | Open | Solution |

For actual suitable solutions, local Hölder regularity and local essential boundedness
are equivalent at every interior point, as proved in BoundedRegularity. VelocityOnlyBridge
proves that bounded velocity makes the actual normalized pressure charge tend to zero;
Caccioppoli and CKN regularity complete the converse. RegularityBridge also proves a CKN epsilon
criterion for the independently specified Hölder convention and cubic charge decay
under a local essential bound.

The gauge-only configuration `comparator-gauges.json` passed the local unsandboxed
development comparison at `1180af7`, then the [secure Linux comparison](https://github.com/CoolRmal/FluidSingularSets/actions/runs/37336630111)
at public proof checkpoint `151a12f`. Both independent gauge statements matched,
and Lean paranoid, lean4lean, NanoDa, con-leche, con-ron and the default Lean kernel
accepted their proofs using only the permitted standard axioms. The Linux run used
the required bubblewrap sandbox. The full `comparator.json` still rejects `sorryAx`
from the remaining box proof body. The pinned full Palomar workflow must pass
after proof completion. The project has not been submitted or registered.
