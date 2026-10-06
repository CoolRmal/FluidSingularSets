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
| Projected local energy for actual smooth harmonic corrections | Proved from the original suitable momentum, divergence, weak gradient and energy equations; the nonsmooth limit is also complete | ProjectedEnergyAlgebra, SmoothProjectedLocalEnergy |
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
| Genuine scaled pressure localization and decay | Proved affine harmonic transport, literal centered averages, actual nonlinear local harmonic remainders and radius-five-halves pressure decay | BallHarmonicPressureDecay |
| Actual suitable pressure decay on balls | Proved physical pressure harmonicity/localized oscillation on a common full time set directly from suitability | SuitableBallPressureHarmonic |
| Pressure gradient on arbitrary local boxes | Proved joint measurable L⁵ᐟ⁴ pressure derivatives using finite native pressure patches with the original time interval preserved | LocalBoxPressureForces |
| Actual projected weak gradients and divergence | Proved original-plus-harmonic slice weak gradients, divergence, joint energy and genuine weighted mixed Sobolev bounds | SuitableProjectedWeakGradient |
| True endpoint mixed physical pressure curves | Proved actual nonlinear time L¹ spatial L² and viscous time L² spatial L² bounds by the literal endpoint velocity/gradient costs | StokesPressureMixedBounds |
| Actual harmonic derivative source bounds | Proved correction and Hessian bounds by the actual original spatial L² velocity class on a common full time set | ProjectedHarmonicSourceBounds |
| Actual spatial mean pressure pairings | Proved genuine mean integrability, true constant mixed classes and zero pairing against actual zero-integral spatial tests | MixedSpatialMeans |
| Velocity-only single-scale regularity criterion | Open | Formalize cited Li–Wang–Zhou result |
| Uniform singular lower charge from the velocity-only criterion | Proved conditional reduction, with actual terminal/frame geometry | BoxChargeReduction |
| Actual centered pressure restriction | Proved bounded linear restriction and literal mean subtraction, exact oscillation moments, and all time exponents | BallCenteredPressureOperator |
| Physical and native unit pressure compatibility | Proved actual equality of affine energy transports, Stokes pressures, and nonlinear/viscous curves | BallStokesUnitCompatibility |
| True projected spatial velocity energy | Proved finite corrected energy and explicit source S1 bounds, with genuine good slices and time L∞ classes | SuitableProjectedVelocityEnergy |
| Pressure energy on arbitrary local boxes | Proved actual spatial L² pressure and time L⁵ᐟ⁴ energy-force classes while preserving the original time interval | LocalBoxPressureEnergy |
| Energy force classes on arbitrary local boxes | Proved full-ball H1 to L⁶, genuine quartic time interpolation and all actual energy force classes on the original time interval | LocalBoxEnergyForces |
| Actual time-energy extraction | Proved scalar Lebesgue differentiation, true backward cutoff limits, product integration and essential energy supremum from literal tested inequalities | TestedTimeEnergy |
| Genuine nonsmooth energy at almost every time | Proved actual energy/dissipation/RHS integrability, real smooth ramp tests and literal time-energy extraction directly from suitability | SuitableProjectedTimeEnergy |
| Actual harmonic evolution on original intervals | Proved complete momentum evolution, true gradient-free force primitive, AC representative and genuine smooth force approximants on the original local interval | LocalBoxProjectedTime |
| Genuine projected energy on original local intervals | Proved nonsmooth local energy directly from suitable source data and actual supported tests without a fixed extra future margin | LocalBoxProjectedLocalEnergy |
| Actual time energy on original intervals | Proved true ramp tests and AE-time energy/dissipation inequality for the actual interval and primitive | LocalBoxProjectedTimeEnergy |
| Native endpoint pressure moments | Proved exact native/physical time norms and actual nonlinear L¹/viscous L² bounds from endpoint source costs | UnitBallPressureMixedBounds |
| Genuine nested pressure oscillation moments | Proved true mean-removed harmonic decay, time integration and a universal contraction with the actual suitable L⁶ source | UnitBallPressureOscillationMoment |
| Quantitative actual tested time energy | Proved simultaneous energy essential supremum and full dissipation bounds from the literal bounded tested right hand side | TestedTimeEnergyBounds |
| Actual smooth cutoff with arbitrary future cap | Proved compact supported sixth-power tests and upper time-derivative estimates independent of future cap width | ProjectedCylinderCutoff |
| Actual source classes on every compact interior | Proved true subtype/product measure transport and genuine suitable velocity, gradient, pressure and original-interval slice classes for every interior radius | FullBallProjectedSources |
| True harmonic operators on arbitrary compact interiors | Proved full-ball representative linearity and actual continuous gradient, value, Hessian and dual-kernel operators with margin-dependent bounds | FullBallHarmonicOperators, FullBallHarmonicValues |
| Actual original-interval projected weak gradients | Proved genuine ambient potential, Hessian, weak gradient and divergence with the supplied force primitive and original interval | LocalBoxProjectedWeakGradient |
| Actual harmonic and pressure cutoff errors | Proved literal component pairings, genuine external source norms and Young bounds retaining the full-ball gradient term | ProjectedCutoffErrors |
| Genuine mean-pressure cancellation on original intervals | Proved actual spatial mean integrability and exact tested pressure decomposition into nonlinear and viscous pairings | SuitablePressureMeanPairings |
| Actual weighted-energy convection bound | Proved true cubed-cutoff energy supremum and mixed Sobolev interpolation with energy exponent five sixths | WeightedProjectedConvection |
| Genuine full-ball projected gradients and energy classes | Proved actual ambient potential, correction, Hessian, weak gradients, divergence and original-interval joint/mixed classes on every compact interior | FullBallProjectedWeakGradient, FullBallProjectedData |
| Exact full-ball pressure mean cancellation | Proved literal whole-ball pressure decomposition and arbitrary-interior original-interval signed pressure pairings | FullBallPressureMeanPairings |
| Genuine spatial smoothing at arbitrary radii | Proved true C² compact extension, harmonic convolution, uniform derivative limits and actual smooth dual kernels with literal evaluation identities | FullBallSpatialSmoothApprox, FullBallSpatialKernels |
| Sharp actual mixed viscous pressure pairing | Proved original-interval time L² pairing and Young absorption into full-ball gradient and endpoint velocity costs | ProjectedViscousMixedPairing |
| Genuine weighted Sobolev with original velocity error | Proved cubed-cutoff L²/L⁶ estimate retaining the literal weighted derivative and an unweighted velocity square error | WeightedProjectedSobolev |
| Genuine uniformly bounded full-ball smooth operators and limits | Proved actual compact pressure/gradient/Hessian operators, finite uniform bounds and genuine fixed-force and moving compact-trajectory convergence | FullBallHessianSmoothApprox, FullBallSmoothLimits |
| Exact full-ball joint differential smoothing | Proved actual smooth pressure, gradient and Hessian fields, exact force-primitive time derivative and harmonic/divergence identities on arbitrary interiors | FullBallJointSmoothApprox |
| True projected mixed source and Sobolev control | Proved actual full-ball source controls for projected L²/L⁶ and weighted cubed-cutoff mixed cost on original intervals | FullBallProjectedSixControl |
| Genuine full-ball cutoff pressure bounds | Proved actual weighted nonlinear-pressure pairings and viscous Young bounds with the literal original gradient/endpoint costs at arbitrary interior radii | FullBallProjectedPressurePairings |
| Genuine bounded radius iteration with boundary costs | Proved explicit nested-radius contraction and source polynomial with all forcing powers up to thirty two; actual PDE one-step premise remains | ProjectedRadiusIteration32 |
| True suitable full-ball smooth source sequence and local energy inequality | Proved actual source-derived joint approximations and the projected local energy inequality on every compact interior radius and exact original interval | FullBallSuitableSmoothApprox, FullBallProjectedLocalEnergy |
| Genuine summed pressure and harmonic cutoff errors | Proved actual pressure mean cancellation, finite component sums, signed error bounds and quantitative original-source harmonic Hessian control | FullBallHarmonicCutoffErrors, FullBallProjectedSignedErrors |
| Genuine arbitrary physical projection-ball rescaling | Proved suitable-solution and local-box pullback, literal native unit ball and original interval endpoint transport | ProjectedBallRescaling |
| Genuine original-interval tested projected time energy | Proved actual tested density integrability, backward cutoff extraction and almost-everywhere energy plus dissipation inequality on every compact interior radius | FullBallProjectedTimeEnergy |
| True original gradient transfer and harmonic joint source control | Proved literal Hessian joint square bound from the endpoint source and unit-cutoff transfer from genuine projected to original gradient density | FullBallProjectedGradientControl |
| Exact cutoff RHS and genuine canonical second derivative bound | Proved literal separated-test derivative/error-family identity and a universal sixth-cutoff Laplacian bound retaining the fourth spatial weight | FullBallCylinderEnergyRhs, CanonicalBallCutoffSecondBounds |
| True endpoint and gradient rescaling at every physical projection radius | Proved actual inverse-radius scaling of extended mixed velocity, gradient norm and coordinate-square gradient costs without finiteness assumptions | ProjectedBallMixedRescaling |
| True margin-dependent harmonic source coefficients | Proved exact inverse-cube velocity bound, inverse-sixth Hessian bound and actual projected slice coefficient control | FullBallMarginCoefficients |
| Genuine native projected right hand side | Proved actual native joint integrability and exact compact/native/iterated integral identities | FullBallNativeEnergyRhs |
| Actual time-weighted projected energies | Proved true square-root time weights, finite actual energy supremum, original-interval mixed classes and monotonicity | FullBallTimeWeightedEnergy, FullBallTestedEnergyBounds |
| True time-weighted gradient transfer and Sobolev | Proved actual weighted gradient density control and Sobolev retaining the time weight on dissipation | FullBallTimeWeightedGradientControl, TimeWeightedProjectedSobolev |
| Genuine time-weighted pressure, harmonic and convection estimates | Proved literal error pairings and sharp five-sixths convection absorption input with the actual tested energy supremum | FullBallTimeWeightedPressureErrors, TimeWeightedProjectedConvection |
| Genuine endpoint mixed velocity finiteness | Proved the full-ball original L²-time/L⁶-space moment finite directly from the actual suitable energy and weak gradient slices | FullBallVelocityMomentFinite |
| True tested dissipation and original-gradient transfer | Proved exact compact/native dissipation transport and the original gradient bound on every actual unit plateau | FullBallDissipationTransport, FullBallTestedOriginalGradient |
| Actual time and Laplacian source errors | Proved genuine integrability and endpoint costs, retaining only an upper derivative bound in the signed time cost | FullBallCutoffSourceErrors |
| Literal native error and pressure integral decomposition | Proved five actual signed error families, deriving joint pressure integrability from the actual RHS and connecting the true mixed pressure bound by Fubini | FullBallNativeErrorDecomposition, FullBallTestedRhsDecomposition |
| Genuine weighted convection and margin powers | Proved the literal time-weighted flux bound and actual reciprocal source-coefficient gap powers | FullBallTimeWeightedConvection, FullBallEndpointGapBounds |
| Genuine tested suitable Caccioppoli inequality | Proved from the actual projected LEI and literal integrable signed RHS, with endpoint Young absorption and no assumed energy bound | FullBallTestedRhsBounds, FullBallEndpointAbsorption, FullBallTestedCaccioppoli |
| Actual terminal-independent canonical gradient estimate | Proved with genuine compact admissible cutoffs, exact unit plateaus and three-quarter original-gradient contraction | FullBallCanonicalCutoffData, FullBallGradientMomentFinite, FullBallCanonicalCaccioppoli |
| Actual energy extraction for joint space-time tests | Proved true essential energy supremum and full coordinate dissipation for arbitrary genuine nonnegative supported tests | FullBallGeneralTestedEnergy |
| Genuine whole source polynomial gap bound | Proved from actual operator coefficients and canonical cutoff budgets, with no terminal-cap dependence | FullBallEndpointCoefficientBounds |
| True terminal cylinder exhaustion | Proved countable increasing exhaustion and null terminal-slice transport to the literal CKN cylinder | TruncatedCylinderExhaustion |
| Actual joint-test pressure mean cancellation | Proved genuine spatial slices and exact centered nonlinear/viscous pressure pairings for arbitrary joint smooth tests and arbitrary time-dependent means | FullBallJointPressureTest |
| Genuine terminal-free cylinder Caccioppoli | Proved the actual full backward cylinder contraction by countable terminal exhaustion | FullBallCylinderCaccioppoli |
| True physical-radius iteration | Proved the literal original coordinate-gradient bound on the three-quarter cylinder by the endpoint velocity polynomial, without an outer-gradient term | NestedProjectionBallRescaling, FullBallRadiusCaccioppoli |
| Actual joint energy error integrability and decomposition | Proved all four genuine Gaussian error families integrable and the exact native/compact/iterated integral decomposition | FullBallJointEnergyErrors, FullBallJointErrorIntegrability, FullBallJointRhsDecomposition |
| True scalar mixed pressure-test energy control | Proved actual time L∞ spatial L² class bounds from the literal Euclidean slice supremum | ProjectedScalarEnergyBound |
| Genuine fixed-projection iteration quantities and pressure decay | Defined actual projected energy and pressure quantities and proved native same-box centered nonlinear decay | FullBallPressureOscillationDecay |
| Actual viscous pressure oscillation moment | Proved centered harmonic time L² spatial L² decay with radius power five halves from the full coordinate-gradient source | FullBallViscousOscillationMoment |
| Genuine compact Gaussian tests and signed heat bounds | Proved actual supported admissible tests, inner lower bounds, gradient bounds and signed terminal-independent heat upper bounds | ProjectedGaussianCutoff |
| Genuine Gaussian heat energy estimate | Proved actual projected energy finiteness, true Tonelli square-moment control and the signed inverse-radius heat bound | ProjectedGaussianHeatError |
| Actual Gaussian pressure flux classes and pairings | Proved genuine nonlinear L¹ and viscous L² native pressure classes, centered mixed pairings and inverse-square Gaussian flux control from the actual projected slice energy | FullBallJointPressureEnergy, CenteredPressureEnergyPairing, ProjectedGaussianPressureEnergy, FullBallNativePressureClasses, ProjectedGaussianPressurePairings |
| True initial projected energy at the rescaled native radius | Proved actual quarter-cylinder slice and dissipation bounds, countable terminal exhaustion, and the three-quarter rescaled initial energy bound solely from the original endpoint velocity polynomial | TerminalSliceEnergyExhaustion, ProjectedPlateauEnergy, FullBallInitialTestedEnergy, FullBallInitialProjectedEnergy, FullBallInitialScaledEnergy |
| Genuine arbitrary-radius weak vector Sobolev | Proved actual same-ball L⁶ membership and the uniform gradient plus inverse-radius velocity norm bound | BallH1Vector |
| True nonlinear pressure absorption | Proved the actual seven-sixths pressure factor is absorbed into a small linear energy term and a three-halves remainder | ProjectedPressureIterationAbsorption |
| Genuine shrinking-scale nonlinear trapping | Proved shrinking-factor, positive energy-threshold and source-smallness selection, invariant nonlinear trapping and its affine geometric envelope | EndpointShrinkingIteration |
| Actual whole-ball mixed weak Sobolev and nonlinear projected source | Proved genuine same-ball mixed energy, literal projected quartic and cubic moments, and normalized cubic control by energy power three halves | BallH1MixedEnergy, FullBallProjectedPressureSource |
| Genuine arbitrary-test inner energy comparison | Proved actual slice supremum and dissipation comparison from a geometric test lower bound | FullBallGeneralEnergyComparison |
| Actual Gaussian inner energy extraction | Proved literal uniform tested RHS controls inner slice energy, dissipation and normalized energy by countable terminal exhaustion | ProjectedGaussianEnergyExtraction |
| Genuine localized Gaussian RHS | Proved exact four actual cylinder-error decomposition and centered nonlinear/viscous pressure error bound on the original interval | FullBallJointPatchRhs, ProjectedGaussianRhs |
| Actual Gaussian convection and harmonic flux | Proved global integrability, literal endpoint source moments, normalized energy/source costs and genuine harmonic Young absorption | ProjectedGaussianFluxErrors, ProjectedGaussianSourceEnergy, ProjectedGaussianConvectionEnergy, ProjectedGaussianHarmonicYoung |
| True finite iteration pressure algebra | Proved actual finite iteration quantity, normalized two-thirds pressure control and exact seven-sixths pressure-energy product | FullBallIterationPressureAlgebra |
| Genuine interpolation and gradient limit | Proved actual all-radius projected energy interpolation, harmonic correction mass vanishes and the original CKN gradient limsup is bounded by twice the eventual projected energy budget | ProjectedRadiusInterpolation, ProjectedGradientLimit |
| Actual nonlinear pressure source and contraction | Proved genuine original-velocity quartic source, normalized nonlinear-pressure contraction at power three halves, real finite conversion and initial quarter pressure source bound | FullBallNonlinearPressureSource, FullBallNonlinearPressureDecay, FullBallNonlinearPressureReal |
| Genuine normalized Gaussian pressure absorption | Proved literal convective seven-sixths and harmonic viscous flux bounds, true Young absorption and the actual combined pressure RHS cost | ProjectedGaussianConvectivePressureAbsorption, ProjectedGaussianViscousPressureAbsorption, ProjectedGaussianPressureRhs |
| True Gaussian nonpressure RHS aggregation | Proved exact cylinder/global error identities and universal heat, convection and harmonic cost for the actual tested solution | ProjectedGaussianNonpressureRhs |
| Actual projected-energy CKN regularity budget | Proved universal positive eventual and geometric projected-energy budgets imply true origin regularity | ProjectedGradientCriterion |
| Common bounded velocity on compact regular sets | Proved a finite-subcover AE velocity bound from actual local Hölder regularity | CompactRegularVelocity |
| Genuine actual Gaussian energy step | Proved the literal tested RHS and normalized smaller projected-energy estimate solely from actual suitable data and proved error bounds | FullBallGaussianEnergyStep |
| True universal energy-pressure coefficient recurrence | Proved fixed absorption parameter, cost positivity, universal finite coefficient and scalar coarsening to the nonlinear scale recurrence | ProjectedGaussianRecurrenceCoefficients, ProjectedGaussianScalarRecurrence |
| Actual initial full iteration quantity | Proved the genuine radius-three-quarter scaled initial projected energy plus nonlinear pressure power is bounded solely by the original velocity polynomial | FullBallInitialEndpointQuantity |
| Requested compact box bound conditional on the analytic criterion | Proved actual finite pressure-gradient charge localization, singular reverse charge and exact isometric transport to the independently stated upper box dimension | CompactBoxCriterion |
| Genuine full suitable-solution iteration step | Proved actual finite iteration identity and full nonlinear energy-pressure recurrence using only suitability and literal native sources | FullBallEndpointIterationStep |
| True positive endpoint source threshold | Proved positive shrink ratio, nonlinear trap below the CKN interpolation budget, and original-source smallness controlling every step | EndpointRecurrenceSmallness |
| Discharge the velocity-only criterion in the actual box target | Open | Apply actual recurrence trapping and join origin regularity to a fixed inner cylinder |
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
