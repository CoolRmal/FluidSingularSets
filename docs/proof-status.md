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

The following tables distinguish proved supporting statements from the two open main
proofs. A theorem about abstract coefficients is used only after deriving its hypotheses
from the solution. Those hypotheses are not added to either target theorem.

| Gauge argument | Status | Modules |
| --- | --- | --- |
| Independent solution class and parabolic measure | Proved bridge to CKN | Specification, CKNBridge |
| Zero logarithmic factors for actual solutions | Proved | CKNBaseline |
| Gauge identities, small-radius formula and limit zero | Proved | Gauge, IteratedGauge |
| Small-radius monotonicity and doubling | Proved | LogGaugeRegularity |
| Successive factors dominate a repeated deepest factor | Proved near zero | LogProductComparison |
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
| Mixed-gradient PDE recurrence | Open velocity decay and local energy assembly | New scale assembly needed |
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
| Compare cylinder and box dissipation costs | Open assembly | New trace assembly needed |
| Positive gauge content gives uniform finite tree capacity and atomic measures | Proved abstract construction | GaugeFrostman |
| Compact weak limit preserving eventual open-ball bounds | Proved abstract limit construction | GaugeFrostmanLimit |
| Actual cell tree, grouped atomic masses and uniform ball bounds | Proved | ParabolicFrostmanGeometry, GaugeFrostmanApproximations |
| Gauge Frostman measure on any compact set of positive gauge measure | Proved under local gauge regularity | GaugeFrostmanConstruction |
| Frostman measure for every finite iterated-log gauge | Proved | IteratedFrostman |
| Frostman ball growth gives actual refined-cell growth | Proved with one level cutoff | FrostmanCellGrowth |
| Full integrated spatial coefficient series is finite | Proved from actual Frostman growth | FrostmanTraceEmbedding |
| Finite trace excludes a persistent set of positive mass | Proved abstract implication | ActivityTrace |
| Transfer every gauge between parabolic carriers | Proved on every set | GaugeTransport |
| Compact interior nullity implies full-domain nullity | Proved | CompactLocalization |
| Apply all pieces to the solution, then exhaust the domain | Open | Solution |

| Box argument | Status | Modules |
| --- | --- | --- |
| Exact exponent balance and moving-scale displacement | Proved scalar implications | MovingScale |
| Uniform ball charge implies covering and dimension bounds | Proved | Packing, BoxFromCharge, BoxDimension |
| Compactness of the localized singular set | Proved | RegularSet |
| Pressure-gradient local integrability | Open | New analytic assembly needed |
| Weighted Poincare and mean-motion estimates | Open | New analytic assembly needed |
| Accelerated-frame suitability | Open | New weak-equation transport needed |
| Velocity-only single-scale regularity criterion | Open | Formalize cited Li–Wang–Zhou result |
| Uniform charge at every singular center and small radius | Open | New PDE criterion needed |
| Apply charge bound to every compact interior patch | Open | Solution |

For actual suitable solutions, local Hölder regularity and local essential boundedness
are equivalent at every interior point, as proved in BoundedRegularity. VelocityOnlyBridge
proves that bounded velocity makes the actual normalized pressure charge tend to zero;
Caccioppoli and CKN regularity complete the converse. RegularityBridge also proves a CKN epsilon
criterion for the independently specified Hölder convention and cubic charge decay
under a local essential bound.

Comparator's development check currently matches the independent statements and
definitions, then rejects `sorryAx` from the two unfinished proof bodies. This is not a
passing Comparator result. The secure Linux check and the pinned full Palomar workflow
must pass after proof completion. The project has not been submitted or registered.
