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
| Divergent reciprocal weights at every finite depth | Proved | IteratedLogSeries |
| Affine change of scale index | Proved | IteratedScaling |
| Persistent recurrence forces divergent weighted cost | Proved scalar implication | PersistentActivity, WeightedActivity, IteratedActivity |
| Critical Sobolev estimate for weak gradients | Proved with a lower-order term | CriticalSobolev |
| Mixed-gradient cost controlled by dissipation | Proved for actual solutions | MixedGradient |
| Remove lower-order term by mean subtraction | Open | Critical Poincare development |
| Pressure decomposition and mixed-gradient PDE recurrence | Open | Reuse CKN pressure theory, assemble new estimates |
| Descendant Carleson bounds imply the dyadic embedding | Proved, finite and infinite families | CarlesonEmbedding, CountableCarleson |
| Growth and descendant count give coefficient bounds | Proved scalar implication | FrostmanCarleson |
| Mass-ratio stopping and trace summation | Proved, finite and infinite families | TraceLayerCake, MassRatioStopping |
| Time integration and concrete dissipation coefficients | Open assembly | Integrated trace development |
| Parabolic dyadic partitions and laminarity | Proved | ParabolicDyadic |
| Adjacent interval containment | Proved | AdjacentIntervals |
| Shifted product grids and cylinder comparison | Open assembly | Shifted grid development |
| Gauge Frostman measure on a persistent compact set | Open | New measure construction needed |
| Finite trace excludes a persistent set of positive mass | Proved abstract implication | ActivityTrace |
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

Hölder regularity implies local essential boundedness, as proved in RegularityBridge.
The converse under suitability remains open. The same module proves a CKN epsilon
criterion for the independently specified Hölder convention and cubic charge decay
under a local essential bound.

Comparator's development check currently matches the independent statements and
definitions, then rejects `sorryAx` from the two unfinished proof bodies. This is not a
passing Comparator result. The secure Linux check and the pinned full Palomar workflow
must pass after proof completion. The project has not been submitted or registered.
