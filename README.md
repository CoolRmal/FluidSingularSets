# FluidSingularSets

Lean formalization for the interior singular set of unforced
three-dimensional suitable weak Navier–Stokes solutions.

The targets use the parabolic metric

$$
d((x,t),(y,s))=\max\{|x-y|,\sqrt{|t-s|}\}.
$$

The two requested conclusions are logarithmic gauge Hausdorff nullity, including
the family of successive logarithmic factors, and the local upper box bound

$$
\overline{\dim}_{B,\mathrm{par}}(S\cap K)\le\frac{25}{23}
$$

for each compact interior set. The proved logarithmic family is

$$
h_k(r)=r\prod_{i=1}^{k}[\log^{\circ i}(1/r)]^2,
$$

specified near zero, where all factors are positive, and extended to larger radii.
The literal repeated-deepest interpretation is also proved:

$$
\widetilde h_k(r)=r[\log^{\circ k}(1/r)]^{2k}.
$$

Its actual Hausdorff measure is bounded by that of the successive-product gauge.


**Both requested conclusions are proved, including every finite gauge depth.
Full Comparator verification and official Palomar mechanical preflight passed
for published source snapshot `dd3ae61`, now registered as
[PALOMAR-2026-10-06-000006, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-06-000006&version=1).**
See the [verification record](docs/verification.md). Challenge contains the intentional
independent statement placeholders; Solution and the supporting proofs have none.

The gauge proof constructs a genuine Frostman measure from positive gauge measure,
derives the scale recurrence directly from suitability, and proves the concrete
mass-ratio gradient trace. The reciprocal logarithmic weights diverge at every finite
depth, contradicting positive Frostman mass on the singular set. Compact interior
localization and exact isometric transport give the full-domain conclusion.
All these supporting proofs contain no placeholders or custom axioms.

At public proof checkpoint `151a12f`, the gauge-only configuration
`comparator-gauges.json` passed the [secure Linux comparison](https://github.com/CoolRmal/FluidSingularSets/actions/runs/37336630111)
with bubblewrap, including Lean paranoid, lean4lean, NanoDa, con-leche, con-ron
and the default Lean kernel. This verifies both gauge targets against their
independent statements. The completed full comparison and official Palomar mechanical
preflight also verified the box proof.

For the box bound, the actual pressure gradient at exponent 5/4, the normalized
weighted Poincaré estimate, the absolutely continuous weighted mean, and the
finite compact density measure are proved. Full suitability and full-neighborhood
regularity transfer for the actual accelerating mean frame are also proved.
The moving relative velocity has the required endpoint mixed-norm bound.

The local Stokes construction now includes the genuine zero-boundary energy
completion, velocity reconstruction, a bounded divergence inverse on every
mean-zero ball L² datum, and a bounded continuous mean-zero pressure operator.
Its pressure is weakly harmonic for genuine divergence-free vector sources.
Actual C² representatives and uniform interior gradient and Hessian estimates
are proved. The actual nonsmooth projected local energy inequality is proved, including
its analytic cancellations, genuine harmonic pressure primitive, and strong
limit. Quantitative weighted cutoff estimates and pressure decay are also
proved. The full-ball pressure values, gradients, and Hessians now define actual
bounded linear operators on arbitrary compact interiors, with quantitative
boundary-margin estimates. Original-interval mean-pressure cancellation and
the sharp weighted-energy convection estimate are also proved. Genuine Gaussian
energy extraction and nonlinear pressure contraction give the actual shrinking-scale
recurrence. Its positive source threshold traps every scale below the CKN regularity
budget, with finiteness and the reciprocal interpolation factor retained.

The proved velocity-only criterion gives a common essential velocity bound on a
fixed inner cylinder. Genuine quarter-box rescaling and a compact regularity cover
make its radius independent of the solution and terminal time. The criterion yields
the singular lower charge at exponent 25/23, including the forward terminal shift
and common compact pressure-gradient measure. Packing and covering then give the
requested upper box dimension on every compact interior patch.
See [the proof status](docs/proof-status.md).

The project pins Lean and Mathlib to `v4.35.0-rc2` and imports the
[Caffarelli–Kohn–Nirenberg library](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg)
at commit `c26903f8e38b7b5a4594c80892e51b0599e8fd82`. The adapted comparator bridge supplies
the independently stated local suitable-solution class and proves ordinary CKN
partial regularity for it. Ordinary one-dimensional Hausdorff nullity does not
by itself prove either requested strengthening.

`Challenge.lean` independently states the targets with Mathlib-only definitions.
`Solution.lean` assembles the proved gauge family, its original logarithmic-square
corollary, and the local upper box-dimension bound.
`comparator.json` permits only `propext`, `Quot.sound`, and
`Classical.choice`. No custom axioms or substituted hypotheses stand in for either
main conclusion.

Build the completed library and standalone statements with:

```sh
lake exe cache get
lake build
```

The registration gates passed for the registered snapshot and can be reproduced with:

```sh
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The secure comparator script requires Linux and bubblewrap. The separate macOS
development script is explicitly unsandboxed and is not a Palomar preflight.
The pinned official workflow in `.github/workflows/palomar-preflight.yml` supplies
the complete mechanical check. Registration follows the current
[Palomar submission process](https://submit.palomar-registry.org/).

Palomar's automated review by `codex:gpt-6-sol`, completed on
`2026-10-06T04:08:24Z`, reported no blocking problems or requested changes.
The registration and review apply to the source snapshot above; later documentation
updates do not change that attribution. Source manuscripts are in `papers/`.
These are research drafts; external human mathematical peer review is not claimed.
The responsible maintainer is
Yongxi (Aaron) Lin (`CoolRmal`). See `formalization.yaml` for current status.

Released under Apache-2.0. Reused CKN material retains its original authorship
and license; cited mathematical sources retain their own rights.
