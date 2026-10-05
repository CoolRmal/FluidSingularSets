# FluidSingularSets

Lean formalization in progress for the interior singular set of unforced
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

**The gauge family is proved for every finite depth. The box-dimension proof remains
unfinished. The complete project has not passed Comparator and is not registered
on Palomar.** Challenge contains the intentional independent statement placeholders.

The gauge proof constructs a genuine Frostman measure from positive gauge measure,
derives the scale recurrence directly from suitability, and proves the concrete
mass-ratio gradient trace. The reciprocal logarithmic weights diverge at every finite
depth, contradicting positive Frostman mass on the singular set. Compact interior
localization and exact isometric transport give the full-domain conclusion.
All these supporting proofs contain no placeholders or custom axioms.

For the box bound, local velocity integrability at exponent 10/3 and the actual weak
pressure gradient at exponent 5/4 are proved. The remaining analytic steps include
weighted mean motion, accelerated-frame suitability, and the velocity-only regularity
criterion. The packing and covering reduction at exponent 25/23 is already proved.
Local essential boundedness and the formal Hölder regularity convention are also
proved equivalent for actual suitable solutions at every interior point.
See [the proof status](docs/proof-status.md) for the completed and open steps.

The project pins Lean and Mathlib to `v4.35.0-rc2` and imports the
[Caffarelli–Kohn–Nirenberg library](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg)
at commit `c26903f8e38b7b5a4594c80892e51b0599e8fd82`. The adapted comparator bridge supplies
the independently stated local suitable-solution class and proves ordinary CKN
partial regularity for it. Ordinary one-dimensional Hausdorff nullity does not
by itself prove either requested strengthening.

`Challenge.lean` independently states the targets with Mathlib-only definitions.
`Solution.lean` assembles the proved gauge family and its original logarithmic-square
corollary. Its only remaining proof placeholder is the box-dimension bound.
`comparator.json` permits only `propext`, `Quot.sound`, and
`Classical.choice`. No custom axioms or substituted hypotheses stand in for either
main conclusion.

Build the completed library and standalone statements with:

```sh
lake exe cache get
lake build
```

The following registration gates must all pass after completing the main proofs:

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

Source manuscripts are in `papers/`. These are research drafts; external
mathematical peer review is not claimed. The responsible maintainer is
Yongxi (Aaron) Lin (`CoolRmal`). See `formalization.yaml` for current status.

Released under Apache-2.0. Reused CKN material retains its original authorship
and license; cited mathematical sources retain their own rights.
