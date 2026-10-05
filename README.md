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

for each compact interior set. The logarithmic family being added is

$$
h_k(r)=r\prod_{i=1}^{k}[\log^{\circ i}(1/r)]^2,
$$

specified near zero, where all factors are positive, and extended to larger radii.

**The two main proof bodies are unfinished. This project has not passed Comparator
and has not been registered on Palomar.** A successful development build includes
intentional Challenge placeholders; it does not certify the two results.

Completed supporting results include persistent-activity divergence, logarithmic
gauge properties, finite-mass packing estimates, and the reduction from a uniform
ball charge to upper box dimension. These have no proof placeholders. The remaining
analytic obligations include the PDE scale recurrence, the dissipation trace,
gauge Frostman and parabolic grid constructions, the velocity-only regularity
criterion, pressure-gradient integrability, and accelerated-frame suitability.

The project pins Lean and Mathlib to `v4.35.0-rc2` and imports the
[Caffarelli–Kohn–Nirenberg library](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg)
at commit `c26903f8e38b7b5a4594c80892e51b0599e8fd82`. Its comparator bridge supplies
the independently stated local suitable-solution class and proves ordinary CKN
partial regularity for it. Ordinary one-dimensional Hausdorff nullity does not
by itself prove either requested strengthening.

`Challenge.lean` independently states the targets with Mathlib-only definitions.
`Solution.lean` assembles the proof-side declarations and currently contains two
explicit proof goals. `comparator.json` permits only `propext`, `Quot.sound`, and
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
