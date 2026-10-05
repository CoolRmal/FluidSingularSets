module

public import comparators.Solution

/-!
# Reusing the Caffarelli–Kohn–Nirenberg library

The pinned upstream comparator solution transports the raw CKN solution class to ordinary
Euclidean coordinates. Its `CKNChallenge.LocalWeakNSESolution` is exactly the independently
restated solution class in this project's Challenge. Its public declarations include
`CKNChallenge.epsilonRegularityL3`, `CKNChallenge.epsilonRegularityGradient`, and
`CKNChallenge.caffarelliKohnNirenberg`.

The last theorem proves ordinary one-dimensional parabolic Hausdorff nullity. The logarithmic
gauge conclusion and the all-scale charge needed for box dimension require additional proofs.
-/
