# Verification record

The completed formalization has passed independent Comparator CI and the official full
Palomar mechanical preflight. The approved source snapshot has been submitted to
Palomar, and its service verification also passed. Review and registration remain pending.

Both runs checked these three targets:

- `FluidSingularSets.singularSet_iteratedLogHausdorffMeasure_zero`
- `FluidSingularSets.singularSet_logSquaredHausdorffMeasure_zero`
- `FluidSingularSets.singularSet_upperBoxDimension_le`

The [independent full Comparator CI](https://github.com/CoolRmal/FluidSingularSets/actions/runs/37404871659)
verified proof commit `e4cda018f26b6c9dbb538aa9f2c2a30f98a8161e` and completed successfully.
Its transcript records acceptance by con-ron, NanoDa, and Lean's default kernel for the
export containing all three targets.

The [official full Palomar preflight](https://github.com/CoolRmal/FluidSingularSets/actions/runs/37406563795)
verified the exact published source commit `dd3ae61ce421a634818f52a6e11a8b78dd1bfc97` and
completed successfully. This commit differs from the independently checked proof commit
only in the preflight workflow file.

The run's `mechanical-report-fluidproof01` artifact contains a schema-2 mechanical report
with the following results:

| Field | Verified value |
| --- | --- |
| Source repository | `CoolRmal/FluidSingularSets` |
| Source commit | `dd3ae61ce421a634818f52a6e11a8b78dd1bfc97` |
| Status | `pass` |
| Stage | `complete` |
| Errors | `[]` |
| Execution profile | `palomar-standard-v1` |
| Checked at | `2026-10-06T03:30:31Z` |

The report permits only `propext`, `Quot.sound`, and `Classical.choice` and lists the three
targets above. Its verifier and Challenge provenance audit succeeded.

The report includes one nonblocking advisory: the configured Challenge source exceeds
the preferred 32 KiB / 300-line review surface. The report's status is `pass`, with no errors.

After the approved intake, [Palomar's own verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/37409636115)
also passed for the exact source commit `dd3ae61ce421a634818f52a6e11a8b78dd1bfc97`.
Its mechanical report records `status: pass`, `stage: complete`, and no errors,
checked at `2026-10-06T03:49:07Z`. All three targets passed with acceptance by
con-ron, NanoDa, and Lean's default kernel.

The service report rates Challenge provenance as `high`, records Mathlib as its
only direct import, and lists no untrusted sources. Challenge has 322 lines and
14,633 bytes; the line count accounts for the nonblocking review-surface advisory.
Palomar's private review and registration remain pending.
