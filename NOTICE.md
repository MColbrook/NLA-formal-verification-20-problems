# Notices and attribution

This repository contains the substantive Lean development accompanying
*Numerical Linear Algebra, Explained: Twenty Problem Resolutions*, by
Matthew J. Colbrook and George Stepaniants. Both are the confirmed human
formalization authors and responsible maintainers for this release.

The repository owner authorized release under Apache-2.0 on 19 November 2026,
with existing third-party notices preserved. The standard text is in
[LICENSE](LICENSE). This release decision applies to contributions within the
owner's authority; it does not replace the original terms or attribution of
reused code, dependencies or cited mathematical sources. This notice supplies
attribution and provenance and does not modify any licence.

## Original formalizations and paper extensions

The development builds on problem-specific Lean projects from
[OpenProblemsInNLA](https://github.com/ajt60gaibb/OpenProblemsInNLA) and later
paper-specific proof extensions in
[big_NLA](https://github.com/MColbrook/big_NLA). Preserve the original author,
copyright and modification notices in copied and adapted source files.
Many original files state Copyright (c) 2026 George Stepaniants and are
released under Apache-2.0. Substantial OpenAI Codex assistance is disclosed in
[formalization.yaml](formalization.yaml), alongside the limits of agent review.
AI assistance does not replace human authorship or responsibility.

The original source snapshots include:

- Fourteen problem projects at OpenProblemsInNLA commit
  `0689db001ddc4c54f2652ed4b13b753637fef700`.
- IV-02, IV-04, MD-06 and TR-04 refreshes at
  `c15a0f5963155e66dc08daa29a6713320c59c23a`.
- IE-21 proof source `1eb284b84ecc0d3c958d022b3e020be7fa111391` and
  IE-22 proof source `c45f9ccef20a2fa5cc4b988e93d4173dab853362`.
- Subsequent imports, compatibility ports, relocations and proof extensions
  identified in the retained source provenance ledgers. These later records
  supplement rather than supersede the snapshot history above.

The new release reorganizes selected proof closures into seventeen projects,
with MF-07 grouped under MF-05, RA-03 under RA-02, and IV-02 under IV-04.
Compatibility and submission-interface edits are new changes to the earlier
source tree. Historical verification receipts concern their bound source
bytes; they do not certify those new changes.

Component licence texts are retained under [LICENSES/](LICENSES/).
[The attribution inventory](docs/attribution-inventory.json) binds the original
source paths and licence text hashes and records their packaged locations.
The prior no-package-grant notices are preserved as historical evidence;
the new release authorization must not be represented as a grant that existed
in those earlier snapshots.

## Complexitylib

The IV-04 proof closure includes an attributed compatibility port of material
from [SamuelSchlesinger/complexitylib](https://github.com/SamuelSchlesinger/complexitylib)
at `67ca3985c6027758b77356a049d4313e8d18158e`, licensed under Apache-2.0.
Original source notices include:

- Copyright (c) 2025 and 2026 Samuel Schlesinger.
- Copyright (c) 2026 Bolton Bailey.
- Copyright (c) 2026 Christian Reitwiessner.

Their original authorship notices and the upstream source/port/relocation
manifest remain with this component. Its licence is also retained at
[LICENSES/upstream-projects/IV-04/NLA/IV04/Complexitylib/LICENSE](LICENSES/upstream-projects/IV-04/NLA/IV04/Complexitylib/LICENSE).

## Mathlib-derived sources and dependencies

A Mathlib-derived spectral functional-calculus file in the RA-09 development
retains Copyright (c) 2024 Jon Bannon and its Apache-2.0 notice. Preserve this
and every other applicable copied source notice.

The new Lean 4.35.0 port depends on canonical Mathlib and the exact packages
in its manifest; it has no LeanCert dependency. Lean, Mathlib and those
packages retain their upstream licences, copyright and attribution. Historical
archives preserve the earlier LeanCert-based proofs, receipts and dependency
notices. The seven inherited numerical certificate statements are unchanged;
their new proofs are ported to Mathlib arithmetic and explicit exponential
bounds. The seventh is NLA.MI19.strict_scalar_gap, whose closed rational
statement is unchanged and whose historical LeanCert kernel-trust proof is
replaced by norm_num. Explicitly logged probability-map, finite-PMF and other
API compatibility edits also preserve the mathematical statements. No implicit
axioms or native-execution trust are introduced by these proof replacements;
ordinary full-source Lean 4.35.0 compilation and compiled selected-axiom
queries passed. Official Comparator, NanoDa and Palomar verification remain
pending the authors' later submission.

The manifests specify exact revisions. This repository does not claim
authorship of upstream dependencies or relicense them by linking to their
interfaces. Dependency caches and build outputs are not part of this source
release.

## Verification tooling

The prior NLA verification driver is credited to George Stepaniants,
Copyright (c) 2026, under Apache-2.0. Its original
[tool notice](LICENSES/verification-tools/NOTICE.md) and
[Apache text](LICENSES/verification-tools/LICENSE-APACHE-2.0) are preserved.
That notice identifies the pinned Forsythe integration and the original
Lean FRO Comparator and lean4export authors and terms. Landrun is identified
there under MIT, Copyright (c) 2025 Armin ranjbar; its own licence must
accompany any redistributed Landrun source. No Landrun implementation is
relicensed by the root Apache declaration. Merely preserving this tooling
provenance is not a claim that those tools were run on the new source tree.

## Mathematical sources

The manuscript and original problem collection are cited separately in
[formalization.yaml](formalization.yaml). Mathematical authorship, problem
proposers, prior proofs and explanatory contributions retain their individual
credits. The author's book, manuscript text and reference PDFs are not
licensed as repository software by this notice. No endorsement by an upstream
author, institution, software author or Palomar is implied.
