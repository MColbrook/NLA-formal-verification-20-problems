# Build architecture and source scope

This document records the original source inventory and the subsequent preparation of the submission folder on 19 November 2026. Its static checks are distinct from the ordinary source-build receipts in `verification/`; it is not a kernel replay or a Palomar acceptance certificate. The authoritative manuscript is the original repository's `main.tex`, SHA256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`.

## Current single-entry architecture

The current release supersedes the earlier grouping recommendation below.
There is one repository-root Palomar submission covering all twenty problems
and all 34 selected declarations. The seventeen component environments remain
as source/provenance and independent-build records; they are not registration
targets. The root Challenge contains a pruned, body-preserving union of their
mathematical statement definitions, while the root Solution imports a shared
proof library with uniquely named generic implementation modules.

The combined interface has separate compilation and axiom evidence in
`verification/combined-build-status.json` and a local statement/body comparison
record in `verification/combined-correspondence.json`. The seventeen component receipts
cannot establish that proofs coexist in one combined environment. See
`README.md`, `SUBMISSION.md`, and the root entry in `submission-index.json`
for the current layout. The remainder of this document records the historical
component staging and earlier architecture analysis.

The combined Challenge visibly resets only the local auxiliary-lemma and matcher
caches between original source units. Explicit import-all of the pinned Lean core
matcher module exposes the cache API; no project helper is imported. These
nonpersistent caches otherwise reuse generated proofs and matchers from earlier
source units, changing references inside fixed definition bodies.
The reset changes only cache state, introduces no mathematical assumptions or
axioms, and restores the original proof-owner names. The statement/body comparison remains exact.

## Historical mathematical grouping

Keep the existing proof projects separate while preparing the current-protocol statement interfaces. Seventeen proof groups cover all twenty problems: MF-05/MF-07 share one group, RA-02/RA-03 share one, and IV-02/IV-04 share one. The other fourteen problems have separate groups. This avoids unnecessary renaming and preserves declaration identities. One official Comparator configuration is one Palomar entry; split a group further if a faithful statement surface cannot fit the Challenge limits. Do not turn all 338 technical configurations into 338 research submissions by default.

The package must retain the mapping for all 53 named statements and 57 prose claim groups, as well as all twenty headline resolutions. An entry selecting only the twenty headlines does not by itself cover the whole manuscript. The IV-02 determinant theorem is proved by the shared IV-04 project, rather than by the old IV-02 scaffold.

## Exact source inventories

| Distribution | Project roots | Local Lean files | Bytes | Lines |
| --- | ---: | ---: | ---: | ---: |
| All existing problem sources | 20 | 4,192 | 41,445,777 | 378,249 |
| Import closure of every mapped current claim and supporting proof file | 17 | 2,270 | 11,230,365 | 234,057 |
| Challenge and Solution import closure for all 338 current interfaces | 18 | 3,730 | 39,762,522 | 348,679 |

The accompanying [machine-readable inventory](build-architecture.json) contains the relative source paths, module names, SHA256 hashes, sizes, and import closures. Imports were extracted after masking nested block comments and line comments. None of the two selected closures has an unresolved nonstandard local import. This is a static source-closure check; elaboration may introduce dependencies that source-token scanning does not establish.

The raw source distribution fits comfortably below Palomar's 500 MiB source-snapshot limit. Compiled caches, dependency checkouts, old raw export archives, credentials, scratch scripts, and unrelated editorial material should not be copied merely because they exist in the working repository. Dependency sources are fetched from pinned manifests. Preserve a compact, accurately labeled evidence index rather than implying that copied old receipts are a fresh official acceptance.

## Historical dependency pins and module collisions

The twenty original projects use `leanprover/lean4:v4.33.1`. All have the same ten package entries, including:

- leancert: `621a43d7cf21f87872392a01e874f2f1dbddc926`;
- mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`;
- the eight remaining exact dependency revisions recorded in the JSON inventory.

A source-only merge into one Lake project is possible only after dealing with module names. Generic `Challenge`, `Solution`, `PaperChallenge`, `PaperSolution`, `Reduction`, and `FidelityAudit` have different contents in different projects. The shared `NLA.*` module names inspected across projects have identical bytes. In the minimum mapped-claim proof closure, the only conflicting repeated module name is `PaperSolution`, needed in six projects. Separate project roots avoid these collisions entirely.

## The current-protocol port

The current [Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md) and its pinned verifier impose requirements that the old interfaces were not written to satisfy. The detailed contract and checked upstream revisions are documented in `PALOMAR-REQUIREMENTS.md`.

The required toolchain floor is Lean 4.35.0-rc2. Every regular `.lean` file in the submitted checkout must use the module system. The Challenge import closure is restricted to the permitted canonical libraries and their exact dependencies; it cannot import this project's semantic helper modules. A Challenge is limited to 1,000 lines and 100 KiB. The old custom `fixed_definition_names` configuration key is not accepted. The current official Comparator instead fixes ordinary definition bodies transitively reachable from selected theorem types. Its reachability rules must be audited before removing a custom fixed-body obligation.

Of the existing 4,192 Lean sources, 3,955 have no leading module header. Of the 2,270 files in the minimum mapped-claim proof closure, 2,035 have no such header. Adding a header alone is insufficient: public imports, public declarations, and exposed definition bodies must retain the required accessibility. Existing receipts certify the recorded old bytes and dependencies, not a rewritten module tree or a new toolchain pin.

The intended current-protocol structure is therefore a shared source distribution with separate entry projects. Each entry has a self-contained `Challenge.lean` defining its mathematical objects directly using permitted imports, a `Solution.lean` proving those exact statements from the ported implementation, an ordinary official Comparator configuration, a pinned Lake project, and honest provenance metadata. The proof implementation may import project helpers on the Solution side. Definitions duplicated into a Challenge need a checked equivalence or a body-preserving namespace arrangement, rather than an informal assertion that they mean the same thing.

### Statement-size feasibility

Naively flattening all imported helper modules is not viable for the larger problems:

| Primary statement | Local import closure lines | Bytes |
| --- | ---: | ---: |
| Universal row deletion, IE-22 | 3,678 | 174,522 |
| Strict tensor-train algorithm, TR-04 | 2,835 | 122,186 |
| Tensor-power family, TR-27 | 2,837 | 127,919 |
| Cubic-graph main theorem, MD-06 | 1,279 | 49,979 |
| Interval determinant, IV-02 through IV-04 | 45,355 | 2,090,698 |
| Interval full hull, IV-04 | 45,334 | 2,089,374 |

These counts include irrelevant imported proofs. A rough source-command pruning estimate leaves about 280 lines of definitions for IE-22, 502 for TR-27, 754 for MD-06, and 996 for TR-04, before the theorem statements and namespace context. Those estimates suggest that precise declaration dependency pruning can help, but they are not Lean parser results or compliance certificates. The interval interfaces still have about 9,360 lines of imported definition commands before pruning. They need a substantially smaller faithful semantic closure or a compact computational presentation with proven equivalence to the original literal machine and encoding model.

An unchanged older source archive should be retained as a compressed archive if needed. Keeping its old `.lean` files in an unused folder still subjects those files to the current checkout-wide module rules. A label saying archival does not exempt them.

## Correctness boundaries

- Preserve all assumptions, quantifiers, scalar fields, dimensions, matrix and tensor operations, algorithm choices, computational encodings, and exact constants when preparing statement surfaces.
- Keep mathematical definitions reachable and fixed. Unconstrained parameters, definition holes, extra axioms, or aliases concealing substantive hypotheses do not supply the corresponding paper theorem.
- Keep the universal strict tensor-train guarantee attached to the modified solver. Its all-order sharpness witness must concern the actual solver execution at each fixed order.
- Keep the literal IV-04 machine, polynomial-time, and output-task semantics when presenting the interval complexity results. A predicate merely named NP-hardness is not a translation check.
- Distinguish the retained successful component checks from the canceled full combined replay. No new replay was performed for this architecture analysis.
- A modernized source tree still needs an ordinary Lean build and the official Palomar Lean-plus-NanoDa verification before it can be described as accepted under the current protocol. No such acceptance is claimed here.

No manuscript files, original Lean sources, Git history, or remote repositories were changed by this analysis.

## Completed source staging

The exact 2,270-file mapped-claim proof closure is staged under `projects/<ID>/`. The initial promotion changed module headers, public imports, and exposed public sections. The subsequent canonical-Mathlib compatibility patch is described below. All 2,150 changed source files have original and current staged SHA256 hashes in `audit/source-port-manifest.json`. The unchanged input sources, original build pins, and four original coverage ledgers are preserved in a deterministic 2,262,738-byte archive: `archives/lean4.33.1-mapped-claim-sources.tar.gz`, SHA256 `2cc227f311ce50440d1932f7cab9cac1e2944e760d0ac3ab0e33e61ae093cf36`.

`python scripts/stage_sources.py verify` passed the static archive, source-hash, deterministic transformation, module-header, import-visibility, exposed-section, and 10,000-line checks. It added 2,035 module headers, promoted 5,072 imports, and added 2,135 exposed public sections. The largest staged source has 5,370 lines. These checks do not establish Lean 4.35 compatibility or Palomar acceptance.

The helper rebuilds source copies from the included archive without the original workspace. It refuses to overwrite unrecorded hand-edited source files by default and preserves existing project pin files. Missing current configuration causes a clear failure; historical 4.33.1 pins are never restored into the modern source tree. Regenerate current configuration with `scripts/pin_mathlib_dependencies.py` before staging when necessary. The original archived Lake defaults are historical inputs; current entry projects must explicitly build their new public Solution modules.

## Generated public entry surfaces

Seventeen public Challenge/Solution/Comparator interfaces were generated from the included original-source archives. The interval-complexity entry has its own precise extractor and audit record, merged into the shared interface inventory. Each generated Challenge imports only canonical Mathlib, has at most 739 lines and 35,386 bytes, and uses the ordinary official configuration keys. The exact inventory is in `audit/entry-surface-inventory.json`; generation alone is not a successful Lean build or official comparison.

Small entries retain the entire relevant semantic source closure, with the selected theorem types copied exactly. The IE-22 surface omits transitive modules that only prove estimates; every referenced semantic definition is retained. The larger TR-04, TR-27, and MD-06 surfaces use conservative declaration dependency extraction. It records ambiguous name resolutions and refuses unresolved project-qualified or private dependencies. No such issue was reported for those three generated surfaces.

Seven public construction lemmas become explicit supporting comparison targets: two cardinality equalities for tensor layouts, four quotient/projection/nonvanishing certificates for tensor geometry, and nonemptiness of the labelled cubic-graph sample. Their exact original types appear as Challenge placeholders, and their genuine original proofs remain on the Solution side. Every theorem placeholder is selected in `theorem_names`; no semantic definition body is replaced by a hole. The per-entry metadata explains the supporting mathematical assertions. Every mapped auxiliary and prose proof root remains in the source inventory and must compile as an independent build-graph root. Fifteen Solution entries also import those roots. TR-04 imports its original primary solution root, and IV-04 imports its two original primary solution roots: older independent arithmetic or polyhedral implementations reuse constant names and cannot all be imported into one environment. TR-04’s two supporting certificates are already in its primary root’s dependency closure. `solution_import_roots` and `independently_built_proof_roots` in the interface audit distinguish these obligations.

The initial statement surfaces preserve their archived mathematical definitions and theorem types while removing import/header/visibility directives, unused checking queries, and unused project namespace opens. Dependency pruning can leave unattached documentation comments, so the extractor converts their delimiters to ordinary comments without changing their text. TR-04 removes empty layout lines outside quoted strings and spaces plain relation tokens in retained theorem headers for the current parser. Any subsequent API compatibility override, including the MD-06 finite uniform distribution port, is literal and hash-bound in `patches/interfaces/`; these are separate from the original text-identity checks. Dependency extraction and output hashes are recorded in `audit/extraction-diagnostics/` and `audit/entry-interfaces.json`.

Rebuilders are `scripts/build_entry_interfaces.py` for whole-closure and reviewed module-pruned entries and `scripts/extract_semantic_surface.py` for the three declaration-pruned entries. They use the included archives and refuse to overwrite hand-edited entry files by default. The original statement archive has 45 members, including five statement-only helpers absent from the proof closure, and SHA256 `0b2410dff7b033a836c732f8d353a86a53a99f64407eeafd598ba3b053e988a4`.

## Canonical Mathlib compatibility patch

The active projects now use Lean 4.35.0 and the canonical Mathlib revision in `dependency-profile.json`; the historical LeanCert environment remains only in the original archives. The literal, hash-bound compatibility patch affects 1,470 source files: it replaces or removes 488 legacy utility imports, removes 5,512 optional `#assert_trust` checking queries and 428 utility options, and changes exactly six elementary proof tactics. Five closed rational comparisons use Mathlib `norm_num`; the exponential bound uses the already proved `Real.exp_one_lt_three.le`. No theorem statement or ordinary mathematical definition body changes. Printed axiom queries and all genuine mathematical proofs are retained.

The full before/after hashes and exact substitutions are in `patches/compatibility/lean435-canonical-mathlib-only.json`. Source promotion and verification apply these substitutions deterministically. `scripts/record_compatibility_patch.py` records later hand-reviewed source compatibility edits as additional exact overrides; it does not infer mathematical equivalence. That initial patch produced a 10,978,077-byte source footprint. Later exact overrides in `patches/compatibility/zz*.json` repair API calls, proof steps already completed by stronger tactics, imports, and visibility required by the module system. A further closed rational inequality in MI-19 uses `norm_num`. The MD-06 probability API port replaces a library identifier whose type changed with the explicit finite uniform PMF construction; its literal definition-body changes are recorded rather than treated as unchanged source text.

The sequential source-stage and verification run for source-build freeze `37ee2fe4e45e01ee46f01bc673993d67dd9890ea4b38a6b8f631a4e1fc2ee6d7` passed for all 2,270 sources with patches through `zz0104`. That snapshot has 2,150 changed source files and 10,981,155 staged bytes. The current source manifest, exact ordered compatibility patches and ordinary build receipts take precedence over these snapshot counts when further repairs are recorded. Static verification checks exact transformations and directives; it does not establish mathematical equivalence, successful compilation, or Palomar acceptance. The dedicated kernel replay remains canceled.


The latest sequential verification checkpoint covers 10,982,243 staged source bytes and binds each recorded compatibility patch-file hash, each visibility-promoted source hash, and the exact transformation-action record. These provenance checks are in addition to final source-byte and directive checks. The current checkpoint is `audit/source-staging-verification.json`; compilation remains a separate requirement.
