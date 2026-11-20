# Palomar submission requirements

Checked on 19 November 2026 against the exact official revisions below. This is a preparation record, not a Palomar verification result. No GitHub upload, intake request, registration, or new kernel replay was performed for this requirements review.

## Official sources and exact revisions

| Source | Revision | Purpose |
| --- | --- | --- |
| [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/tree/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60) | `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60` | [Submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md) and [binding protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/docs/specification.md) |
| [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7) | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` | Executable validators and reusable verification workflow |
| [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406) | `2891de4c48955af824969a263d31b25e7a9a1406` | Starter layout, metadata and CI examples |
| [Lean bundled Comparator](https://github.com/leanprover/lean4/tree/11acb17ec6b07a8f9e9173e6845197929540936b/src/lake/Lake/Check) | `11acb17ec6b07a8f9e9173e6845197929540936b` (v4.35.0-rc2) | Definition comparison semantics at the supported floor |

The public [submission guide](https://palomar-registry.org/how-to-submit) points to the policy; the [submission server](https://submit.palomar-registry.org/) is the intake route. Recheck the policy before submitting: these rules can change. The machine-readable companion is [palomar-requirements.json](palomar-requirements.json).

## Repository and entry layout

The submission identifies a public GitHub repository, an immutable full 40-character commit SHA, and one explicit repository-relative Comparator configuration path. One configuration produces one entry. A single configuration may select several declarations; separate configurations need separate submissions. This makes a family of entries sharing one paper and commit possible.

A selected Lean project needs one Lakefile (TOML or Lean), a supported toolchain, committed dependency pins, a Challenge, a Solution and metadata. `Challenge.lean` and `Solution.lean` are conventions: dotted modules such as `Submissions.MF05.Challenge` and `Submissions.MF05.Solution` are allowed in one shared project. No otherwise-unused root Challenge file is required. A nested project is also allowed. The selected file for each named module must be regular, inside that project, and resolvable through Lake's source paths.

The metadata may be shared outside a selected nested project when its explicit path ends in `formalization.yaml`. The Comparator file must be inside the selected project and end in `.json`. Paths use forward slashes from the repository root and cannot contain `..`, absolute components or symlinks. The single repository licence remains at the repository root. [Policy §§2,6](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md)

## Source, toolchain and dependency gates

The current [toolchain floor](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/toolchains.json) is **Lean v4.35.0-rc2**. With canonical Mathlib, the selected toolchain must exactly match the toolchain of the resolved Mathlib commit, including patch and release-candidate suffixes. Pin every Git dependency to a full lowercase commit at a public credential-free HTTPS GitHub URL. A committed manifest is mandatory for a Lean Lakefile; the narrow TOML exception is limited to certain contained path-only dependency layouts.

Every regular Lean source in the submitted checkout must use `module` and have at most 10,000 physical lines, including unused files and contained projects. Only `lakefile.lean` is exempt from the header. The scan excludes `.git` and `.lake`; Lean symlinks fail. Module documentation follows the header. The [official source validator](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/scripts/source_requirements.py) checks this before a build.

Porting requires visibility changes as well as a header. The [Lean porting recipe](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/) recommends public imports as appropriate and `@[expose] public section` after imports for an initial mathematical-library port. Definitions whose bodies clients unfold must be exposed; metaprograms can require meta imports. A successful source scan does not establish a successful port. Rebuild after any migration.

The Challenge's entire transitive import closure must be Lean core or an authenticated canonical Mathlib, Tau Ceti or CSLib closure. **A Challenge cannot import project-specific helper files**, even if those helpers contain only definitions. Essential local definitions must be stated in the selected Challenge itself, using ordinary documented mathematical meanings. Proof-only Solution imports have the broader public-GitHub and contained-path dependency rules. [Dependency implementation](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/scripts/verify_submission.py)

Do not include Git submodules, Git LFS pointers, or compiled Lean/native artifacts outside `.lake`. Submitted `.lake` state is discarded. The whole checkout excluding `.git` and symlinks must fit within 500 MiB.

| File | Hard bound |
| --- | --- |
| Selected Challenge | 1,000 lines and 100 KiB |
| Any submitted Lean source | 10,000 physical lines |
| Comparator JSON / Lakefile / root licence | 1 MiB each |
| `formalization.yaml` | 256 KiB |

A Challenge over 300 lines or 32 KiB receives an auditability warning. Inline registry display additionally needs exactly one selected declaration and at most 100 lines/32 KiB; larger accepted Challenges receive a separate rendered page.

## Comparator and fixed definitions

The [submitted-config validator](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/scripts/verify_submission.py#L1136) requires `challenge_module`, `solution_module`, a nonempty `theorem_names` array and `permitted_axioms`. Only `definition_names` and `enable_nanoda` are optional additional keys. **`fixed_definition_names` is rejected.** Module names must be distinct safe dotted identifiers. Selected declaration names must use the verifier's canonical Lean identifier syntax.

This does not mean ordinary definitions may change freely. In the bundled [`Compare.loop`](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/lake/Lake/Check/Compare.lean), constants transitively reached from compared theorem types are compared by complete constant information unless they are selected theorem targets or definition holes. Ordinary definition bodies must match. [`runForUsedConsts`](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/lake/Lake/Check/Util.lean) follows both types and available values, inductive constructors and recursor rules. This is a source-code finding, not an executed comparison of this package.

Use `definition_names: []` when no intentional definition holes are wanted. Do not move the old fixed-definition list into `definition_names`: that field permits a Solution-supplied value for a Challenge hole. Before retiring a custom fixed-body receipt, check that each material fixed definition lies in the new selected statement closure; an unreferenced old fixed target is not automatically checked merely because its name appeared in the former custom configuration.

A helper theorem whose proof occurs in an ordinary definition is also reached by this comparison. If the Challenge replaces that helper proof by `sorry`, select the helper in `theorem_names` as well and retain its genuinely proved Solution counterpart. Otherwise the non-target theorem proof is compared structurally. Use stable public helper names: the verifier gives the canonical Challenge a fresh module name, which changes private generated names. This follows the derived Boolean equality of [Lean theorem/constant information](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Lean/Declaration.lean), rather than an assumption about proof irrelevance. Supporting helpers should be identified as such in the mathematical account.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted axioms. Challenge `sorry` placeholders are intentional; proved Solution closures may not use `sorryAx`, `Lean.ofReduceBool` or other axioms. Palomar always runs Lean's kernel and independent NanoDa. A submitted `enable_nanoda: false` cannot disable replay. Con-ron is additionally attempted; recognized support/capacity declines are distinguished from rejection or unknown errors. [Protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/docs/specification.md)

## Metadata, provenance and mathematical account

Use the [v0.4 template](https://github.com/PalomarRegistry/PalomarTemplate/blob/2891de4c48955af824969a263d31b25e7a9a1406/formalization.yaml) with factual project name, concise mathematical description, human authors and responsible maintainers, licence, classifications, sources, automation methods and completed-review status. The description is the registry abstract, limited to 10,000 characters; the name is limited to 300. There must be 1–8 distinct supported arXiv categories and at most 8 MSC2020 codes. The current validator accepts an empty MSC list. Unknown metadata fields are allowed; duplicate YAML keys and merge keys are rejected.

The sources must distinguish the paper being formalized, the problem collection and earlier mathematical work. Prior formalizations belong separately in `related_formalizations`; software dependencies are not mathematical sources. Canonical relationships are `formalizes`, `adapts`, `independently-proves`, `background` and `other`. For this source-based development, use the relevant substantive relationship and do not mark an already-presented result `original-proof`. The pinned policy prescribes canonical source kinds; the pinned implementation accepts broader optional source-kind text. `paper` follows both. [Metadata validator](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/scripts/submission_contract.py)

Omit `repository` when the new repository contains the substantive proofs. Only a thin wrapper uses `repository.substantive_formalization` with an exact public repository and commit. Do not infer formalizer authorship from the paper's author list. AI systems are credited in automation, never as project authors or responsible maintainers. Disclose material AI roles honestly; untracked costs, exact model versions or elapsed effort need not be invented or reconstructed. Review status describes work already done and must not imply Palomar approval.

Across the metadata, README and Challenge documentation, explain every selected result, its relation to the paper, hypotheses, quantifiers, degenerate cases, definitions, known divergences and omissions. A source-to-Lean ledger supplies useful review evidence but does not replace correct formal statements. The abstract should signpost the principal result families; it need not list every declaration. A supplied informal proof account must describe the proof actually present. State novelty only when supported by a literature search.

The root needs exactly one conventional standard licence file, at most 1 MiB, whose detected SPDX identifier exactly matches `project.license`. A custom no-grant notice fails the mechanical gate. The detector does not establish ownership or permission to relicense copied material. Preserve third-party terms and attribution.

## Validation and later submission

Exact official source trees, including their original licences, were downloaded during preparation. The machine-readable record includes repository/archive pins. Useful non-kernel entry points are `source_requirements.inspect_lean_sources`, `submission_contract.load_formalization_metadata`, and `verify_submission.load_comparator_config`, `supported_toolchain`, `repository_license_file` and `manifest_packages`. Those individual checks are narrower than Palomar's full preparation and execution.

After upload, a maintainer can run the exact [reusable workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/.github/workflows/submission.yml) as a predictive preflight: pin `uses` and `pipeline_commit` to the same SHA above, choose `mode: full` and `execution_profile: palomar-standard-v1`, and supply a 12-character lowercase-alphanumeric request identifier plus the exact project/configuration/metadata paths and truthful authorization relationship. That preflight runs kernels. It was not run as part of this preparation, following the user's instruction to skip replay. A package-specific audit or old receipt must not be described as a current Palomar pass.

For eventual submission, commit and push the exact intended public snapshot; record its full SHA. Submit through the server as a responsible author/maintainer or with their approval, separately proving repository write access. Review and registration are separate stages: a review finding no blocking issue does not itself publish a registry entry. Registration needs explicit consent and preserves the source and dependencies under immutable public archive tags. The user will perform upload and submission.

## Compatibility baseline requiring attention

Before any new Palomar migration, the existing development under `lean/problems` used Lean v4.33.1 in all 20 project toolchains. The legacy tree contains sources requiring module promotion and custom checker configurations using the unsupported fixed-definition key. The new package records each promoted source and applies the official source inspection to the resulting files. These are baseline observations about the existing source tree, not assertions about the final new repository. Earlier package audits and component replays certify their recorded source versions; they do not certify a changed toolchain, module port, merged project or newly flattened statement.

A release claim must therefore distinguish source coverage and historical evidence from current-interface compilation, exact statement comparison, root licensing and Palomar's future mandatory replay. Where any of those checks remains outstanding, the repository should state it plainly instead of declaring submission acceptance.
