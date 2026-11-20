# Submit the collection once to Palomar

All twenty problem resolutions have **one** repository-root Challenge/Solution
interface and **one** public Comparator configuration. Submit the root entry
once. The seventeen `projects/` directories are internal proof components,
with historical source-build evidence and mathematical accounts.

## 1. Check the snapshot

With Python 3.11 or later, run from the repository root:

~~~text
python -m pip install -r tools/requirements.txt
python scripts/build_entry_metadata.py --check
python scripts/build_combined_interface.py --check
python tools/check_source_coverage.py
python tools/check_submission.py
~~~

The readiness report is
[audit/static-submission-check.json](audit/static-submission-check.json).
It must establish matching fresh combined compilation and selected-axiom
evidence in
[verification/combined-build-status.json](verification/combined-build-status.json).
The seventeen independent component builds alone cannot establish one combined
Solution. Their historical receipts remain in `verification/build-status.json`
and `verification/selected-axioms/`.

After any combined proof input changes, rebuild and refresh the combined
evidence. The combined build helper's `--help` documents compiler, dependency,
and working-directory options. Official Palomar verification and NanoDa replay
remain separate from these local checks.

## 2. Commit and push

This working folder is on `main`, with `origin` configured as
`https://github.com/MColbrook/NLA-formal-verification-20-problems`.
For a new snapshot or later corrections, commit and push all intended changes.
If the working tree is already clean, use the existing pushed commit.

~~~text
git status --short
git add .
git diff --cached --stat
git commit -m "Prepare single numerical linear algebra Palomar submission"
git push -u origin main
git status --short
git rev-parse HEAD
~~~

After committing, `git status --short` should be empty. Copy the full
40-character SHA and confirm that exact commit is visible on GitHub.
Configure your own Git author name/email if requested, and reconcile any new
remote changes before pushing.

Keep LICENSE, NOTICE.md, LICENSES/, manifests, source archives, audit records,
and .gitattributes, which preserves audited source bytes across Git checkouts.

## 3. Complete one submission form

Open [Palomar's form](https://submit.palomar-registry.org/) and use:

| Field | Value |
| --- | --- |
| Repository | `MColbrook/NLA-formal-verification-20-problems` |
| Commit | The final pushed full 40-character SHA |
| Comparator configuration | `comparator.json` |
| Project directory | Leave blank: the project is at the repository root |
| Formalization metadata | `formalization.yaml`, or leave blank for this root default |
| Existing Palomar ID | Leave blank for this new registration |

If the form offers internal component configurations, explicitly select the
**root** `comparator.json`. Do not submit the configurations under `projects/`
as additional entries. The root configuration covers all twenty problems and
all 34 component headline/supporting declarations, plus the documented
technical proof helpers in the root configuration.

Select the truthful responsible author/maintainer relationship, or approval
from one, and authenticate with a GitHub account that has repository write
access. Review the preliminary checks and collection-wide description, then
submit once. Save the returned status-page link together with the commit SHA.

Palomar performs isolated mechanical verification, including Comparator,
Lean's kernel, and independent NanoDa replay, then editorial review.
Inspect the exact reports and any requested corrections on the status page.

## 4. Register after review

If the review identifies no blocking problem, inspect the abstract, selected
statements, and review, then choose **Register** on that same status page.
Registration is a separate final choice. It publishes one registry record
and preserves immutable source/dependency history.

For corrections before registration, commit and push the changes, rerun the
relevant checks, and submit the new full SHA. Enter an existing Palomar ID only
when registering a new version of an already registered result.

See the [official guide](https://palomar-registry.org/how-to-submit) and
[binding protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md).

## Optional source transfer

~~~text
python scripts/make_upload_zip.py
~~~

This creates `dist/palomar_submission-upload.zip`, omitting Git state, dependency
caches, local build logs, and `dist/` itself. The ZIP is ignored by Git and is
unnecessary when pushing directly. Extract it into an empty directory with
the repository files directly at its root.

## Optional local reproduction

Install the pinned compiler through Elan and prepare the pinned dependency cache:

~~~text
elan toolchain install leanprover/lean4:v4.35.0
python scripts/prepare_dependencies.py
~~~

Then, in PowerShell:

~~~powershell
$leanCompiler = (elan which lean).Trim()
python scripts/build_combined_project.py --lean $leanCompiler --jobs 1
python scripts/check_combined_correspondence.py --lean $leanCompiler
~~~

The build helper stages byte-identical shared proof sources, checks the combined
Challenge and Solution import closure, and runs compiled axiom queries for
every declaration in the root configuration. It keeps source/dependency and compiler bindings
in the combined receipt. The single-job setting suits the preparation laptop;
increase parallelism only when sufficient memory is available. Run the
readiness checker again afterwards. The correspondence helper imports the
Challenge and Solution independently and invokes the bundled Comparator
comparison code on their statement and fixed-definition closures. It materializes statement data without
full proof export or kernel replay; Palomar performs the official checks.

The manually triggered **Source build and submission preflight** workflow
reproduces the internal component builds and then the combined root build.
These internal build jobs still produce one Palomar registration target.
Report local build and comparison outcomes separately from Palomar's result.
