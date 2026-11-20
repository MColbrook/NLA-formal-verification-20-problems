# Verification-tool provenance and licence notices

The NLA driver (`bootstrap.sh`, `verify.sh`, `harness.py` and its tests) is
Copyright (c) 2026 George Stepaniants, licensed under Apache-2.0. It was
developed with Codex assistance. See `LICENSE-APACHE-2.0`.

`source-lock.json` fetches exact files from
[sgstepaniants/Forsythe, commit
8d1b0c0545a77b40245e84705aa7d273e6c81e62](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof).
Every fetched file has an independent SHA256 digest and byte count. No
mathematical Forsythe proof is fetched: the Lean test declarations exercise
the checker itself. Original notices and licence texts remain in place.

The fetched sources comprise:

- Lean FRO's Comparator, Apache-2.0, including the original author and
  copyright notices. Forsythe's distribution adapts the kernel replay call
  to Lean 4.33.1 and records the exact one-line change in
  `scripts/comparator-lean-4.33.1.patch`. It retains statement, transitive
  axiom, kernel replay, constructor/recursor and quotient consistency checks.
- Lean FRO's lean4export, Apache-2.0, compiled for Lean 4.33.1.
- Landrun 0.1.18, MIT, Copyright (c) 2025 Armin ranjbar; its original licence
  is fetched and retained at `.tools/landrun/LICENSE` in the tool directory.
- Forsythe's strict Landrun/Bubblewrap adapter and sandbox, kernel replay,
  and Comparator regression probes, under its `lean-proof/LICENSE`
  (Apache-2.0). These files are fetched without modification.

The driver derives a noninteractive CI copy of the sandbox probe: its two
systemd `--pty` options become `--pipe`, and service/caller deadlines are added.
Every assertion and isolation property remains unchanged. The original source
and its hash remain intact, and the derived source hash is checked and recorded.
The derived copy also prints each case's start for noninteractive diagnostics.
Its probe-only Landrun arguments permit execution of `/usr/bin/bwrap` so the
nested escape control actually exercises namespace/write isolation on modern
Landlock hosts. This does not change the Comparator sandbox or waive a denial
assertion; the original host's best-effort Landlock behavior differed.

NLA adds a generic committed-project snapshot driver, recorded tool/source
hashes, configuration checks, and two additional negative controls for
`sorryAx` and Lean 4.33.1's generated native-execution axiom. NLA does not claim that the tool authors
reviewed this integration, and does not substitute Forsythe's historical
verification logs for a new run on an NLA theorem.

The paper package adapts this driver with Codex assistance to accept named
configurations, qualified modules, and uncommitted source snapshots. The
adaptation makes no Git mutations and records its own source hash. The
locked checker, exporter, sandbox and regression sources are unchanged.
The bundled test_harness.py exercises input and snapshot validation only;
genuine Linux sandbox/checker controls remain separate required checks.

The optional `fixed_definition_names` extension uses ordinary definition roots.
It requires safe `defnInfo` declarations on both sides, compares their types,
bodies and dependencies with the pinned `compareAt` function, then applies the
pinned transitive `checkAxioms` and `runBuiltinKernel`, including its quotient
post-check. Fixed definitions never enter either comparison bypass list.
The older nonempty `definition_names` hole mode remains rejected.

`FixedDefinitionsMain.lean` is NLA integration code under Apache-2.0. For each
extension run, the driver freshly compiles the small SHA256-locked Comparator
and Export source closure. It derives `NlaHarness.PinnedComparatorMainSupport`
from the exact locked Comparator `Main.lean`, omitting only the final CLI
`main` declaration. Both the exact omitted tail and the entire retained
prefix are checked; the retained prefix SHA256 is
`b82d2f71c3b11c9af5ae7bfd32275a1a467772d7e87bb49c23ea172a4e44c4ae`.
The original source and source-lock are unchanged. New source and artifact
hashes, compilation logs and actual positive/body/type/kind/unsafe/custom-axiom
controls are recorded separately. The authenticated extension build comes
first in the import path so project modules cannot shadow its checker imports.
The literal locked exporter CLI source is run against this same freshly
compiled closure; its wrapper and source bytes are also authenticated.

The licences grant code reuse; they do not establish mathematical verification
or author endorsement of NLA's results.
