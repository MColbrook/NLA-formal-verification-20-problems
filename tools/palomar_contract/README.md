# Pinned Palomar validation sources

These files are copied without modification from [PalomarSubmission at 14aa8d6b3c2f14a8540605e37144560b9a00e7e7](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7). Their MIT licence and original notices are retained. SOURCE.json records every copied-file digest.

The adjacent check_submission.py imports only static validators. It does not invoke the official prepare/execute orchestration, a Lean build, Comparator, a kernel, a subprocess or network access. This local structural check is narrower than Palomar verification.

Install the portable local-check dependency with `python -m pip install -r tools/requirements.txt`. The unchanged upstream requirements with artifact hashes are also retained in this directory. Run `python tools/check_submission.py --self-test`, then `python tools/check_submission.py --json audit/static-submission-check.json`. Exit code 2 means static structure passed but matching build evidence is still missing; `--static-only` uses only the structural verdict for CI without changing readiness fields.

Build evidence is read from `verification/build-status.json`: top-level `status: pass` and 17 project records with `id`, `status: pass`, `toolchain`, `source_inventory_sha256`. Each digest must match the checker’s current per-project report, so stale pre-port builds do not establish compatibility. Kernel replay is separate and is never performed here. Do not import the wrapper into a build process: it deliberately disables subprocess and network entry points; call it as a command.
