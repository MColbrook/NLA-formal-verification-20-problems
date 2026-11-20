# Sharp random-pivoting losses for Cholesky and LU

The sharp worst-case expected loss after r random pivots is 2^r for Cholesky trace residual and 4^r for LU squared Frobenius residual, relative to the corresponding optimal rank-r error.

Research audience: Researchers in randomized numerical linear algebra and low-rank matrix approximation.

Assumptions and conventions:

- The pivot laws and residual updates are the actual randomized algorithms, including zero-pivot and absorbing-zero cases.
- Cholesky inputs are complex positive semidefinite matrices; LU inputs may be arbitrary rectangular complex matrices. Ratios require positive optimal rank-r error.
- The same suprema hold on the stated subclass of real positive-definite entrywise-positive inputs. The rank parameter includes every positive integer r.

Selected headline statements:

- **rap-cor:sup** — Identifies the exact four least upper bounds: 2^r for the Cholesky loss and 4^r for the LU loss, both over the full admissible classes and over the real positive-definite entrywise-positive sharpness subclasses. Lean declaration: `NLA.RA02.Paper.paper_sup_worst_case_constants`.

This grouped component covers RA-02 and RA-03. Unit-diagonal restrictions and finite rational certificates are separate auxiliary library material, not extra conclusions of the selected supremum theorem.

Only the exact declarations listed in [comparator.json](comparator.json) are selected for this component. The full independently compiled module graph retains the other recorded paper proofs; library coverage and a selected comparison are separate scopes. Every retained local module passed ordinary compilation.

This Solution imports all mapped proof roots. The all-local builder mode compiles every retained local module independently, keeping alternative proof environments separate where necessary.

This component passed ordinary full-source Lean 4.35.0 compilation and read-only compiled axiom-dependency queries for every configured declaration, within propext, Classical.choice and Quot.sound. Historical Lean 4.33.1 receipts remain separate source-bound evidence. Official Comparator and NanoDa verification remain pending the authors' later submission; no Palomar acceptance or independent-kernel replay is claimed.

The source is the author-provided unpublished manuscript, section 4, SHA-256 `b66976c1efa4f625f3b380fef6e945ddf4d7beea6e1b264e2f87d6790548bba5`. The manuscript and book are not reproduced here. [formalization.yaml](formalization.yaml) records mathematical sources, prior formalizations, scope and AI involvement.

Human authors and responsible maintainers: Matthew J. Colbrook and George Stepaniants. Substantial OpenAI Codex assistance and agent review are disclosed; no independent human review is claimed. The owner authorized the new Apache-2.0 release with third-party notices preserved. See the repository [LICENSE](../../LICENSE), [NOTICE](../../NOTICE.md) and [component texts](../../LICENSES/).

This proof component belongs to the single root Palomar submission. Submit the collection once with the repository-root comparator.json and formalization.yaml; leave the project directory blank. This account does not require a separate registry entry.
