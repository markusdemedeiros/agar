[![Proof Provenance][fc-class-certificate]][fc-link]

> [!CAUTION]
> Here be dragons. This repository is AI-generated. 

# Agar

A small concurrent imperative language with an Iris-style separation-logic
program logic, verified end-to-end in Lean 4.

* Surface language with heap, procedures, `fork`/`CAS`/`alloc`/`free`.
* A custom mask-aware fancy-update WP, integrated with iris-lean's
  invariants, late credits, and fancy-update infrastructure.
* Full multi-thread adequacy: `wp_strong_adequacy` ties threadwise
  reasoning to a closed `Machine.StepStarN` safety + main-postcondition
  theorem. This is the current marquee result.
* A pure terminating denotational fragment (`PureStmt`) with a
  bidirectional marquee theorem `Machine.denote_iff`, plus closed-form
  examples for Gauss, GCD, and squaring.
* Worked verification examples: counter (CAS+ghost RA), one-slot
  producer/consumer, fork+disjoint-heap, mutex, spinlock, ticket lock,
  Treiber stack, 3-element insertion sort — each closed via
  `Machine.Adequate`.


## Layout

```
Agar/
  Lang/        — surface language (Syntax, Semantics, Notation, Denotational)
  Iris/        — program-logic infrastructure (Wp, Heap, Rules, Tactics,
                 TacticsAtomic, Adequacy, Hoare, Implements, Library, Delab,
                 Algebra/{CounterRA,LockRA})
  Examples/    — end-to-end verifications (Sanity, Recursion, Sequential,
                 DataStructures, Fork, ParAdd, Invariant, Mutex, Spin,
                 LaterCredits, Counter, ProducerConsumer, GcdMarquee,
                 InsertionSort3, SquareMarquee)
```

See `Agar.lean` for the per-module index with one-line descriptions.

## Where to start reading

1. `DESIGN.md` — language spec, operational semantics, intended notation.
2. `Agar/Iris/TACTICS.md` — reference for the proof-mode tactic suite
   (`wp_pures`, `wp_call <ident>`, `wp_apply`, `wp_load`/`wp_store`,
   `wp_cas_*`, `wp_alloc`, `inv_*`, the atomic-triple variants).
3. `Agar/Examples/Sanity.lean` — minimal sanity checks against each WP
   rule.
4. `Agar/Examples/Fork.lean`, then `Examples/Counter.lean` — small
   concurrent examples.
5. `Agar/Examples/InsertionSort3.lean` — the most substantial
   end-to-end heap-mutation proof.
6. `Agar/Lang/Denotational.lean` + `Examples/GcdMarquee.lean` — the
   bidirectional denotational/operational connection.

## Build

```
lake build
```

Toolchain: Lean v4.29.0. The iris-lean dependency is pinned in
`lakefile.toml` to a commit on the upstream main branch that ships the
post-v4.29.0 `WSat`/`Invariants`/`FUpd`/`LaterCredits` libraries.

[fc-link]: https://github.com/markusdemedeiros/Proof-Provenance
[fc-class-bare]: https://img.shields.io/badge/proof%20provenance-bare-black?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA1MTIgNTEyIiBmaWxsPSJ3aGl0ZSI+PHBhdGggZD0iTTE3NiAyNGMwLTEzLjMtMTAuNy0yNC0yNC0yNHMtMjQgMTAuNy0yNCAyNFY2NGMtMzUuMyAwLTY0IDI4LjctNjQgNjRIMjRjLTEzLjMgMC0yNCAxMC43LTI0IDI0czEwLjcgMjQgMjQgMjRINjR2NTZIMjRjLTEzLjMgMC0yNCAxMC43LTI0IDI0czEwLjcgMjQgMjQgMjRINjR2NTZIMjRjLTEzLjMgMC0yNCAxMC43LTI0IDI0czEwLjcgMjQgMjQgMjRINjRjMCAzNS4zIDI4LjcgNjQgNjQgNjR2NDBjMCAxMy4zIDEwLjcgMjQgMjQgMjRzMjQtMTAuNyAyNC0yNFY0NDhoNTZ2NDBjMCAxMy4zIDEwLjcgMjQgMjQgMjRzMjQtMTAuNyAyNC0yNFY0NDhoNTZ2NDBjMCAxMy4zIDEwLjcgMjQgMjQgMjRzMjQtMTAuNyAyNC0yNFY0NDhjMzUuMyAwIDY0LTI4LjcgNjQtNjRoNDBjMTMuMyAwIDI0LTEwLjcgMjQtMjRzLTEwLjctMjQtMjQtMjRINDQ4VjI4MGg0MGMxMy4zIDAgMjQtMTAuNyAyNC0yNHMtMTAuNy0yNC0yNC0yNEg0NDhWMTc2aDQwYzEzLjMgMCAyNC0xMC43IDI0LTI0cy0xMC43LTI0LTI0LTI0SDQ0OGMwLTM1LjMtMjguNy02NC02NC02NFYyNGMwLTEzLjMtMTAuNy0yNC0yNC0yNHMtMjQgMTAuNy0yNCAyNFY2NEgyODBWMjRjMC0xMy4zLTEwLjctMjQtMjQtMjRzLTI0IDEwLjctMjQgMjRWNjRIMTc2VjI0ek0xNjAgMTI4SDM1MmMxNy43IDAgMzIgMTQuMyAzMiAzMlYzNTJjMCAxNy43LTE0LjMgMzItMzIgMzJIMTYwYy0xNy43IDAtMzItMTQuMy0zMi0zMlYxNjBjMC0xNy43IDE0LjMtMzIgMzItMzJ6bTE5MiAzMkgxNjBWMzUySDM1MlYxNjB6Ii8+PC9zdmc+Cg==
[fc-class-certificate]: https://img.shields.io/badge/proof%20provenance-certificate-black?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA1MTIgNTEyIiBmaWxsPSJ3aGl0ZSI+PHBhdGggZD0iTTMxMiAyMDEuOGMwLTE3LjQgOS4yLTMzLjIgMTkuOS00N0MzNDQuNSAxMzguNSAzNTIgMTE4LjEgMzUyIDk2YzAtNTMtNDMtOTYtOTYtOTZzLTk2IDQzLTk2IDk2YzAgMjIuMSA3LjUgNDIuNSAyMC4xIDU4LjhjMTAuNyAxMy44IDE5LjkgMjkuNiAxOS45IDQ3YzAgMjkuOS0yNC4zIDU0LjItNTQuMiA1NC4yTDExMiAyNTZDNTAuMSAyNTYgMCAzMDYuMSAwIDM2OGMwIDIwLjkgMTMuNCAzOC43IDMyIDQ1LjNMMzIgNDY0YzAgMjYuNSAyMS41IDQ4IDQ4IDQ4bDM1MiAwYzI2LjUgMCA0OC0yMS41IDQ4LTQ4bDAtNTAuN2MxOC42LTYuNiAzMi0yNC40IDMyLTQ1LjNjMC02MS45LTUwLjEtMTEyLTExMi0xMTJsLTMzLjggMGMtMjkuOSAwLTU0LjItMjQuMy01NC4yLTU0LjJ6TTQxNiA0MTZsMCAzMkw5NiA0NDhsMC0zMiAzMjAgMHoiLz48L3N2Zz4K
[fc-class-prototype]: https://img.shields.io/badge/proof%20provenance-prototype-black?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA0NDggNTEyIiBmaWxsPSJ3aGl0ZSI+PHBhdGggZD0iTTI4OCAwTDE2MCAwIDEyOCAwQzExMC4zIDAgOTYgMTQuMyA5NiAzMnMxNC4zIDMyIDMyIDMybDAgMTMyLjhjMCAxMS44LTMuMyAyMy41LTkuNSAzMy41TDEwLjMgNDA2LjJDMy42IDQxNy4yIDAgNDI5LjcgMCA0NDIuNkMwIDQ4MC45IDMxLjEgNTEyIDY5LjQgNTEybDMwOS4yIDBjMzguMyAwIDY5LjQtMzEuMSA2OS40LTY5LjRjMC0xMi44LTMuNi0yNS40LTEwLjMtMzYuNEwzMjkuNSAyMzAuNGMtNi4yLTEwLjEtOS41LTIxLjctOS41LTMzLjVMMzIwIDY0YzE3LjcgMCAzMi0xNC4zIDMyLTMycy0xNC4zLTMyLTMyLTMyTDI4OCAwek0xOTIgMTk2LjhMMTkyIDY0bDY0IDAgMCAxMzIuOGMwIDIzLjcgNi42IDQ2LjkgMTkgNjcuMUwzMDkuNSAzMjBsLTE3MSAwTDE3MyAyNjMuOWMxMi40LTIwLjIgMTktNDMuNCAxOS02Ny4xeiIvPjwvc3ZnPgo=
[fc-class-reference]: https://img.shields.io/badge/proof%20provenance-reference-black?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA0NDggNTEyIiBmaWxsPSJ3aGl0ZSI+PHBhdGggZD0iTTk2IDBDNDMgMCAwIDQzIDAgOTZMMCA0MTZjMCA1MyA0MyA5NiA5NiA5NmwyODggMCAzMiAwYzE3LjcgMCAzMi0xNC4zIDMyLTMycy0xNC4zLTMyLTMyLTMybDAtNjRjMTcuNyAwIDMyLTE0LjMgMzItMzJsMC0zMjBjMC0xNy43LTE0LjMtMzItMzItMzJMMzg0IDAgOTYgMHptMCAzODRsMjU2IDAgMCA2NEw5NiA0NDhjLTE3LjcgMC0zMi0xNC4zLTMyLTMyczE0LjMtMzIgMzItMzJ6bTMyLTI0MGMwLTguOCA3LjItMTYgMTYtMTZsMTkyIDBjOC44IDAgMTYgNy4yIDE2IDE2cy03LjIgMTYtMTYgMTZsLTE5MiAwYy04LjggMC0xNi03LjItMTYtMTZ6bTE2IDQ4bDE5MiAwYzguOCAwIDE2IDcuMiAxNiAxNnMtNy4yIDE2LTE2IDE2bC0xOTIgMGMtOC44IDAtMTYtNy4yLTE2LTE2czcuMi0xNiAxNi0xNnoiLz48L3N2Zz4K
[fc-class-canonical]: https://img.shields.io/badge/proof%20provenance-canonical-black?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA1MTIgNTEyIiBmaWxsPSJ3aGl0ZSI+PHBhdGggZD0iTTI0My40IDIuNmwtMjI0IDk2Yy0xNCA2LTIxLjggMjEtMTguNyAzNS44UzE2LjggMTYwIDMyIDE2MGwwIDhjMCAxMy4zIDEwLjcgMjQgMjQgMjRsNDAwIDBjMTMuMyAwIDI0LTEwLjcgMjQtMjRsMC04YzE1LjIgMCAyOC4zLTEwLjcgMzEuMy0yNS42cy00LjgtMjkuOS0xOC43LTM1LjhsLTIyNC05NmMtOC0zLjQtMTcuMi0zLjQtMjUuMiAwek0xMjggMjI0bC02NCAwIDAgMTk2LjNjLS42IC4zLTEuMiAuNy0xLjggMS4xbC00OCAzMmMtMTEuNyA3LjgtMTcgMjIuNC0xMi45IDM1LjlTMTcuOSA1MTIgMzIgNTEybDQ0OCAwYzE0LjEgMCAyNi41LTkuMiAzMC42LTIyLjdzLTEuMS0yOC4xLTEyLjktMzUuOWwtNDgtMzJjLS42LS40LTEuMi0uNy0xLjgtMS4xTDQ0OCAyMjRsLTY0IDAgMCAxOTItNDAgMCAwLTE5Mi02NCAwIDAgMTkyLTQ4IDAgMC0xOTItNjQgMCAwIDE5Mi00MCAwIDAtMTkyek0yNTYgNjRhMzIgMzIgMCAxIDEgMCA2NCAzMiAzMiAwIDEgMSAwLTY0eiIvPjwvc3ZnPgo=
