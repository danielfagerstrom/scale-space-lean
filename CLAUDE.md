# scale-space-lean — Claude Code context

> **Note for public readers.** This file is working context for the author's AI-assisted
> development sessions, kept in the repository as provenance. It references private
> infrastructure — a wiki hub — that is not part of this repository. Nothing in the library depends
> on it; the public verification route is the two `lake` commands in `README.md`.

This file holds this repository's standing rules and nothing else. What this library is, why it
carries no axiom, and how it grows are `README.md`'s; the reasoning behind the rules below is the
hub's ADR-0026 and `RELEASES.md` § "Dependencies between modules" — read those rather than expecting
them restated here.

## Rules

- **Admission is second demand, not design.** A declaration moves in when a *second* article
  actually needs it, by extraction from where it already lives. A single consumer, however general
  the statement looks, is not enough.
- **No `axiom`, no `sorry`.** Where a statement would otherwise need to cite an article's analytic
  interface, it takes what that interface provides as a **hypothesis** of the statement instead; the
  consuming article discharges it from its own ledger. A module that carries an axiom silently
  widens every downstream article's trust base — don't add one.
- **`AxiomCheck.lean` covers every public declaration.** A move or a new declaration that doesn't
  add its `#print axioms` line there is an incomplete move.
- **No import of an article package.** Dependencies run one way: this library may `require`
  `harmonic-semigroups` (once it exists); it never imports a paper's own package. A structure only
  one article uses stays there; one a second article needs moves here with the declarations stated
  in it (the hub's `RELEASES.md`, "The test").
- **Every module says where its home is.** One `Home: …` line in each module's docstring, right
  after the title — `Home: <article>[/<module>]:<label>[, …]` (a blueprint node states it),
  `Home: none (<why>)` or `Home: owed <article> (<what is missing>)`. README.md's "Home" section
  has the full syntax. A module that moves in or is written here gets its line in the same pull
  request as the move. `scripts/gen_library_reference.py --check-source` fails on a module
  without one, or with a malformed one.
- **Tags are the author's.** A session does not cut a release or move `RELEASES.md`'s pin.
- **A move is a move, then a build** — copy the declaration, delete it from its old home, adjust
  the namespace and imports, `lake build`; not an occasion to restate, generalize, or otherwise
  rewrite it. Generalizing is the promotion cycle's job, not an extraction's.

## Commands

```bash
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```
