# Manuscript and formalization

Use `material/manuscript.tex` as the mathematical reference. Preserve its
hypotheses, conclusions, notation, and proof strategy. Use established
mathematical terminology and the manuscript's names for states, operators,
measurements, and results. When a Lean name differs, explain the correspondence.
The manuscript's number of modes satisfies `m ≥ 1`. Coverage of `m = 0`
in Lean is additional generality, not a manuscript requirement.

If you find a possible mathematical gap or error in the manuscript, **stop
formalizing and discuss it with the user before proceeding**. Give the
manuscript location, the precise inference in question, and what would justify
it. If you propose a different proof strategy, stop and discuss that choice
first. Resume proof work only after agreement with the user. Do not silently
alter the manuscript, introduce an unproved assumption, weaken a statement, or
substitute another proof.

Use the [manuscript index](docs/manuscript-index.md) to locate the relevant
statements, Lean declarations, blueprint entries, and remaining mathematical
questions. Give each numbered manuscript theorem one blueprint node. Keep its
statement, checked Lean declarations, and open obligations together. Link to
independently stated lemmas for its mathematical prerequisites.
Update the manuscript index and the corresponding blueprint entries
when the manuscript or the proofs change. Run
`python3 scripts/manuscript_map.py --write` to regenerate the Markdown and
TeX, then `python3 scripts/manuscript_map.py --check-lean` after `lake build`.

Keep material proved as part of a manuscript proposition or theorem with that
result's blueprint node, including intermediate arguments in its proof.
The Gaussian preliminaries nodes collect reusable background used by the
manuscript's results, not steps of those results' proofs. For example, the
positivity and polarization argument belongs to Proposition 6.1, while Weyl
operators and general characteristic-function properties belong to the
bosonic preliminaries.

Limit preliminaries to statements needed to carry out the manuscript's proofs.
Do not expand the task into a general development of Gaussian quantum mechanics.
Background descriptions such as metaplectic lifts, quadratic-Hamiltonian ground
states, or exponential identifications need not be formalized unless a proof of
one of the section's results actually depends on them. Distinguish such unused
background from prerequisites that block a manuscript result.
