# Building and maintaining the formalization

Run these commands from the repository root. The Lean toolchain, Mathlib
revision, and documentation dependencies are pinned in the repository.

## Lean and local checks

Install [elan](https://github.com/leanprover/elan) and put `lake` on your `PATH`.
Elan selects the version in [lean-toolchain](../lean-toolchain).

```sh
lake exe cache get                 # first run: download the Mathlib build cache
lake build
lake env lean scripts/NoSorry.lean
lake env lean scripts/Audit.lean
lake env lean scripts/ManuscriptChecks.lean
python3 scripts/check_readme.py
python3 scripts/manuscript_map.py --check-lean
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The whole-library check rejects `sorry` in public and private declarations and
verifies that every library source is imported. The axiom audit additionally
checks selected declarations against exactly
`[propext, Classical.choice, Quot.sound]`. The manuscript checks verify public
statements and important proof dependencies, including the projective argument
for Theorem 3.4 and the reduced-state argument for Theorem 6.7. The README check
compiles its displayed Lean examples against the public import.

Lean's linters run during `lake build`; cached warnings may be replayed. The
library builds without warnings. Keep the existing linters enabled when
editing proofs. README examples are checked with warnings treated as errors.

## Blueprint and documentation

In addition to Lean, install Python, Graphviz, and a TeX distribution with
`kpsewhich`, `latexmk`, and `pdflatex`. The Python requirements are pinned in
[blueprint/requirements.txt](../blueprint/requirements.txt). Graphviz development
headers and a C compiler may be needed to build its Python binding.
CI uses `texlive-latex-recommended` and `texlive-fonts-recommended` rather than
the larger `texlive-latex-extra` collection.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r blueprint/requirements.txt
leanblueprint web
python3 scripts/manuscript_map.py --check-html
bash blueprint/check-decls.sh
leanblueprint pdf
```

The HTML check validates source links, manuscript references, proof status,
GitHub navigation, and agreement of the compact and wide dependency graphs.
The declaration check uses the existing Lean environment.

To browse locally:

```sh
python3 -m http.server 8000 --bind 127.0.0.1 --directory blueprint/web
```

Open [the blueprint](http://127.0.0.1:8000/),
[compact graph](http://127.0.0.1:8000/dep_graph_document.html), or
[wide graph](http://127.0.0.1:8000/dep_graph_wide.html). Serving over HTTP is
required for the interactive graph. The printed document is
`blueprint/print/print.pdf`.

The committed graph image in the README is rendered from the same graph data:

```sh
python -m pip install cairosvg      # also install the Cairo system library
bash blueprint/render-graph.sh
```

This script uses installed Graphviz and does not download a renderer. On macOS
it discovers Homebrew's Cairo library directory automatically.

Assemble the blueprint HTML and PDF into the complete site with:

```sh
python3 scripts/build_pages.py
python3 -m http.server 8000 --bind 127.0.0.1 --directory _site
```

The blueprint's Lean links open the corresponding `.lean` source on GitHub,
at the commit used to build the blueprint and with a declaration line anchor.
Local builds use `HEAD`; commit Lean source changes and rebuild before assembling
a publishable site, whose checks reject uncommitted linked Lean files.
Site assembly validates these source links, checks local homepage links, and
enforces the published site's size limit. Separate Lean API documentation is
not generated.

## Manuscript and proof updates

Use [material/manuscript.tex](../material/manuscript.tex) as the mathematical
reference. Preserve its hypotheses, conclusions, notation, and proof strategy.
If a mathematical gap or error appears, or a different proof strategy is
needed, discuss it with the authors before proceeding. See [AGENTS.md](../AGENTS.md)
for the project instructions and the [comparison report](manuscript-comparison.md)
for the existing proof correspondences.

Edit [docs/manuscript-map.json](manuscript-map.json) and the corresponding
[blueprint nodes](../blueprint/src/content.tex), then regenerate the index:

```sh
python3 scripts/manuscript_map.py --write
lake build
python3 scripts/manuscript_map.py --check-lean
```

Do not edit the generated Markdown or TeX index by hand. Every numbered
manuscript theorem has one blueprint node containing its statement, checked
proof, and any open obligations. Intermediate arguments stay with that result.
Each section's preliminaries node collects the reusable background actually
needed by its proofs. Unused background qualifications belong in the index
and [coverage guide](coverage.md).

The reference checker derives equation numbers from the manuscript source,
requires every numbered equation label to be indexed, and validates equation
captions in the blueprint. Unsupported numbering conventions fail explicitly.
After compiling the manuscript, compare with LaTeX's references as well:

```sh
python3 scripts/manuscript_map.py --check-equations-aux path/to/manuscript.aux
```

Rebuild the blueprint, declaration checks, and graph image after changing
references or nodes. The graph uses boxes for definitions and ellipses for
results. A green border marks a formalized statement; pale mint marks a
formalized proof; green fill means its proof and all ancestors are formalized.
Pale amber denotes partial coverage. Section backgrounds are faint green when
all their proofs are complete, and light gray otherwise.

## Dependencies and CI

Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` consistent when
updating Lean or Mathlib, and run the full Lean and blueprint checks after an
upgrade. Dependency updates and release creation are deliberate maintenance
operations, not automatic consequences of changing `lean-toolchain`.

The [CI workflow](../.github/workflows/lean_action_ci.yml) runs the Lean build,
audits, README examples, reference tests, blueprint HTML/PDF builds,
and site checks. Successful runs on `main` publish to GitHub Pages. Pull
requests run checks without deploying; newer runs cancel superseded runs for
the same pull request. Runs on `main`, including deployments, are not interrupted.
In the repository's Pages settings,
select **GitHub Actions** as the deployment source.

The blueprint is published directly at
[the site root](https://qit-lmu.github.io/gaussian-testing/), with the PDF at
`blueprint.pdf`. No landing page or deployment branch is needed. Generated
outputs and local caches are ignored by Git.

## Repository layout

| Path | Purpose |
| --- | --- |
| [GaussianTesting.lean](../GaussianTesting.lean) | Public import of the full library. |
| [GaussianTesting/](../GaussianTesting/) | Hilbert-space robustness, Kac operators, fermions, bosons, and testing protocols. |
| [material/](../material/) | Manuscript and bibliography. |
| [blueprint/](../blueprint/) | Blueprint sources, graph rendering, and the committed dependency diagram. |
| [docs/](../docs/) | Coverage, manuscript index, proof comparison, and this guide. |
| [scripts/](../scripts/) | Reproducible audits, reference checks, and documentation assembly. |

The project uses Lean, Mathlib, and leanblueprint. The code is licensed under
[Apache 2.0](../LICENSE). The [manuscript](../material/manuscript.tex) is licensed
under [CC BY 4.0](../material/LICENSE).
