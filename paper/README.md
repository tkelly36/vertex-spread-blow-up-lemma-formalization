# Source manuscript

This formalization follows:

> Tom Kelly, *A Vertex-Spread Blow-Up Lemma*.

The original manuscript source was frozen at publication checkpoint
`0502013edc6e`, tagged `exp-E255-success`. The completed formalization also
incorporates the colour-round addendum ratified during the final Trellis run.

The [manuscript PDF](main.pdf) and its self-contained LaTeX source are included
here. Build the PDF with `latexmk -pdf main.tex` from this directory.

This is the manuscript used by the completed run, including the later
colour-round addendum, with the author's requested remark appended to the
introduction and the two associated bibliography entries added. All text from
the definitions section onward and the addendum are unchanged from that
completed-run manuscript. The presentation follows the author's LaTeX
template, with the required manuscript macros retained locally in
`mystyle.sty`.

The two cited independent works are listed as preprints: no published journal
version was found when checked on October 15, 2026. Nenadov's
[publication list](https://sites.google.com/view/rajkon) lists the Nenadov–Pham
paper as submitted, and Kohayakawa's
[publication list](https://www.ime.usp.br/~yoshi/fullpubs.pdf) lists the
Allen–Böttcher–Kohayakawa–Neve paper as submitted. The bibliography uses the
author spellings in the papers, including Böttcher; Pham is unaccented.

The formalization target is the manuscript label `lem:spread-blowup`, whose
Lean counterpart is `SpreadBlowup`. The final formalization checkpoint is
`2c9924e1bc633639c6f5dc54c617c17e75debbd1` (Trellis cycle 322).

The paired TeX files under `formalization/Tablet/` document the statements and
proofs of the formal proof nodes. The repository's main README and public
formalization viewer give entry points to the completed development.
