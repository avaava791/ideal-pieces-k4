# There is no ideal pair-piece family for the crossing at K = 4

A short note on Remark 2.9 of arXiv:2610.41622 (a claim under review).

**Result.** For every exact decomposition f = Σ πᵢ of the crossing
f(x,y,u,v) = [x=v][y=u], with N = 2^m values per leg,

    Σᵢ min(rank_row(πᵢ), rank_col(πᵢ)) ≥ N.

So a family of 2^{o(m)} pieces of cost (2,0) and (0,2) per bit does not exist,
and the family {(2,x),(x,2)}, 0 < x < 1, of §4.6 is not admissible.
The gap [N³, N^3.547] of Remark 2.9 remains open.

## Contents

- `note.tex`, `note.pdf`: the note (4 pages). Build: `pdflatex note.tex` (run twice) or `tectonic note.tex`
- `lean/`: a standalone Lean 4 + Mathlib project with the formal proof
  - `lean/IdealPieces.lean`, main theorem `IdealPieces.card_le_sum_min_rank`
  - Build: `cd lean && lake exe cache get && lake build`
  - Toolchain: `leanprover/lean4:v4.37.0-rc1`
  - No `sorry`. Axioms: `propext`, `Classical.choice`, `Quot.sound`

## Author

avaava791 (independent). The argument and the note were prepared with the
assistance of Claude (Anthropic).

## License

- Note (`note.tex`, `note.pdf`): CC BY 4.0
- Lean code (`lean/`): Apache License 2.0

## Citation

See `CITATION.cff`.
