# Certified Accounting for Adaptive Shuffled Gaussian Training: supplementary material

- `paper/`: LaTeX source of the submission (`\documentclass[conference]{IEEEtran}`), its bibliography and the figure tables.
- `certificate/`: the accountant and every computation behind the numbers in the paper. `python run_all.py` rebuilds all certificates (under three minutes on one core), and `python check_paper_numbers.py` then compares every number quoted in the paper with the regenerated outputs.
- `formalization/`: the Lean 4 development described in the section "Lean formalization" of the paper. `lake exe cache get && lake build` checks it, and `lake env lean Axioms.lean` prints the axioms of each result.

Each directory has its own README with requirements and details.

To package these files for upload, run `git archive --format=zip --prefix=supplementary/ -o supplementary_material.zip HEAD` from a clone; the archive contains only tracked files.
