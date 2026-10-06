# Paper source

`main.tex` uses `\documentclass[conference]{IEEEtran}` with its default 10-point font and page geometry.

Run `./build.sh` with a TeX installation that provides IEEEtran, amsmath, amsthm, mathtools, microtype, booktabs, hyperref and pgfplots (TeX Live's publishers and pictures collections contain the class and the plotting package). A generated `main.bbl` is included; BibTeX or BibTeX8 rebuilds it from `references.bib`.

The two figures are drawn by pgfplots directly from `comparison_sigma1.dat` and `comparison_sigma2.dat`. These tables are written by `../certificate/run_all.py`, and `../certificate/check_paper_numbers.py` checks the numbers quoted in the text against the same outputs.
