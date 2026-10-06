# Paper source

Run `./build.sh` with a TeX installation containing IEEEtran, amsmath, amsthm, microtype, booktabs, etoolbox, hyperref, and pgfplots. TeX Live's publishers and pictures collections provide the relevant class and plot packages. A generated `.bbl` is included for inspection; BibTeX or BibTeX8 rebuilds it from `references.bib`.

The manuscript uses the official IEEE SaTML-required declaration `\documentclass[conference]{IEEEtran}` with its default 10-point font and page geometry. The abstract heading uses a colon separator. The source of the requirement is https://satml.org/call-for-papers/ (checked October 5, 2026). The document includes the venue's Open Science and LLM-usage sections. This is an author-named working manuscript, not an anonymized submission or an accepted paper. No claim of submission eligibility or venue acceptance is made.

The pgfplots figures are drawn directly from the certified tables `comparison_sigma1.dat` and `comparison_sigma2.dat`. Axes are logarithmic vertically; lines join certified markers. Product-pair curves are lower certificates from a coarsened statistic, and the Poisson curve is an upper guarantee for a different sampler. The certificate appendix gives the exact interpretation of each curve.

To regenerate the numerical inputs, run `run_all.py` in the accompanying certificate directory. It writes the tables to its sibling paper directory. All class files and fonts are loaded from the user's TeX installation; no font files are distributed.
