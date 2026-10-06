# Baseline: moment/Laplace evaluation of the null-clone reduction

This directory keeps the earlier moment/Laplace evaluation of the null-clone
reduction, used in the paper only for the ablation (five-epoch upper values 9.21
at sigma=1 and 0.83 at sigma=2). It supports T = 1000 batches per epoch and
noise multipliers 1 and 2. Scope and assumptions are those of `../README.md`.

## Reproduce from the beginning

Use Python 3.10 or later. No third-party numerical package is required.

```
python run_all.py
```

This rebuilds all one-epoch bounds, the exact rational dominating pairs and the
multi-epoch results. The witness files only select inequalities and rational
parameters; every selected inequality is rechecked numerically. Both tails in
the Gaussian-bin Laplace bound are included. There is no Monte Carlo stage in the
certificate and no unquantified numerical-integration error.

## Query the accountant

```
python account.py --sigma 1 --epochs 5 --delta 1e-8 --epsilon 9.21
python account.py --sigma 2 --epochs 5 --delta 1e-8
```

The second command searches a cent grid. It reports an upper privacy bound, not a
lower bound on the true optimum. This interface supports up to 100 epochs and
uses the sensitivity-one Gaussian composition as a fallback. A different order
of rounded convolutions can change the last few digits of a bound; each result
includes its own complete error charge.

## Composable objects

`run_all.py` writes `dominating_pair_sigma1.json` and `dominating_pair_sigma2.json`,
which contain exact rational probabilities P and Q (the pair (R,S) of the paper). Each finite atom has likelihood ratio
(51/50)^j, where j is its `loss_index`. The `P_only` and `Q_only` atoms must both be
retained. P is oriented as the real-record hypothesis, Q as the null hypothesis.
The pair dominates the entire conditional epoch experiment for every incoming
history. Independent products therefore dominate fully adaptive composition.
The two oriented privacy-loss distributions are not interchangeable.

The finite probabilities are exact Python Fractions.
For convolution, P and Q finite masses are rounded down independently to 2^-56.
These arrays are lower submeasures used only to evaluate the exact pair. Every
missing mass, including singular atoms and each convolution rounding, is charged
as infinite privacy loss. Never renormalize these arrays.

## File guide

`intervals.py` supplies dyadic inclusion arithmetic at 1024 fractional bits.
`build_profile.py` verifies analytic moment, variance, and Gaussian inequalities.
`refine_laplace.py` adds a bounded Laplace-transform upper bound for the reverse
profile. `compose.py` constructs and checks the testing-envelope pair, then uses
integer polynomial multiplication to convolve both oriented loss measures.
`run_all.py` also writes `verified_results.json`, which collects the results (the
per-sigma result files contain the same endpoints), and `manifest.json`, which
records file hashes.

The computational certificate verifies the stated mathematical inequalities.
Its connection to the adaptive mechanism rests on the proofs in the paper.
