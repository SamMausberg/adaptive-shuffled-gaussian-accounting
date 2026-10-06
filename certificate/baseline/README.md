# Certified adaptive Gaussian reshuffling accountant

This artifact supports T = 1000 batches per epoch and noise multipliers 1 and 2.
The theorem in the companion paper covers every batch size and output dimension,
arbitrary common-record heterogeneity, and measurable queries selected from all
previous releases. Each epoch must use a fresh independent uniform permutation.
Adjacency replaces one item by a zero-contributing item without deleting its slot.
The Gaussian releases are ideal real-valued releases. No implementation of a
floating-point Gaussian sampler is being certified.

## Reproduce from the beginning

Use Python 3.10 or later. No third-party numerical package is required.

```
python run_all.py
```

This rebuilds all one-epoch bounds, the exact rational dominating pairs, and the
accepted multi-epoch results. The witness files contain choices of inequalities
and rational parameters only. Their numerical truth is rechecked. Both tails in
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

`dominating_pair_sigma1.json` and `dominating_pair_sigma2.json` contain exact
rational probabilities P and Q. Each finite atom has likelihood ratio
(51/50)^j, where j is its `loss_index`. The `P_only` and `Q_only` atoms must both be
retained. P is oriented as the real-record hypothesis, Q as the null hypothesis.
The pair dominates the entire conditional epoch experiment for every incoming
history. Independent products therefore dominate fully adaptive composition.
The two reverse-oriented PLDs are not interchangeable.

The paired finite probabilities are exact Fractions, not rounded normalizations.
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
`verified_results.json` holds the accepted results; the smaller per-sigma result
files contain the same endpoints. `manifest.json` records reproducible hashes.

The computational certificate verifies the stated mathematical inequalities.
Its connection to the adaptive mechanism rests on the proofs in the paper.
It is not a proof-assistant formalization or an independent peer review.
