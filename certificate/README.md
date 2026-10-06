# Certified accounting for adaptive shuffled Gaussian training

This archive accompanies Samuel Mausberg's working manuscript, “Certified Accounting for Adaptive Shuffled Gaussian Training.” It contains a reusable upper accountant and the complete computations behind the paper's lower/upper comparisons. The accepted table is `verified_results.json`; exact rational endpoints are encoded as `[numerator, denominator]` strings.

## Scope

The shuffled mechanism has 1000 fixed-size batches per epoch. Every epoch uses a fresh independent uniform permutation. Clipped item queries have Euclidean norm at most one and may depend on all preceding noisy releases, including releases in earlier epochs. Adjacency replaces one item by an inert zero record while preserving its slot. Common records may be heterogeneous; the upper guarantee holds in every batch size and finite dimension. Noise is ideal independent Gaussian noise with standard deviation `sigma` on each sum.

The supplied profiles support `sigma=1` and `sigma=2`. They are not a certificate for reused permutations, arbitrary replacement of one real item by another, data-dependent batch selection, released batch identities, or a particular floating-point Gaussian sampler. Clipping by a public constant C and adding noise of standard deviation sigma*C gives the same normalized model. Division by a fixed or expected batch size is postprocessing; division by a realized Poisson batch size is outside this comparison.

The Poisson option is a different mechanism. Each item is included independently with probability 1/1000 at each update, for 1000 times the epoch count updates. It matches sum noise and expected batch size. The tool never substitutes that guarantee for fixed-size shuffling.

The lower benchmark coarsens the continuous Chua product pair to per-epoch coordinate-maximum bins. Its lower inverse endpoints are attainable lower bounds for the continuous pair and for the unrestricted shuffled query transcript. Upper inverse endpoints of the coarsened statistic apply only to that statistic. They are not continuous-pair upper bounds. A final trained model can have smaller privacy loss than the full transcript.

## Quick use

A 64-bit Linux environment with Python and the GNU MPFR shared library is required. The accepted run used Python 3.13.5 and GNU MPFR 4.2.2. The ctypes wrapper checks the 64-bit public MPFR layout; another ABI needs a reviewed binding. Do not disable Python assertions.

From the `certificate` directory:

```sh
python account.py --sampler shuffle --sigma 1 --epochs 5 --delta 1e-8 --epsilon 7.97
python account.py --sampler shuffle --sigma 2 --epochs 5 --delta 1e-8 --epsilon 0.71
python account.py --sampler poisson --sigma 1 --epochs 5 --delta 1e-8 --epsilon 0.507
python account.py --sampler poisson --sigma 2 --epochs 5 --delta 1e-8 --epsilon 0.182
```

Omit `--epsilon` for a certified cent-grid inverse search. Explicit epsilon evaluation accepts finer rational or decimal inputs. The interface accepts one through 100 epochs and target delta between 1e-12 and 1/2. A coarse grid or accumulated numerical deficits can prevent a requested certificate; the program then reports failure rather than inferring privacy. Its stdout contains both divergence upper bounds and a `certified` flag. Exit status 2 means the chosen epsilon was not certified; it does not prove a privacy violation.

Cached input checksums are verified before composition when `manifest.json` is present. A checksum detects file changes; it is not a substitute for checking the mathematical reduction or rebuilding the probabilities. For shuffling the interface may use the valid deterministic Gaussian fallback when that is sharper.

## Full reconstruction

The full run also requires GNU C++ and NumPy/SciPy. The accepted environment used g++ 14.2.0, NumPy 2.3.5, and SciPy 1.17.0 on x86-64 Linux. NumPy and SciPy propose clone parameters only. Every accepted proposed parameter is reevaluated by directed interval arithmetic; proposal accuracy is not part of the certificate.

```sh
python run_all.py
python verify_checks.py
```

`run_all.py` compiles the conditional-convolution program with

```sh
g++ -O2 -std=c++17 -frounding-math -ffp-contract=off -fno-fast-math candidate_dp.cpp -o candidate_dp
```

It rebuilds Gaussian-bin and endpoint-spread probabilities, checks that the C++ input is an exact serialization of its rational JSON, reconstructs both conditional positive-part recurrences, reevaluates threshold-specific clone probabilities, builds the exact rational dominating pair, and composes it. It then reconstructs the attainable lower benchmark and the continuous Poisson upper comparison. Finally it runs additional arithmetic checks, collects the tables, and writes a new checksum manifest. It creates a sibling `paper` directory containing the generated pgfplots tables if that directory does not already exist.

A successful complete reconstruction is recorded in `full_reproduction.log`. The log's elapsed times and diagnostic floating-point displays are not the numerical privacy certificates; the JSON files contain the exact accepted inequalities. The supplied executable binary is intentionally omitted: the source and compilation command are included. Review the flags and rounding behavior before using a different compiler or architecture.

## Proof and computation map

`candidate_prepare.py` constructs convex endpoint-spread laws for the truncated lognormal likelihood ratio. The normal mesh is 1/50 on [-10,10]; the explicit tail correction accounts for the entire omitted first moment. Support uses 30 fractional bits, probabilities use 72 fractional bits, and every missing probability is moved in the conservative direction. `candidate_dp.cpp` computes upper conditional call and put functions for counts through 64 or 160 using positive arithmetic rounded upward. The threshold grid has relative spacing at most approximately 1/400; its exact integer nodes are in the inputs. No convergence assumption is used.

`refine_candidates.py` combines these values with certified binomial probabilities and a Gaussian upper bound for all remaining counts. The clone exponent h is selected from a rational grid of spacing 1/40. Its ranges are [3.5,9.5] at sigma=1 and [1.625,6] at sigma=2. All final threshold bounds are rounded upward and checked separately by direction. Small candidate counts are not discarded.

`compose.py` builds the testing envelope at likelihood thresholds (51/50)^j, j=0,...,555, as an exact rational binary experiment. Its finite probability masses are rounded downward to 56 bits. Packed integer multiplication computes convolution coefficients exactly; all missing mass is charged at infinite privacy loss. `dominating_pair_sigma*.json` can be reused without reconstructing the one-epoch profile.

`pair_maximum.py` uses exact Gaussian CDF differences for maximum bins at sigma*j/100, j=0,...,1200, including both infinite end bins. It computes lower and upper rounded-loss products with likelihood mesh ratio 2001/2000. Only its lower bounds transfer to the full continuous pair. `poisson_account.py` instead constructs an upper endpoint-spread experiment for the continuous one-step Poisson mechanism with mesh ratio 10001/10000, then composes 1000*E steps. Both use 72-bit retained masses and the exact integer convolution in `lattice.py`. Cropped or rounded-away mass is discarded for lower bounds and charged at infinite loss for upper bounds.

`mpinterval.py` requests explicit downward/upward MPFR rounding for every primitive at 256-bit precision and exports exact dyadic fractions. `intervals.py` retains an independent rational-series enclosure used for the original Gaussian comparison and selected cross-checks. `verify_checks.py` compares these primitive enclosures, verifies packed multiplication against naive integer convolution on small inputs, checks likelihood-score calculations directly, tests conditional moment inequalities, and verifies preservation of the Poisson one-step profile at a grid threshold. These are additional implementation checks, not independent human review or formal verification.

## Files and provenance

The paper and proof source are in the sibling `paper` directory. `verified_results.json` and `comparison_sigma*.dat` contain the accepted comparison. `results_sigma*.json`, `pair_maximum_results_sigma*.json`, and `poisson_results_sigma*.json` retain each calculation's exact directional endpoints and scope. Input files and intermediate convolution arrays are included so that individual stages can be inspected without rerunning the whole artifact.

`baseline/` preserves the prior moment/Laplace null-clone implementation and its certificates supplied in the preceding research round. It is used only for the explicitly labeled ablation. The new upper proof and computations do not assume those bounds. `checks/coarse_results_sigma*.json` records a second conservative computation using a coarser mesh; it is not used to interpolate or certify the fine run. To recompute the inherited baseline, run its `run_all.py` separately in that directory.

The cloning principle and approximate-kernel replacement are credited to Feldman, McMillan, and Talwar, “Hiding Among the Clones” (FOCS 2021; arXiv:2012.12803). Dominating-pair and discretization foundations are credited to Zhu, Dong, and Wang (AISTATS 2022), Gopi, Lee, and Wutschitz (NeurIPS 2021; arXiv:2106.02848), and Doroshenko et al. (PoPETs 2022; arXiv:2207.04380). The benchmark is from Chua et al. (ICML 2024; arXiv:2403.17673), with its multi-epoch construction in “Scalable DP-SGD” (NeurIPS 2024; arXiv:2411.04205). Full bibliographic entries and the independent-allocation distinction are in the manuscript.

The source and proofs were developed with GPT-6 Astra Pro assistance. The artifact's deterministic verification path uses no language model or training dataset. The results have received internal proof and arithmetic checks, not independent mathematical review. Human author review and a publication license decision remain necessary before release as production accounting software.
