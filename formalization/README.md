# Lean formalization

Lean 4 (toolchain `leanprover/lean4:v4.34.0-rc2`) with Mathlib at revision `2631d1cc8c2ace6c6a900425d6e5d2b5963966e9`.

```sh
lake exe cache get      # downloads the Mathlib build for this revision
lake build              # builds every module; warnings are errors
lake env lean Axioms.lean
```

`Axioms.lean` runs `#print axioms` on 200 results, including every one cited in the paper; `axioms_output.txt` is its output. Each result depends only on `propext`, `Classical.choice` and `Quot.sound`. No file contains `sorry`, an `axiom` declaration or `native_decide`.

## Modules

| File | Paper | Content |
|---|---|---|
| `ASGA/Basic.lean` | `sec:model` | Hockey-stick divergence (supremum over measurable sets), total variation, testing tradeoff, `Φ`, `g_σ`, `γ_σ`, finite measures on `Fin n`. |
| `ASGA/Envelope.lean` | `thm:main`, `sec:composition` | The envelope `f`, its shape, `T_{P,Q} ≥ f`, the explicit rational pair of `eq:atoms`, its tradeoff `f`, domination in both directions (`envelope_pair_exists`), and `H_ε(Q,P) = 1 - e^ε + e^ε H_{-ε}(P,Q)`. |
| `ASGA/CloneCoupling.lean` | `lem:clone` | TV transfer with cost `(1+k)β`, the modified kernel and `TV = η_u`, the hybrid bound for history-dependent kernels, mixtures, data processing, likelihood-ratio form. |
| `ASGA/Gaussian.lean` | `eq:gamma`, `eq:gaussian`, `prop:counts`, `eq:tau` | Gaussian profile, lognormal identities, `η_u ≤ γ_σ(p)` in every dimension, recurrences and convexity of `F_m`, `J_m`, the bound of `prop:counts` from the conclusions of `lem:clone`, tail correction. |
| `ASGA/Reflection.lean` | `app:reflection` | The pair `eq:chua` is strictly improved by the final-query switch, in both directions, for every `T ≥ 2`, `σ > 0`, `ε ≥ 0`. |
| `ASGA/Certificate.lean` | `app:certificate` | Endpoint spreads and convex order (`eq:spread` and the Poisson spread), the chord induction for `F_m` and `J_m` on a node grid with its boundary identities, relocation of rounded-away mass, the tail correction, soundness of the conditional convolution given the convex-order and truncation hypotheses (`certificate_call_sound`, `certificate_put_sound`), the upper profile `eq:upperpld` and the lower profile for products, carry-free integer packing, and the decimal ratios quoted in the text. |
| `ASGA/Link.lean` | `eq:recurrences` | The functions `F_m`, `J_m` of `prop:counts` equal the recursions bounded in `Certificate.lean`. |

## Not formalized

These steps are proved on paper only:

- the reduction from the shuffled mechanism to the conditional experiment of `lem:clone` (the uniform-partition construction, the clone coupling and the simulation with feedback) and the identification of that experiment's likelihood ratio with `L_K`;
- the cap of each conditional epoch by `g_σ` in `prop:counts`;
- the adaptive composition theorem of Zhu, Dong and Wang used for the second claim of `thm:main`;
- the attainment of the product pair and the distribution `eq:maxcdf` behind the lower endpoints;
- the passage from the per-bin convex-order inequality to domination of the discretized Poisson experiment, and the Gaussian composition behind the deterministic brackets;
- the passage from batch sums to translated densities in `app:reflection`.

The closed form of `eq:tau` (`Gaussian.integral_lr_sub_truncLR`, truncation in the normal input) and the Lipschitz correction in `Certificate.lean` (truncation by a map on the likelihood-ratio axis) are separate statements; no theorem joins them. The Lean files do not verify the Python and C++ programs in `../certificate`: binary64 and MPFR rounding are not modelled, and computed quantities enter the certificate theorems only through inequality hypotheses (for example, that a stored node value dominates the chord recursion).
