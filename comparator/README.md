# Comparator certificate for the ICLR manuscript

This directory holds a [Comparator](https://github.com/leanprover/comparator)
challenge/solution pair certifying that the theorems of the manuscript are proved in the
library `LeanDeepgen` from the standard axioms only.

* `Challenge.lean` states every theorem of the paper (one `theorem` per paper label, in
  `namespace LeanDeepgen.Challenge`) with the proof replaced by `sorry`. It imports **only the
  definition modules** of the library (`LeanDeepgen.Setting.*`, `Profiles.Defs`,
  `Tradeoff.Defs`, `Growth.Defs`) plus, for the worked examples of the appendices, the example
  modules `LeanDeepgen.Examples.*` (which contain the example *definitions*; they transitively
  import theorem modules, but no statement in the challenge depends on a theorem). The
  general-purpose tools (`FoML.ToMathlib`, `FoML.ToFoML`) are provided by the dependency
  [lean-rademacher](https://github.com/auto-res/lean-rademacher). Everything
  in the import closure of the challenge is the trusted "vocabulary" of the certificate.
* `Solution.lean` imports the whole library and proves each challenge statement by the
  corresponding library theorem (`:= LeanDeepgen.<name> <args>`).
* `config.json` lists the 64 theorem names (55 of the original certificate, 6 added on
  2026-09-25 for the new results `prop:envelope`, `cor:envelope-profiles`, `lem:reachable-radius`,
  `lem:ode-scheme-entropy`, `lem:cot-branch-sample`, and 3 added on 2026-09-26 for the deep ReLU
  appendix, `lem:relu-layer-covering`, `prop:relu-regimes`, `prop:relu-regimes-iii-lower`) and
  the permitted axioms `propext`, `Quot.sound`, `Classical.choice`. `./script/comparator.sh` was
  re-run on 2026-09-26 with all 64 theorems: "Your solution is okay!".

Comparator checks that each listed theorem has, in `Solution`, exactly the statement given in
`Challenge` (all constants occurring in the statement are identical in both environments) and
that its proof uses only the permitted axioms. Each challenge statement is copied verbatim
(binders, implicitness, hypothesis order, universe levels) from the library theorem; the
`open` lines of each section reproduce the context of the source module so both files
elaborate to identical kernel terms. The one exception is `thm_dudley_subgaussian`, whose
auxiliary definitions live in a theorem module (`FoML/ToFoML/DudleySubGaussian`) and are therefore
unfolded inline in the challenge.

## How to run

```sh
# once: tools in ../comparator-tools/ (see the top-level README, "Comparator による検証")
./script/comparator.sh          # builds Challenge and Solution, exports, runs the checker
lake build Challenge Solution   # fast iteration on the two files
```

The expected last line of the output is `Your solution is okay!`.

## Statements and the revised manuscript

The challenge states each theorem in its *Lean* form, i.e. as the manuscript will read after
the revisions listed in [`ToDraft.md`](../ToDraft.md) (necessary fixes D1–D36 and the adopted
generalizations W4–W28). In particular the challenge already incorporates:

* explicit constants in `thm:bv` / `thm:bv-general` (`6b√(2 log(4/δ)/n)`, gap `3b√(…)`),
  measurability, `b > 0` and pointwise boundedness of the hypothesis class (D1, D3), and the
  gap form for every `f ∈ 𝓗` (D2);
* integrability of the Dudley integrand in `thm:hidden-decomp` and `thm:rad.decomp.ent.ent`,
  with the covering-number convention fixed (D5, D6, D34); arbitrary anchor `f₀ ∈ F` (W5); the
  sample version of the entropy decomposition (W8);
* `prop:hilbert-sg` for real inner product spaces (W6);
* finiteness of the Rademacher suprema and an arbitrary hidden class `B` in
  `thm:sudakov-type` (D7, W7); `k ≥ 1` in the polynomial rates (D32);
* growth conditions: no compactness in P1 (1) (W10), all `k` / nonempty invariant set /
  bounded absorbing set / `0 < c` in P1' (D12, W11), `k ≥ 0` and explicit constant in P2 (D13,
  W12), freeness dropped in E1 (W13), `r ≥ 2` and no isometry in E1' (D15, W14), disjoint
  chambers in E2 (W15), quantified "small `ε`" (`ε < 1/2`, `ε < λδ₀/2`) and no compactness of
  `G` in E3 and its corollaries (D17, D18, W16);
* sign/normalization hypotheses in the profiles (D20, W18–W20);
* two-sided `Θ` trade-off rates with explicit balancing depths (Lambert-W-free `k*` for PL) and
  the exact PP balancing (D22, W21, W22);
* examples: `≤ N(ℋ_k, ε/2)` and no compactness in `prop:implementation` (a) (D24, W23),
  `r ≥ 2` in `lem:cot-branch-growth` (D26), all `ε > 0` in `lem:cot-append-growth` (D27/W25),
  co-coercivity form of `lem:fp-contraction` (D28), saturation without time-stamp consistency
  (D29/W26), no distinctness in `prop:linear-interpolation` (D30/W27), `R_Φ > 0` (D31), window
  feature map only in `lem:cot-output` (W28), and rigorous versions with explicit constants of
  `prop:cot-append`, `prop:ode-fixedpoint`, `prop:ode-horizon` (D33);
* deep ReLU appendix (2026-09-26, R1–R6 in `ToDraft.md`): `R_K` any bound `‖x‖ ≤ R_K ≥ 0` on
  `K`, explicit `C_F = 2(2β_W R_K + β_W + β + 1) max{β_W, β}` in `lem:relu-layer-covering` (R1);
  `K ≠ ∅`, `0 < Λ` and all `k` in `prop:relu-regimes` (i), the `(1 + C/ε)` form of the envelope
  profile with `log(1 + 2C_F/D̄)` in (ii)/(iii) (R2); width `w ≥ 4`, `Λ ≥ 20`, `β_W ≥ 41`,
  `β ≥ 2` in the lower bound of (iii) (R3).

The three ReLU theorems were added to `Challenge.lean` / `Solution.lean` / `config.json` on
2026-09-26; `./script/comparator.sh` was re-run the same day with all 64 theorems: "Your
solution is okay!" (commit `aa16b1e`).

## Mapping: paper label → challenge theorem → library theorem

| Paper label | `LeanDeepgen.Challenge.` | Library theorem (`LeanDeepgen.`) | Module |
|---|---|---|---|
| `thm:bv-general` | `thm_bv_general` | `bv_general` | `Bounds/BiasVariance` |
| `thm:bv-general` (gap) | `thm_bv_general_gap` | `bv_general_gap` | `Bounds/BiasVariance` |
| `thm:bv` | `thm_bv` | `bv` | `Bounds/BiasVariance` |
| `thm:bv` (gap) | `thm_bv_gap` | `bv_gap` | `Bounds/BiasVariance` |
| `thm:hidden-decomp` (= `thm:mixed-sg`) | `thm_hidden_decomp` | `hidden_decomp` | `Bounds/HiddenOutput` |
| `thm:hidden-decomp` (depth `k`) | `thm_hidden_decomp_depth` | `hidden_decomp_depth` | `Bounds/HiddenOutput` |
| `prop:hilbert-sg` | `prop_hilbert_sg` | `hilbert_sg` | `Bounds/HiddenOutput` |
| `prop:finite-lipschitz-sg` | `prop_finite_lipschitz_sg` | `finite_lipschitz_sg` | `Bounds/HiddenOutput` |
| `thm:sudakov-type` (= `thm:sudakov`) | `thm_sudakov_type` | `sudakov_type` | `Bounds/Sudakov` |
| `cor:sudakov-rates` (i) | `cor_sudakov_rates` | `sudakov_rates_exp` | `Bounds/Sudakov` |
| `cor:sudakov-rates` (ii) | `cor_sudakov_rates_poly` | `sudakov_rates_poly` | `Bounds/Sudakov` |
| `cor:matching` (i) | `cor_matching` | `matching_exp` | `Bounds/Sudakov` |
| `cor:matching` (ii) | `cor_matching_poly` | `matching_poly` | `Bounds/Sudakov` |
| `thm:rad.decomp.ent.ent` *(not printed in the current manuscript; kept in the library — formerly App. E of the ICLR draft)* | `thm_rad_decomp_ent_ent` | `rad_decomp_ent_ent` | `Bounds/EntropyDecomp` |
| `thm:rad.decomp.ent.ent` (sample) *(not printed in the current manuscript; kept in the library — formerly App. E of the ICLR draft)* | `thm_rad_decomp_ent_ent_sample` | `rad_decomp_ent_ent_sample` | `Bounds/EntropyDecompSample` |
| `thm:caa` *(not printed in the current manuscript; kept in the library — formerly App. P of the ICLR draft)* | `thm_caa` | `totallyBounded_unifMaps_iff_equicontinuous` | `Growth/ArzelaAscoli` |
| `cond:p1` (1) | `cond_p1` | `cond_p1_of_totallyBounded` | `Growth/Saturation` |
| `cond:p1` (2a) | `cond_p1_2a` | `cond_p1_of_equicontinuous` | `Growth/Saturation` |
| `cond:p1` (2b) | `cond_p1_2b` | `cond_p1_of_uniformLipschitz` | `Growth/Saturation` |
| `cond:p1` (2c) | `cond_p1_2c` | `cond_p1_of_nonexpanding` | `Growth/Saturation` |
| `cond:p1-ucont` | `cond_p1_ucont` | `cond_p1_ucont` | `Growth/Saturation` |
| `cond:p2-nilp` | `cond_p2_nilp` | `cond_p2_nilp` | `Growth/Polynomial` |
| `cond:e1-free-iso` | `cond_e1_free_iso` | `cond_e1_free_iso` | `Growth/Exponential` |
| `cond:e1p-theoremC` | `cond_e1p` | `cond_e1p_theoremC` | `Growth/Exponential` |
| `cond:e2-pingpong` | `cond_e2_pingpong` | `cond_e2_pingpong` | `Growth/Exponential` |
| `cond:e3` | `cond_e3` | `cond_e3` | `Growth/MemoryExpansion` |
| `cor:superexp` | `cor_superexp` | `cor_superexp` | `Growth/MemoryExpansion` |
| `cor:doubleexp` | `cor_doubleexp` | `cor_doubleexp` | `Growth/MemoryExpansion` |
| `lem:log-split` (inequality) | `lem_log_split` | `log_one_add_div_le` | `Profiles/LogSplit` |
| `prop:profiles` (i) | `prop_profiles_i` | `profile_saturation` | `Profiles/Profiles` |
| `prop:profiles` (ii) | `prop_profiles_ii` | `profile_poly_bounded` | `Profiles/Profiles` |
| `prop:profiles` (iii) | `prop_profiles_iii` | `profile_exp_bounded` | `Profiles/Profiles` |
| `prop:profiles` (iv) | `prop_profiles_iv` | `profile_poly_linear` | `Profiles/Profiles` |
| `prop:profiles-finite` | `prop_profiles_finite` | `profile_finite` | `Profiles/Profiles` |
| `tab:tradeoff` PP | `thm_tradeoff_pp` | `Tradeoff.tradeoff_PP` | `Tradeoff/Regimes` |
| `tab:tradeoff` EP | `thm_tradeoff_ep` | `Tradeoff.tradeoff_EP` | `Tradeoff/Regimes` |
| `tab:tradeoff` EL | `thm_tradeoff_el` | `Tradeoff.tradeoff_EL` | `Tradeoff/Regimes` |
| `tab:tradeoff` PL | `thm_tradeoff_pl` | `Tradeoff.tradeoff_PL` | `Tradeoff/Regimes` |
| `prop:implementation` (a) | `prop_implementation_a` | `prop_implementation_a` | `Examples/Implementation` |
| `prop:implementation` (b) | `prop_implementation_b` | `prop_implementation_b` | `Examples/Implementation` |
| `prop:implementation` (c) | `prop_implementation_c` | `prop_implementation_c` | `Examples/Implementation` |
| `prop:global_scalar_observable` | `prop_global_scalar_observable` | `global_scalar_observable` | `Examples/Readout` |
| `prop:linear-interpolation` | `prop_linear_interpolation` | `linear_interpolation` | `Examples/Readout` |
| `cor:rkhs-readout` | `cor_rkhs_readout` | `rkhs_readout` | `Examples/Readout` |
| `lem:cot-append-growth` | `lem_cot_append_growth` | `cot_append_growth` | `Examples/ChainOfThought` |
| `lem:cot-branch-growth` | `lem_cot_branch_growth` | `cot_branch_growth` | `Examples/ChainOfThought` |
| `lem:cot-output` (window `Φ_L`) | `lem_cot_output` | `lipschitzWith_windowFeature` | `Examples/ChainOfThought` |
| `prop:cot-append` | `prop_cot_append` | `prop_cot_append` | `Examples/ChainOfThought` |
| `lem:fp-contraction` | `lem_fp_contraction` | `fp_contraction` | `Examples/ODE` |
| `lem:ode-saturation` | `lem_ode_saturation` | `ode_saturation` | `Examples/ODE` |
| `lem:ode-euler-error` | `lem_ode_euler_error` | `euler_global_error` | `Examples/ODE` |
| `prop:ode-fixedpoint` | `prop_ode_fixedpoint` | `prop_ode_fixedpoint` | `Examples/ODE` |
| `prop:ode-horizon` | `prop_ode_horizon` | `prop_ode_horizon` | `Examples/ODE` |
| `prop:envelope` (= `prop:envelope-restated`) | `prop_envelope` | `prop_envelope` | `Growth/Envelope` |
| `cor:envelope-profiles` (a), (b) | `cor_envelope_profiles` | `cor_envelope_profiles` | `Growth/Envelope` |
| `lem:reachable-radius` | `lem_reachable_radius` | `lem_reachable_radius` | `Growth/Envelope` |
| `lem:ode-scheme-entropy` (distance, covering) | `lem_ode_scheme_entropy` | `lem_ode_scheme_entropy` | `Examples/ODE` |
| `lem:ode-scheme-entropy` (entropy integral) | `equalSchemeClass_profile` | `equalSchemeClass_profile` | `Examples/ODE` |
| `lem:cot-branch-sample` | `lem_cot_branch_sample` | `lem_cot_branch_sample` | `Examples/ChainOfThought` |
| `lem:relu-layer-covering` | `lem_relu_layer_covering` | `lem_relu_layer_covering` | `Examples/ReLU` |
| `prop:relu-regimes` (i)–(iii), upper bounds | `prop_relu_regimes` | `prop_relu_regimes` | `Examples/ReLU` |
| `prop:relu-regimes` (iii), lower bound (E2) | `prop_relu_regimes_iii_lower` | `prop_relu_regimes_iii_lower` | `Examples/ReLU` |
| `thm:bernoulli-sudakov` (bonus) | `thm_bernoulli_sudakov` | `FoML.ToFoML.bernoulli_sudakov` (lean-rademacher) | `FoML/ToFoML/BernoulliSudakov` |
| `thm:dudley-subgaussian` (bonus, inlined) | `thm_dudley_subgaussian` | `FoML.ToFoML.dudley_subgaussian_finite_space` (lean-rademacher) | `FoML/ToFoML/DudleySubGaussian` |

Not included: the cited theorems `thm:guivarch-bass`, `cor:nilpotent-entropy`,
`thm:breuillard-large-balls` (not formalized; P2 takes their conclusion as a hypothesis), the
`Φ_∞` part of `lem:cot-output` (W28), and the integral identity of `lem:log-split`
(`∫₀^{D̄} √log(D̄/ε) dε = (√π/2) D̄`, used inside the proofs of `prop:profiles` (ii)/(iv) and
stated in `FoML/ToMathlib/SqrtLogIntegral`, a theorem module).

Note (2026-09-26): `thm:rad.decomp.ent.ent` (both forms) and `thm:caa` are a different case from
the paragraph above — they *are* formalized and remain in the comparator challenge, but the
manuscript was pruned on 2026-09-26 and no longer prints the corresponding appendix sections
(formerly App. E, "A deterministic entropy alternative to `thm:hidden-decomp`", and App. P,
"Compact-Domain Arzelà–Ascoli Principle for Self-Maps", in the pre-2026-09-26 lettering — *not*
to be confused with the current Appendix E, "The Sudakov-type converse", which is a different
section under the reorganized lettering A–M introduced later the same day). The Lean modules
`Bounds/EntropyDecomp`, `Bounds/EntropyDecompSample` and `Growth/ArzelaAscoli` are unchanged.

Note (2026-09-26, appendix reorganization): the manuscript's appendix was further reorganized the
same day into a fixed order and lettering A–M (see `SUMMARY.md`): A conventions/basic facts, B
literature, C bias--variance, D hidden--output, E the Sudakov-type converse (`thm:sudakov-type`,
`cor:matching`, `cor:sudakov-rates`, `prop:global_scalar_observable`, `prop:linear-interpolation`,
`cor:rkhs-readout`), F growth mechanisms, G the layerwise envelope, H variance profiles, I the
four regimes and balancing depths, J teacher--student/neural-operator/implementation examples
(`prop:implementation`, proof now in J.3), K deep ReLU networks, L chain-of-thought symbolic
computation, M unrolled iterative solvers and samplers. All Lean labels
(`thm:...`/`prop:...`/`lem:...`/`cond:...`) referenced in the table above are unchanged by this
reorganization; only their location within the appendix moved.

## Maintenance

When a library theorem's statement changes, update the corresponding challenge statement
(never the library to fit the challenge) and regenerate the proof line in `Solution.lean`; the
argument list is the challenge's explicit binders in order.
