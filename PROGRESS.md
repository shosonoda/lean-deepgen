# 進捗管理 (PROGRESS.md)

計画は [PLAN.md](PLAN.md)，現状の要約は [SUMMARY.md](SUMMARY.md)．
状態: `todo` / `wip` / `stated`（statement のみ，証明は `sorry`）/ `done`（sorry なし）/ `blocked`．

## ステップ一覧

| # | ステップ | モジュール | 状態 | 担当 | 備考 |
|---|---|---|---|---|---|
| 0 | 計画立案（原稿からの抽出，PLAN.md） | — | done | 親 | 2026-09-24 |
| 1 | 設定の定義 | `Setting/*` | done | サブエージェント (general-purpose) | 2026-09-24．55 ノード，sorry なし，blueprint web 生成確認済み |
| 1' | FoML との接続（Rademacher 定義の付け替え，`ToFoML/CoveringNumberBridge`） | `Setting/Rademacher`, `ToFoML/*` | done | サブエージェント | 2026-09-24．`empRademacher` は FoML の `empiricalRademacherComplexity_without_abs`；bridge 4 補題は証明済み |
| 2 | 基本補題（App. F.2） | `Growth/Lemmas`, `Setting/Covering` | done | サブエージェント | 2026-09-24．Lipschitz embedding（external/internal/packing），sub-multiplicativity，probes-packing すべて証明済み |
| 3 | 指数下界 E1, E1', E2 | `Growth/Exponential` | done | サブエージェント | 2026-09-24．E1, E1', E2（下界と語長ごとの単射性）すべて証明済み |
| 4 | プロファイル（lem:log-split, prop:profiles） | `Profiles/LogSplit`, `Profiles/Profiles` | done | サブエージェント | 2026-09-24．Γ(3/2) 積分を含め全て証明済み |
| 5 | 飽和 P1, P1'（Arzelà–Ascoli 自己写像版） | `Growth/ArzelaAscoli`, `Growth/Saturation` | done | サブエージェント | 2026-09-24．thm:caa（↔），thm:maa，lem:oaa，cor:aa-semigroup-saturation，P1（4 変種），P1' すべて証明済み |
| 6 | 多項式 P2 | `Growth/Polynomial` | done | サブエージェント | 2026-09-24．定数 `C_H max(1, R_S L_α)^D` を明示，直径評価も証明済み |
| 7 | 主定理の statement（thm:bv, thm:hidden-decomp, thm:sudakov-type 等） | `Bounds/*` | done | サブエージェント | 2026-09-24．全 9 件の statement 確定（可積分性・有界性の仮定を追加，SUMMARY 参照） |
| 8 | cor:sudakov-rates / cor:matching の証明 | `Bounds/Sudakov` | done | サブエージェント | 2026-09-24．thm:sudakov-type（sorry）から代入で証明済み |
| 9 | トレードオフ（EL/EP/PL/PP） | `Tradeoff/Regimes` | done | サブエージェント | 2026-09-24．PP は厳密等式＋下界，EP/EL/PL は `IsTheta`，順序注意も証明済み |
| 10 | output layer の十分条件（prop:hilbert-sg, prop:finite-lipschitz-sg） | `Bounds/HiddenOutput`, `ToFoML/VectorHoeffding` | done | サブエージェント | 2026-09-24．両方証明済み（Hilbert 空間版 Rademacher tail を Pinelis 型 majorization で証明） |
| 11 | 例（implementation, CoT, ODE, readout） | `Examples/{Regimes,Implementation,Readout,ChainOfThought,ODE}` | done | サブエージェント | 2026-09-24．prop:implementation (a)(b)(c)，readout 4 件，CoT，ODE すべて証明済み．informal だった prop:cot-append, prop:ode-fixedpoint, prop:ode-horizon も高確率評価＋明示深さの厳密版で証明（Euler 大域誤差 lem:ode-euler-error 含む） |
| 12 | 主定理の証明（確率論） | `Bounds/*`, `ToFoML/*`, `ToMathlib/*` | **done** | サブエージェント | 全主定理証明済み（thm:bv の定数は原稿どおり 4β_ℓ / 2β_ℓ）．thm:sudakov-type は Bernoulli–Sudakov minoration（ToMathlib/ToFoML で完全証明，`e2aafba`）から導出 |
| 13 | E3（記憶保存拡大） | `Growth/MemoryExpansion` | done | サブエージェント | 2026-09-24．(i)–(iii) 上下界，cor:superexp，cor:doubleexp すべて証明済み |

## Bernoulli–Sudakov（PLAN.md §7，青写真 `00note/sudakov-math.md`）

| 補題 | 内容 | モジュール | 状態 |
|---|---|---|---|
| G1 | Gaussian 積測度，座標の法則・独立性，線形汎関数の法則・MGF | `ToMathlib/GaussianPi` | done (`e7a6cae`) |
| G2 | Gaussian 裾（上界 Chernoff，下界 Mills 比），負部分の期待値 | `ToMathlib/GaussianTail` | done |
| G3 | iid Gaussian max の下界 `E max ≥ (1/6)√log M` | `ToMathlib/GaussianMaxLower` | done |
| G4 | Gaussian 部分積分（1 次元・座標・線形像版） | `ToMathlib/GaussianIntegrationByParts` | done (`0967c43`) |
| G5 | log-sum-exp（挟み込み，勾配，Hessian の 2 次形式 ≥ 0） | `ToMathlib/LogSumExp` | done |
| G6–G7 | 補間の微分公式，Sudakov–Fernique（行列形） | `ToMathlib/SudakovFernique` | done (`47fe148`) |
| G8 | Gaussian Sudakov minoration（`a√(log M)/(6√2)`） | `ToMathlib/GaussianSudakov` | done (`d664021`) |
| B2, B4, B8, B10 | 縮約（決定論的），log-sum-exp の max 上界，`b(u)` の不変性，計数補題 | `ToFoML/BernoulliSudakovTools` | done (`0078e03`) |
| B1, B3, B5, B6 | 符号対称化，打ち切り MGF（K = 16），裾部分（定数 16）・有界部分の max 評価 | `ToFoML/BernoulliSudakovTruncation` | done (`979ec2a`) |
| B7, B9 | 臨界ケース（`L₃ = 9216 + 12√2`），部分族選択（`L₂ = √2 L₃`） | `ToFoML/BernoulliSudakovCritical` | done (`30051f8`) |
| B11, B12 | 多重スケール反復（`L₀ = 8L₂`），`bernoulli_sudakov`（`c = 1/L₀ ≈ 9.6e−6`） | `ToFoML/BernoulliSudakovIteration`, `ToFoML/BernoulliSudakov` | done (`e2aafba`) |

## ノード別状態

（2026-09-24 時点: 893 ノード，**sorry 0**，主要定理の `#print axioms` は `propext, Classical.choice, Quot.sound` のみ）

| ラベル | Lean 名 | 状態 |
|---|---|---|
| def:word-ball, def:words, def:semigroup-closure | `wordBall`, `words`, `semigroupClosure` | done |
| lem:wordball-zero/succ/mono, lem:id-mem-wordball, lem:mem-wordball-succ, lem:subset-semigroup-closure, lem:wordball-subset-of-subset, lem:comp-mem-wordball-add, lem:wordball-succ-eq-union-words | `wordBall_*`, `id_mem_wordBall`, `comp_mem_wordBall_add` 等 | done |
| lem:words-encard-le, lem:wordball-encard-le, lem:wordball-card (`|B(k,F)| ≤ r^{k+1}`) | `encard_words_le`, `encard_wordBall_le`, `encard_wordBall_le_pow` | done |
| def:d-inf, def:d-inf-real, def:d-S, def:emp-norm, def:emp-sup-norm, def:diam-S, def:emp-space(+instance) | `uniformDist`, `uniformDistReal`, `empDist`, `empNorm`, `empSupNorm`, `empDiam`, `EmpSpace` | done |
| lem:empdist-self/comm/nonneg/triangle, lem:sqrt-sum-sq-add-le, lem:dist-emp-space | `empDist_*`, `sqrt_sum_sq_add_le` | done |
| lem:dS-le-dinf, lem:edist-le-uniformdist, lem:dist-le-uniformdist-toreal | `empDist_le_uniformDist` 等 | done |
| lem:right-comp-1lip, lem:left-comp-lip | `uniformDist_comp_right_le`, `uniformDist_comp_left_le` | done |
| def:metric-entropy, lem:packing-covering, lem:covering-le-external-two-mul, lem:exists-external-cover, lem:subadditivity | `metricEntropy`, `packing_covering`, `externalCoveringNumber_union_le` 等 | done |
| def:comp-class, def:hypothesis-class, def:err-imp, lem:comp-class-mono, lem:hypothesis-class-zero/mono | `compClass`, `hypothesisClass`, `implError` 等 | done |
| def:loss, def:emp-risk, def:risk, def:emp-minimizer, def:err-model | `BoundedLipschitzLoss`, `empRisk`, `risk`, `IsEmpMinimizer`, `modelError` | done |
| def:emp-rademacher, def:rademacher, lem:emp-rademacher-mono, lem:emp-rademacher-le-abs | `empRademacher`（FoML 経由）, `rademacherComplexity`, `empRademacher_mono`, `empRademacher_le_abs` | done |
| def:unif-maps(+instance), def:to-unif-maps, lem:edist-unif-maps 他 | `UnifMaps X := X →ᵤ X`（Mathlib の `UniformFun` の sup-edist を流用） | done |
| lem:foml-covering-le-external, lem:external-le-foml-covering, lem:totallyBounded-of-covering-finite | `ToFoML.coveringNumber_le_externalCoveringNumber` 等 | done |
| lem:lipschitz-embedding(-internal,-packing), lem:submultiplicativity, def:eval-probes, lem:probes-packing(-internal,-family) | `Growth/Lemmas` | done |
| def:word-of, lem:wordof-mem-words/wordball, lem:pow-le-covering-of-probes, cond:e1-free-iso, cond:e1p-theoremC, lem:e2-probe, cond:e2-pingpong | `wordOf`, `cond_e1_free_iso`, `cond_e1p_theoremC`, `cond_e2_pingpong` | done |
| lem:sqrt-add-le, lem:log-split-ineq, lem:log-split-integral, lem:gamma-three-halves, lem:sqrt-log-integrable | `Profiles/LogSplit` | done |
| def:entropy-integral, lem:metric-entropy-anti, lem:entropy-integral-* , prop:profiles-i/ii/iii/iv, prop:profiles-finite | `entropyIntegral`, `profile_saturation`, `profile_poly_bounded`, `profile_exp_bounded`, `profile_poly_linear`, `profile_finite` | done |
| def:sup-separable, lem:risk-lipschitz, lem:emp-risk-lipschitz, lem:impl-error-pointwise | `Bounds/BiasVariance` | done |
| thm:bv-general, thm:bv-general-gap | `bv_general`, `bv_general_gap` | done（Rademacher 定数は原稿どおり；偏差項は明示定数） |
| thm:bv, thm:bv-gap | `bv`, `bv_gap` | done（一般版に帰着） |
| def:output-process, ass:sg-increment-main, def:hilbert-readout-class | `outputProcess`, `SubGaussianIncrements`, `hilbertReadoutClass` | done |
| thm:hidden-decomp（可積分性仮定付き） | `hidden_decomp` | done |
| prop:hilbert-sg | `hilbert_sg` | done（A_H = 1） |
| thm:hidden-decomp-depth | `hidden_decomp_depth` | done（thm:hidden-decomp に帰着） |
| ass:readout-realization-main, thm:sudakov-type（有界性仮定付き）, cor:sudakov-type-bounded, lem:emp-rademacher-nonneg | `ReadoutRealization`, `sudakov_type`, `sudakov_type_of_bounded` | done（`bernoulli_sudakov` に帰着） |
| thm:bernoulli-sudakov | `ToFoML.bernoulli_sudakov` | done（`c = 1/(8√2 L₃)`） |
| lem:khintchine-lower, lem:bernoulli-sudakov-two, lem:sum-signs-pow-four-le 他 | `ToFoML/SudakovMinoration` | done |
| cor:sudakov-rates(-poly), cor:matching(-ii), lem:sudakov-rates-of-log-le, lem:first-branch-le | `sudakov_rates_exp`, `sudakov_rates_poly`, `matching_exp`, `matching_poly` | done（有界性仮定を継承） |
| thm:caa(+of-equicontinuous/of-totallyBounded), thm:maa, lem:oaa, lem:caa-closure-compact, cor:aa-semigroup-saturation(-internal) | `Growth/ArzelaAscoli` | done |
| cond:p1, cond:p1-2a/2b/2c, cond:p1-ucont, def:p1ucont-memory-length, lem:p1ucont-* | `Growth/Saturation` | done |
| cond:p2-nilp(-real,-compact), lem:p2-wordball-subset-ball, lem:p2-transfer, lem:p2-diameter | `Growth/Polynomial` | done |
| def:e3-*, cond:e3-i/ii/iii-upper/iii-lower, cond:e3, cor:superexp, cor:doubleexp | `Growth/MemoryExpansion` | done |
| def:bias-exp/poly, def:var-log/poly, def:gen-bound, def:k-pp/ep/el/pl, lem:balancing, thm:tradeoff-pp/ep/el/pl, rem:tradeoff-ordering | `Tradeoff/Regimes` | done |
| lem:bv-deterministic(-gap), lem:bv-uniform-deviation, lem:bv-loss-rademacher, lem:bv-emp-rademacher-reindex | `Bounds/BiasVariance` | done |
| lem:contraction(-without-abs), lem:rademacher-finite-approximation, lem:rademacher-abs-le-shift, lem:rademacher-singleton-abs, lem:sup-dense-separableSpace, lem:uniformfun-countably-generated | `ToFoML/{Contraction,AbsShift,UniformFunSeparable}` | done |
| def:var, lem:hidden-decomp-var, lem:covering-empSpace-le-unifMaps, lem:empDiam-*, cor:profile-p1(-totallyBounded,-nonexpanding), cor:profile-p2-compact/noncompact, cor:profile-finite, cor:var-profiles(-p1,-p2-*,-finite) | `Bounds/Variance` | done |
| def:comp-list, def:impl-word, lem:impl-word-error, prop:implementation-a/b/c, cor:implementation-b-nonexpanding/contractive, def:relu-layer, lem:affine-eq-relu, def:is-relu-net, lem:impl-error-id | `Examples/Implementation` | done |
| def:linear-readouts, def:reachable-sample-set, prop:global_scalar_observable, prop:linear-interpolation, cor:linear-interpolation-*, lem:gram-right-inverse, cor:rkhs-readout, cor:finite-dim-feature | `Examples/Readout` | done |
| def:cot-*, lem:cot-metric-prefix, lem:cot-compact, lem:cot-append-lipschitz/saturation/growth/profile, lem:cot-branch-pingpong/growth/profile, lem:cot-output, cor:cot-output-sg | `Examples/ChainOfThought` | done（cor:cot-output-sg は prop:hilbert-sg 経由） |
| def:fp-vector-field-class, lem:fp-contraction, lem:fp-saturation, lem:fp-entropy-explicit, lem:ode-scheme-lipschitz, def:ode-scheme-ball, lem:ode-saturation(-profile) | `Examples/ODE` | done |
| thm:dudley-subgaussian, lem:emax-of-tail, lem:layer-cake-finite, def:sg-increments-finite 他 | `ToFoML/DudleySubGaussian` | done |
| lem:rademacher-real-tail, lem:chernoff-finite, lem:union-bound-absorb, lem:rademacher-hilbert-tail-real | `ToFoML/VectorHoeffding` | done |
| lem:rademacher-hilbert-tail, lem:cosh-norm-add-sub-le, lem:convexOn-cosh-sqrt, lem:signs-cosh-norm-le, lem:chernoff-cosh-finite | `ToFoML.rademacher_hilbert_tail` 他 | done（Pinelis 型，定数 2 のまま） |
| prop:finite-lipschitz-sg, prop:hilbert-sg-of-tail, prop:hilbert-sg-real | `finite_lipschitz_sg`, `hilbert_sg_of_tail`, `hilbert_sg_real` | done |
| lem:ent-composition-covering, thm:rad.decomp.ent.ent-foml, thm:rad.decomp.ent.ent（可積分性仮定付き，スケール x/4） | `Bounds/EntropyDecomp` | done |
| def:unif-fun, def:unif-self, ass:ent-readout, ass:ent-transition | `UnifFun`, `UnifSelf`（`UnifMaps` と重複，要統合）, `EntReadout`, `EntTransition` | done |

## 作業ログ

- 2026-09-24: 原稿（`main-iclr2027.tex`, `06iclr2027/`）から定義・定理を抽出し PLAN.md を作成．
  付録の statement 抽出は Explore サブエージェントで実施．`lake build` が通ることを確認（Lean v4.32.0, Mathlib v4.32.0）．
  Mathlib に `coveringNumber` / `packingNumber`（`Topology/MetricSpace/CoveringNumbers`）があることを確認し，これを採用する方針とした．
- 2026-09-24: Step 1（設定の定義）をサブエージェントで形式化．`LeanDeepgen/Setting/{WordBall,Metrics,Covering,Hypothesis,Loss,Rademacher}.lean`（計 585 行，55 blueprint ノード，sorry なし）．
  `blueprint/src/content.tex` を原稿の章立てに合わせて書き換え，`./script/generate.sh --no-pdf` で web 版の生成と checkdecls を確認．
  設計上の決定: Rademacher 期待値は `Fin n → Bool` 上の平均（測度論不要）；`sup`/`inf` は `sSup`/`sInf` of image（`ℝ` の入れ子 `⨆` は空集合で 0 になる junk を避けるため）；
  subadditivity と packing–covering は `externalCoveringNumber` で述べる（Mathlib の内部被覆数は単調でない）．
  未コミット（コミットは指示があってから）．
- 2026-09-24: ユーザー指示により lean-rademacher（`FoML`，https://github.com/auto-res/lean-rademacher，rev `f509f2b`，Lean/Mathlib v4.32.0）を lake 依存に追加（`lakefile.toml`，`lake update FoML`，`lake build FoML` 成功）．
  FoML に無い一般的な道具は `LeanDeepgen/ToFoML/` に置く方針を PLAN.md に追記．
  FoML の `coveringNumber` は root 名前空間，Mathlib のものは `Metric.coveringNumber` なので衝突なし．
  Step 1'+7（FoML 接続と主定理 statement），Step 2+3（増大度補題と E1/E1'/E2），Step 4（プロファイル）を 3 つのサブエージェントで並行着手．
- 2026-09-24: 3 エージェント完了．Growth/Lemmas, Growth/Exponential, Profiles/LogSplit, Profiles/Profiles, ToFoML/CoveringNumberBridge, Bounds/{BiasVariance,HiddenOutput,Sudakov,EntropyDecomp} を追加し，ルート・content.tex に組み込み．
  `lake build` 成功（sorry は主定理 7 件のみ），`generate.sh --no-pdf` で blueprint web + checkdecls 通過．
  要統合: `UnifSelf`（EntropyDecomp）→ `UnifMaps`（Metrics），HiddenOutput の Dudley 積分 → `entropyIntegral`．
- 2026-09-24: 第 2 波（5 エージェント）完了．P1/P1'，P2，E3，トレードオフ，thm:bv-general 証明．`lake build` 成功，blueprint 310 ノード，残 sorry は thm:hidden-decomp, prop:hilbert-sg, prop:finite-lipschitz-sg, thm:sudakov-type, thm:rad.decomp.ent.ent の 5 件．
  thm:bv-general は FoML の両側一様偏差評価経由のため定数が原稿と異なる（原稿 4β R̂ + C b√(log(1/δ)/n) → Lean 8β R̂ + 10 b√(2 log(2/δ)/n)；gap は 2β → 4β，5b）．原稿の定数を回復するには片側 symmetrization が必要．
  追加仮定: `∀ x, ∃ M, ∀ f ∈ 𝓗, |f x| ≤ M`（各点有界；`⨆` の junk 回避）．
- 2026-09-24: 第 3 波着手: プロファイル表の接続（`Bounds/Variance`），実装・readout 例，CoT・ODE 例，sub-Gaussian Dudley（`ToFoML/DudleySubGaussian`）+ thm:hidden-decomp，prop:hilbert-sg / prop:finite-lipschitz-sg / thm:rad.decomp.ent.ent の証明．
- 2026-09-24: 第 3 波（5 エージェント）完了．Bounds/Variance（tab:profiles），Examples/{Implementation,Readout,ChainOfThought,ODE}，ToFoML/{DudleySubGaussian,VectorHoeffding}，prop:finite-lipschitz-sg，entropy 分解の FoML 形．
  並列作業の衝突 2 件を修正（`empDiam_le_diam_univ` の重複定義 → ODE 側を `'` 付きに改名；blueprint ラベル `lem:sqrt-add-le` の重複 → EntropyDecomp 側を `-ent` に）．
  発見: thm:hidden-decomp と thm:rad.decomp.ent.ent の Lean statement は Dudley 積分の可積分性を仮定しないと偽（Lean の Bochner 積分は非可積分で 0；反例あり）．第 4 波で可積分性仮定を追加．
- 2026-09-24: 第 4 波着手: statement 修正（可積分性），Hilbert 空間版 Rademacher tail（Pinelis），Bernoulli–Sudakov minoration の分離と thm:sudakov-type の導出．
- 2026-09-24: 第 4 波 (1) 完了: thm:hidden-decomp / thm:hidden-decomp-depth / cor:var-profiles に可積分性仮定を追加（tab:profiles の 4 系は既存仮定から可積分性を導出），thm:rad.decomp.ent.ent を可積分版に置換．残 sorry は `rademacher_hilbert_tail` と `sudakov_type` のみ．
- 2026-09-24: 第 4 波 (2) 完了: `rademacher_hilbert_tail`（Hilbert 空間の Rademacher 和の tail，指数の定数 2）を majorization + cosh√ の凸性で証明．prop:hilbert-sg は sorry なし．残 sorry は `sudakov_type` のみ．
- 2026-09-24: 第 4 波完了．thm:sudakov-type の Lean statement が sup の非有界性で偽であることが判明し，有界性仮定（`∀ σ, BddAbove …`）を追加して系にも伝播．Bernoulli–Sudakov minoration を `ToFoML/SudakovMinoration.bernoulli_sudakov` に分離（sorry；M = 2 の Khintchine 下界は証明済み）．
  テンプレートの `LeanDeepgen/Basic.lean` を削除．最終: `lake build` 成功，`generate.sh --no-pdf` 通過，blueprint 568 ノード，Lean 約 12,000 行，残 sorry 1 件．全て未コミット．
- 2026-09-24（第 2 セッション）: FoML を main に切替（`6eddab4`）．commit 開始．リファクタリング（`ToMathlib/` 6 ファイルに Mathlib 向け補題を分離，`UnifSelf` 統合，重複削除；`da9d61c`），片側 symmetrization で thm:bv の定数回復（`b5f6e55`），CoT/ODE の EL/PL 命題の厳密化と Euler 大域誤差（`41ff83c`），ToDraft.md と PLAN.md §5–7（緩和候補・残作業・Bernoulli–Sudakov 計画；`3b656ba`）．
  最終: `lake build` 成功，blueprint 643 ノード，Lean 約 14,400 行，残 sorry は `bernoulli_sudakov` 1 件．
- 2026-09-24（第 3 セッション）: ユーザー判断: Bernoulli–Sudakov は R1（教科書ルート，仮定化なし）で長期的に進める；PLAN §5 の W4–W28 を採用．
  `00note/sudakov-math.md`（ULB §6.4 + Sudakov–Fernique の青写真，定数 c = 1/L ≈ 2.6e−6）を作成．G1–G5，B2/B4/B8/B10 を証明済み（上表）．W5/W7/W11/W14/W15 を Lean に反映（`35d44fe`），W8 は保留（R7）．
- 2026-09-24（第 3 セッション，続き）: Bernoulli–Sudakov minoration を R1 ルートで完全形式化（G1–G8: `ToMathlib/{GaussianPi,GaussianTail,GaussianMaxLower,GaussianIntegrationByParts,LogSumExp,SudakovFernique,GaussianSudakov}`；B1–B12: `ToFoML/{BernoulliSudakovTools,BernoulliSudakovTruncation,BernoulliSudakovCritical,BernoulliSudakovIteration,BernoulliSudakov}`）．
  **プロジェクト全体で sorry 0**．`lake build` 成功，blueprint 893 ノード，Lean 約 19,000 行．主要 16 定理の `#print axioms` を確認（標準 3 公理のみ）．
- 2026-09-25: W8 実施（`Bounds/EntropyDecompSample`，`2e4ea0e`）．Comparator 導入（`../comparator-tools/` に comparator と lean4export v4.32.0 をビルド，`script/comparator.sh`，`comparator/{Challenge,Solution}.lean` の sanity 版で動作確認 約 50 秒）．リファクタリング（定義モジュール分離・名前空間統一・重複除去）をサブエージェントで実施中．
- 2026-09-25: リファクタリング完了（定義モジュール `Setting/Assumptions`, `Profiles/Defs`, `Tradeoff/Defs`, `Growth/Defs`；ToMathlib は `LeanDeepgen.ToMathlib`，ToFoML は `LeanDeepgen.ToFoML` に統一；重複 7 件削除；lint 0）．
  Comparator: `comparator/Challenge.lean`（定義モジュールのみ import，原稿の 55 定理を sorry 付きで列挙；ToDraft の修正・W4–W28 反映後の形）と `Solution.lean`（ライブラリで証明）で `./script/comparator.sh` → 「Your solution is okay!」（`47f5cf3`）．
  lean-rademacher: `ToMathlib`（13）+ `ToFoML`（13）を `FoML/ToMathlib`, `FoML/ToFoML` として `ss` ブランチに移植（`@[blueprint]` はコメントアウト，変換スクリプト `scripts/import-lean-deepgen-extras.py`），`lake build` 成功，PR #11 を作成 → ユーザー指示により，変換スクリプト（private リポジトリ参照）を除いたブランチ `ss-pr` から PR #12 に差し替え（#11 は close；docstring の private ノート参照も公開リポジトリ参照に修正）．
- 2026-09-25: lean-rademacher PR #12 マージ後，FoML を `db9f187` に更新し `LeanDeepgen/ToMathlib`・`ToFoML` を撤去（`FoML.ToMathlib`/`FoML.ToFoML` を参照，`e5224bd`；ビルド・blueprint・Comparator 通過）．公開リポジトリへ publish．
- 2026-09-25: 公開．`publish-code.sh` で https://github.com/shosonoda/lean-deepgen （main，`6cc52ab`）へ，`publish-page.sh` で blueprint サイト（web + PDF）を gh-pages へ．公開側の Pages 環境に `gh-pages` からのデプロイを許可．PDF 版のために blueprint 文中のコード内 `_` をエスケープ，原稿マクロ（`\gen`,`\bias`,`\var`,`\kopt`）と cleveref を preamble に追加．CI は `requirements.txt` を追加，`blueprint.yml` は docgen-action（pip 非互換で失敗）を外し web 版のみデプロイ（ユーザー了承）．
- 2026-09-25: 公開版 blueprint の表示崩れ（本文がモジュール名の生表示，依存グラフ空）を修正．原因は公開側に TeX が無く plasTeX の代替探索が `macros/common` や抽出 `.tex` のサブディレクトリ付きパスを解決できないこと．`ci.yml`・`blueprint.yml` に `texlive-binaries`（`kpsewhich`）を導入（`c702b15`）．公開サイトで本文・依存グラフ（569 ノード，ローカルと同一）・PDF を確認．
