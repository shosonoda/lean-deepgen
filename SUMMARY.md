# 形式化の現状 (SUMMARY.md)

更新日: 2026-09-25（第 9 回：FoML.ToMathlib/ToFoML へ移行，公開）

## 概要

- 対象: "Why and When Deep is Better than Shallow: Implementation-Agnostic State-Transition Model of Deep Learning"（ICLR 2027 投稿原稿）．
- 環境: Lean v4.32.0，Mathlib v4.32.0，LeanArchitect v4.32.0，FoML（lean-rademacher `main`）．`lake build` と `./script/generate.sh --no-pdf`（blueprint web + checkdecls）が通る．
- 規模: Lean 約 12,200 行（一般的道具 約 8,400 行は lean-rademacher へ移管），blueprint 575 ノード．**`sorry` は 0**．主要定理（thm:bv-general, thm:bv, thm:hidden-decomp(-depth), thm:sudakov-type, cor:matching, thm:rad.decomp.ent.ent, prop:hilbert-sg, prop:finite-lipschitz-sg, P1', P2, E2, cor:doubleexp, prop:profiles, tradeoff_PL, bernoulli_sudakov）の `#print axioms` は `propext, Classical.choice, Quot.sound` のみ．
- 計画: [PLAN.md](PLAN.md)．進捗: [PROGRESS.md](PROGRESS.md)．原稿への修正: [ToDraft.md](ToDraft.md)．
- 検証: [comparator/](comparator/)（Challenge 55 定理 / Solution）を `./script/comparator.sh` で検査済み（statement 一致・公理 3 つのみ・kernel 受理）．
- 上流: `ToMathlib`/`ToFoML` は lean-rademacher に統合済み（PR #12 マージ，FoML rev `db9f187`）．本プロジェクトは `FoML.ToMathlib`/`FoML.ToFoML` を依存として参照し，ローカルコピーは撤去．
- 公開: https://github.com/shosonoda/lean-deepgen（Lean 一式），blueprint（web + PDF）: https://shosonoda.github.io/lean-deepgen/ ．公開側 CI（`ci.yml`）と Pages（`blueprint.yml`，web 版のみ；`pages.yml`，ローカル生成物）で検証・デプロイ．

## 形式化済みの対象

| 区分 | 定義 | statement のみ | 証明済み |
|---|---|---|---|
| 設定（Sec. 2） | 13 / 13（+ 補助定義 7） | — | 基本補題 35 / 35 |
| 主定理（Sec. 3） | 仮定 3 / 3 | 9 / 9 | **9 / 9 完全証明** |
| 増大度（Sec. 4, App. F） | — | 14 / 14 | 14 / 14（基本補題，E1, E1', E2, P1, P1', P2, E3, cor:superexp, cor:doubleexp, Arzelà–Ascoli 系） |
| プロファイル・トレードオフ（Sec. 4.2, 5） | — | 4 / 4 | 4 / 4（lem:log-split，prop:profiles (i)–(iv)，tab:tradeoff の 4 regime を `IsTheta` で） |
| 例・応用（App.） | — | 17 / 17 | 17 / 17（prop:cot-append, prop:ode-fixedpoint, prop:ode-horizon は高確率評価＋明示深さの厳密版；lem:ode-euler-error も証明済み） |

## Mathlib との対応

| 原稿の概念 | Lean / Mathlib |
|---|---|
| covering number `N(A,ρ,ε)` | `coveringNumber ε A : ℕ∞`（内部被覆，閉球，`ε : ℝ≥0`）; 外部中心が必要な場面は `externalCoveringNumber` |
| packing number `M(A,ρ,ε)` | `packingNumber ε A` |
| packing–covering 双対 | `packingNumber_two_mul_le_externalCoveringNumber`, `coveringNumber_le_packingNumber` |
| Arzelà–Ascoli | `BoundedContinuousFunction.arzela_ascoli`, `ArzelaAscoli.isCompact_of_equicontinuous` |
| sub-Gaussian | `ProbabilityTheory.Kernel.HasSubgaussianMGF` |
| word ball `B(k,F)` | `LeanDeepgen.wordBall F k : Set (X → X)`（再帰 `B(k+1) = B(k) ∪ F ∘ B(k)`），`words F m`（長さちょうど m），`semigroupClosure F` |
| `d_∞`, `d_S`, `diam_S` | `uniformDist : ℝ≥0∞`（`⨆ x, edist`），`empDist S`（`Fin n → X` 上），`empDiam S`；`EmpSpace S` に `PseudoMetricSpace` インスタンス |
| `ℋ_k = H ∘ B(k,F)`, `ε_imp`, `ε_model` | `hypothesisClass H F k`, `implError ι 𝓗 : ℝ≥0∞`, `modelError L P 𝓗 𝒞` |
| 損失・リスク・η-経験最小化元 | `BoundedLipschitzLoss Y`（`ℓ, b, β` と 3 公理），`empRisk`, `risk`, `IsEmpMinimizer` |
| Rademacher 複雑度 | `empRademacher S G`（`Fin n → Bool` 上の平均，`sSup` of image），`rademacherComplexity P n G`（`Measure.pi` で積分） |
| Dudley の entropy integral | FoML `dudley_entropy_integral'`（`R̂ ≤ 4ε + (12/√n) ∫_ε^{c/2} √log N`，FoML 独自の開球 covering number）；Mathlib 版との橋渡しは `ToFoML/CoveringNumberBridge` |
| 一様偏差の高確率評価，ERM の oracle 不等式 | FoML `uniform_deviation_tail_bound_separable_*`，`IsApproxERM.excessRisk_le` |
| 縮約不等式（任意 index），abs/片側 Rademacher の比較，sup-norm 稠密 ⇒ 可分 | `ToFoML/Contraction`，`ToFoML/AbsShift`，`ToMathlib/UniformFunSeparable`（証明済み） |
| 片側 symmetrization・McDiarmid・観測標本版の一様偏差評価 | `ToFoML/OneSidedDeviation`（証明済み；thm:bv の定数回復に使用） |
| Mathlib 向け補題（被覆数の Lipschitz 埋め込み・和・有限性，Γ(3/2) 積分，cosh 不等式，UniformFun の可分性・第一可算性，layer cake） | `ToMathlib/{CoveringNumber,SqrtLogIntegral,CoshInequalities,UniformFunSeparable,IntervalIntegral,Misc}` |
| sub-Gaussian 過程の Dudley（有限確率空間，定数 12） | `ToFoML/DudleySubGaussian.dudley_subgaussian_finite_space`（証明済み） |
| 標本版 entropy 分解（W8） | `Bounds/EntropyDecompSample.rad_decomp_ent_ent_sample`（証明済み；sup-norm 版はその系） |
| Rademacher 和の Hoeffding tail（実数値） | `ToFoML/VectorHoeffding.rademacher_real_tail`（証明済み）；Hilbert 空間版 `rademacher_hilbert_tail`（定数 2，Pinelis 型 majorization）も証明済み |
| Bernoulli–Sudakov minoration（Talagrand ULB Thm 6.4.1） | `ToFoML/BernoulliSudakov.bernoulli_sudakov`（証明済み，`c = 1/(8√2 L₃)`，`L₃ = 9216 + 12√2`）；部品: `ToFoML/BernoulliSudakov{Tools,Truncation,Critical,Iteration}` |
| Gaussian 側（Mathlib 向け）: 積測度・裾・iid max 下界・部分積分（Stein）・log-sum-exp・Sudakov–Fernique・Gaussian Sudakov | `ToMathlib/{GaussianPi,GaussianTail,GaussianMaxLower,GaussianIntegrationByParts,LogSumExp,SudakovFernique,GaussianSudakov}`（証明済み） |
| tab:profiles（機構 → プロファイル → R̂ の評価） | `Bounds/Variance`（`varTerm`, `var_profile_p1/p2_bounded/p2_linear/finite`） |
| Dudley 積分 `V_k(S)`，4 プロファイル | `entropyIntegral D A`，`profile_saturation` 等（`Profiles/Profiles`） |
| 語 `f_{i_k} ∘ ⋯ ∘ f_{i_1}`，E1/E1'/E2 | `wordOf f u`（`List (Fin r)`），`cond_e1_free_iso`，`cond_e1p_theoremC`，`cond_e2_pingpong`（`Growth/Exponential`） |

## 原稿と Lean の主な差異

- **thm:bv-general / thm:bv の定数**: Rademacher 項は原稿どおり `4β_ℓ R̂_S(𝓗)`（gap は `2β_ℓ`）．偏差項は明示定数 `6 b √(2 log(4/δ)/n)`（gap は `3b√…`；原稿の `C b√(log(1/δ)/n)` の `C` を具体化したもの．`log(4/δ)` は ±ℓ 各 2 事象の union bound 由来）．
- **追加仮定**: thm:bv 系に「各点で有界: `∀ x, ∃ M, ∀ f ∈ 𝓗, |f x| ≤ M`」（`⨆` の junk 値回避），`0 < b`，`0 ≤ β_ℓ`，損失の可測性．
- **P2**: 球のエントロピー仮定は `ENNReal.ofReal` 形（有限性を含む）で述べる．`k ≥ 1` は不要．
- **P1'**: `0 < c` を仮定，`A` のコンパクト性と `k ≥ m(ε)` は未使用（全ての k で成立）．
- **E3 系**: `ε < λ δ₀ / 2`，`ε < 1/2`，`N(δ, G) ≠ ⊤` を仮定（PLAN.md §1.6）．
- **thm:sudakov-type**: 各符号パターンで `ℋ_k` 上の Rademacher 平均が上に有界という仮定を追加（sup が非有界だと Lean の `iSup` は 0 になり statement が偽）．有界クラス版 `cor:sudakov-type-bounded` も用意．
- **thm:hidden-decomp / thm:rad.decomp.ent.ent**: Dudley 積分の可積分性を仮定に追加（Lean の Bochner 積分は非可積分関数で 0 になるため，仮定なしでは偽）．entropy 分解は FoML の Dudley（内部・開球被覆）経由のためスケールが `x/4, x/(4L_H)`，積分区間 `[0, B_H/2]` に変わる．
- **tab:profiles**: 内部被覆数の非単調性のため `N(A, d_S, ε) ≤ N^ext(A, d_∞, ε/2)` を経由し，P2 の定数に `2^D` が付く．
- **例**: ODE の射影 `Π_K` は Mathlib に無いので `IsProjectionOnto K proj`（像が K，K 上恒等，1-Lipschitz）を仮定．勾配ステップの縮小は強単調性と co-coercivity を仮定に置く（強凹＋smooth から従う）．
- **トレードオフ**: Lambert W は Mathlib に無いので PL の深さは `(2βn / log(2βn))^{1/(2β)}` で直接定義し，`k^{2β} log k / n → 1` を証明．

## 未解決・注意点

- 主定理の statement での逸脱（LaTeX 文中にも明記）: 確率評価の定数は FoML 由来の `3 b √(2 log(2/δ)/n)` を明示；Sudakov の universal constant は `∃ c > 0, ∀ (𝒳 : Type u) …` の形；`ℙ_σ` は `Signs n` 上の計数比；`log M` は `M = ∞` で 0（不等式を弱めるだけ）．
- Step 1 の設計判断: `ℝ` 上の `⨆ g ∈ G` は空集合で 0 になるため `sSup (f '' G)` を使用（利用側で `BddAbove` と `Nonempty` を仮定に入れる）．
  `metricEntropy` は `coveringNumber = ⊤` のとき `Real.log 0 = 0` になる junk 値を持つ（有限性の仮定を各定理に置く）．

- `d_∞` は `ℝ≥0∞` 値（`UnifMaps X := X →ᵤ X` の sup-edist）で扱い，非コンパクト域でも問題ない．
- 今後の候補: (1) `ToFoML/`（+ `ToMathlib/`）の lean-rademacher `ss` ブランチへの反映（blueprint 注釈をコメントアウト；ユーザー指示待ち），(3) 原稿への反映（ToDraft.md；ユーザー指示待ち），(4) 公開リポジトリへの publish，(5) Comparator による公理検査，(6) Sudakov の定数改善（`c ≈ 9.6e−6` は証明の便宜上の値）．
- 原稿の細かな仮定の不足（PLAN.md §1.6）は Lean 側で仮定を追加して対処する．
