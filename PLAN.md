# 形式化計画 (PLAN.md)

作成日: 2026-09-24
対象原稿: `../draft-metric-deep/main-iclr2027.tex` + `06iclr2027/`
（"Why and When Deep is Better than Shallow: Implementation-Agnostic State-Transition Model of Deep Learning"）

進捗は [PROGRESS.md](PROGRESS.md)，形式化の現状は [SUMMARY.md](SUMMARY.md) を参照．

## 0. 方針

- **LeanArchitect 流**: 各定義・定理に `@[blueprint "label"]` を付け，statement は原稿の LaTeX を写す．
  依存関係 (`\uses`) は自動推論に任せ，必要なときだけ `uses :=` / `proofUses :=` で補う．
  `sorry` 付きで statement を先に固め (`notReady := true` は使わず，sorry の有無で `\leanok` を制御)，
  証明は後から埋める．
- **ラベルは原稿の `\label` をそのまま使う**（例 `thm:bv`, `cond:p1`）．blueprint の章立ては原稿の章立てに合わせる
  (`blueprint/src/content.tex` で `\inputleannode` を並べる)．
- **Mathlib を最大限使う**:
  - covering / packing number: `Mathlib.Topology.MetricSpace.CoveringNumbers`
    (`coveringNumber`, `externalCoveringNumber`, `packingNumber` : `ℝ≥0 → Set X → ℕ∞`，閉球，
    `packingNumber_two_mul_le_externalCoveringNumber`, `coveringNumber_le_packingNumber` 等が既存)．
  - Arzelà–Ascoli: `BoundedContinuousFunction.arzela_ascoli` (`α →ᵇ β`) および `ArzelaAscoli.*` (`Topology/UniformSpace/Ascoli`)．
  - sub-Gaussian: `ProbabilityTheory.Kernel.HasSubgaussianMGF`（Rademacher 和の集中に使う）．
  - FoML（lean-rademacher）: `Signs n`，`empiricalRademacherComplexity(_without_abs) n F S`（`F : ι → 𝒳 → ℝ`，index 付き，`⨆ i`），
    `rademacherComplexity n F μ X`，`uniformDeviation`，`dudley_entropy_integral'`（`R̂ ≤ 4ε + (12/√n) ∫_ε^{c/2} √(log N(x)) dx`，
    FoML 独自の `coveringNumber (ha : TotallyBounded A) (ε : ℝ) : ℕ`，開球），`uniform_deviation_tail_bound_separable_*`，
    `IsApproxERM.excessRisk_le`，`empiricalRademacherComplexity_contraction_finite`（有限クラスのみ）．
  - Lambert W, Γ(3/2) など：Mathlib に無いものは補題化して `sorry` 段階を明示．
- **lean-rademacher (`FoML`) を利用する**（https://github.com/auto-res/lean-rademacher，local: `../lean-rademacher`，
  lake 依存 `FoML` として rev `f509f2b` に固定）．Rademacher 複雑度・Dudley 積分・一様偏差の高確率評価・ERM の oracle 不等式・
  有限クラスの縮約不等式はここから取る．本プロジェクトと独立性の高い「機械学習理論の一般的な道具」で FoML に無かったもの
  （`ToFoML`）と Mathlib にあるべきだが無いもの（`ToMathlib`）は lean-rademacher へ移した（`FoML.ToMathlib`，`FoML.ToFoML`，
  PR #12；本プロジェクトは依存としてそれらを使う）．新しい一般的な道具は，ローカルの `LeanDeepgen/ToFoML` または `ToMathlib`
  スクラッチモジュールで開発し（`LeanDeepgen` の他モジュールに依存させない），同じ方法で upstream する．
- **サブエージェントで形式化**: 各ステップは独立モジュール単位で `general-purpose` サブエージェントに委譲する
  （プロンプトには対象 statement の LaTeX，使う Mathlib 名，命名規約，「`lake build` が通ること」を含める）．
  親エージェントは PLAN/PROGRESS/SUMMARY の更新とレビューのみを行い，トークンを節約する．
- 形式化の粒度は「原稿の主張を Lean の命題として正確に述べ，証明は可能な範囲で埋める」．
  確率論を要する部分（Rademacher 複雑度，Dudley，Sudakov）は statement を先に固め，証明は後回しにする．

## 1. 原稿から抽出した主要対象

### 1.1 定義（Sec. 2, App. 増大度）

| ラベル案 | 名称 | 内容 |
|---|---|---|
| `def:state-space` | 状態空間 | 距離空間 `(𝒳, d)`；hidden layer は連続自己写像 `f : C(𝒳,𝒳)` |
| `def:hidden-class` | hidden-layer class | `F ⊆ C(𝒳,𝒳)` |
| `def:word-ball` | 深さ k hidden class `B(k,F)` | `{f_m ∘ ⋯ ∘ f_1 : 0 ≤ m ≤ k, f_i ∈ F}`，`B(0,F)={id}`，単調増加．半群 `⟨F⟩ = ⋃_k B(k,F)` の word ball |
| `def:output-class` | output-layer class | `H ⊆ C(𝒳, ℝ)` |
| `def:hypothesis-class` | 深さ k 仮説クラス | `ℋ_k = H ∘ B(k,F)` |
| `def:target-class` / `def:impl-class` | 目標クラス `𝒞`，実装クラス `ℋ_imp`，実装写像 `ι : ℋ_k → ℋ_imp` | |
| `def:loss` | 損失 | `ℓ : ℝ × 𝒴 → [0,b]`，第 1 引数で `β_ℓ`-Lipschitz |
| `def:risk` | リスク | `L[f] = 𝔼 ℓ(f(X),Y)`，`L̂[f] = n⁻¹ Σ ℓ(f(X_i),Y_i)`，η-経験最小化元 |
| `def:err-imp`, `def:err-model` | 実装誤差・近似項 | `ε_imp(k) = sup_{f∈ℋ_k} ‖f − ι f‖_∞`，`ε_model(k) = inf_{ℋ_k} L − inf_{𝒞} L` |
| `def:d-S`, `def:d-inf` | 経験距離・一様距離 | `d_S(f,g) = (n⁻¹ Σ d(f X_i, g X_i)²)^{1/2}`，`d_∞(f,g) = sup_x d(f x, g x)`；`‖u‖_S`, `‖u‖_{S,∞}` |
| `def:covering` | covering / packing number，metric entropy | Mathlib の `coveringNumber` / `packingNumber` を使用．`diam_S(F)` |
| `def:rademacher` | 経験 / 期待 Rademacher 複雑度 | `R̂_S(G) = 𝔼_σ sup_{g∈G} n⁻¹ Σ σ_i g(X_i)`，`R_n(G) = 𝔼_S R̂_S(G)` |
| `def:entropy-integral` | `V_k(S) = ∫_0^{D_k(S)} √(log N(B(k,F), d_S, ε)) dε`，`D_k(S) = diam_S B(k,F)`，`var(k,n) = 12 A_H L V_k(S)/√n` | Sec. 4 |

### 1.2 主定理（Sec. 3）

| ラベル | 種別 | 内容 | 難度 |
|---|---|---|---|
| `thm:bv` | 定理 | 実装非依存 bias–variance 分解 (`thm:bv-general` の特殊化)：確率 `1−δ` で `L[ĥ] − inf_𝒞 L ≤ β_ℓ ε_imp + ε_model + η + 4β_ℓ R̂_S(ℋ_k) + C b √(log(1/δ)/n)` と gap 版 | hard（確率） |
| `thm:bv-general` | 定理 (App. B) | 一般版：擬距離 `d_T`，定数 `β_L, β_L̂` | hard |
| `ass:sg-increment-main` | 仮定 | sub-Gaussian output-layer 増分：`ℙ_σ(|Z_f − Z_g| > t) ≤ 2 exp(−n t² / (2 A_H² L² d_S(f,g)²))` | — |
| `thm:hidden-decomp` (= `thm:mixed-sg`) | 定理 | `R̂_S(H∘F) ≤ R̂_S(H) + (12 A_H L/√n) ∫_0^{diam_S F} √(log N(F,d_S,ε)) dε`（Dudley） | hard |
| `prop:hilbert-sg` | 命題 | Hilbert 特徴写像の線形 output layer は `A_H = 1` で仮定を満たす | medium |
| `prop:finite-lipschitz-sg` | 命題 | 有限 Lipschitz output layer は `A_H = (1 + log m / log 2)^{1/2}` で満たす | medium |
| `ass:readout-realization-main` | 仮定 | output-layer による hidden geometry の実現（κ-co-Lipschitz，`R_out` 有界） | — |
| `thm:sudakov-type` (= `thm:sudakov`) | 定理 | 条件付き Sudakov 型下界 `R̂_S(ℋ_k) ≥ c sup_ε min{κ ε √(log M(B_k,d_S,2ε)/n), κ²ε²/R_out}` | hard |
| `cor:sudakov-rates` / `cor:matching` | 系 | fixed-scale packing 下界 `e^{αk}` / `k^β` から `√(k/n)`, `√(log k/n)` の下界 | easy（代入） |
| `thm:rad.decomp.ent.ent` | 定理 (App. D) | 決定論的エントロピー分解（`ass:ent-readout`, `ass:ent-transition`） | hard |

### 1.3 増大度条件（Sec. 4, App. F）

基本補題（App. F.2）:

| ラベル案 | 内容 | 難度 |
|---|---|---|
| `lem:packing-covering` | `M(A,2ε) ≤ N(A,ε) ≤ M(A,ε)` | easy（Mathlib 既存） |
| `lem:lipschitz-embedding` | `φ` が `L`-Lipschitz なら `N(φ(S), Lε) ≤ N(S, ε)`，packing も同様 | easy |
| `lem:subadditivity` | `N(F ∪ G, ε) ≤ N(F,ε) + N(G,ε)` | easy |
| `lem:submultiplicativity` | 左右 Lipschitz 半群で `N(FG, ε+δ) ≤ N(F, ε/ρ) N(G, δ/λ)` | easy–medium |
| `lem:right-comp-1lip` / `lem:left-comp-lip` | `d_∞(a∘f, b∘f) ≤ d_∞(a,b)`，`d_∞(f∘a, f∘b) ≤ lip(f) d_∞(a,b)` | easy |
| `lem:probes-packing` | 有限プローブ `P` での評価写像は 1-Lipschitz；像が `δ`-分離な `M` 点を含めば `ε < δ/2` で `N(S,d_∞,ε) ≥ M` | easy |

条件（namedcondition）:

| ラベル | 名称 | 結論 | 難度 |
|---|---|---|---|
| `cond:p1` | P1: コンパクト等連続半群は飽和 | `𝒳` コンパクト，`⟨F⟩` が precompact / 等連続 / 一様 Lipschitz / 非拡大のいずれか ⇒ `N(B(k,F),ε) ≤ N(Ḡ,ε) < ∞` | medium（Arzelà–Ascoli） |
| `cond:p1-ucont` | P1': コンパクト不変集合への縮小 | 一様縮小 `c<1`，コンパクト不変集合 `A`，有界吸収集合 `K` ⇒ `k ≥ m(ε)` で `N(B(k,F),d_∞,ε) ≤ N(A,ε/2) + Σ_{ℓ<m(ε)} N(F^ℓ,ε)` | medium |
| `cond:p2-nilp` | P2: 冪零制御は多項式増大 | 群 `H` の球のエントロピーが `C_H(1+R/δ)^D`，作用が `L_α`-Lipschitz，`F ⊆ α(S)` ⇒ `N(B(k,F),d_∞,ε) ≤ C(1+k/ε)^D` | medium |
| `cond:e1-free-iso` | E1: 自由半群 + 一点一様分離 | 語長ごとの単射性と基点 `x_*` での `δ`-分離 ⇒ `ε < δ/2` で `N ≥ r^k` | easy |
| `cond:e1p-theoremC` | E1': 等長 + 同長コーディング | E1 の等長版 | easy |
| `cond:e2-pingpong` | E2: ping–pong コーディング | 分離チャンバー，コーディングコア，リセット，マーカー分離 ⇒ `ε < α/2` で `N ≥ r^k`，語長ごとの単射性 | medium |
| `cond:e3` | E3: 記憶保存拡大は超指数 / 二重指数 | `log N(B(2k+1,F),ε) ≳ k²` または `≳ λ^{pk}` | hard（構成） |
| `cor:superexp`, `cor:doubleexp` | 系 | E3 の二つの regime | hard |
| `thm:caa`, `thm:maa`, `lem:oaa`, `thm:pmaa`, `cor:aa-semigroup-saturation` | App. コンパクト Arzelà–Ascoli | 自己写像版 AA と半群飽和 | medium（Mathlib AA を流用） |
| `thm:guivarch-bass`, `cor:nilpotent-entropy`, `thm:breuillard-large-balls` | App. 冪零 Lie 群 | 引用定理（axiom 扱いも検討） | hard（Lean 化は対象外候補） |

### 1.4 プロファイルとトレードオフ（Sec. 4.2, Sec. 5）

| ラベル | 内容 | 難度 |
|---|---|---|
| `lem:log-split` | `log(1+k/ε) ≤ log(1+k/D̄) + log(D̄/ε)`，`∫_0^{D̄} √(log(D̄/ε)) dε = D̄ Γ(3/2) = (√π/2) D̄` | medium（積分は Γ 関数） |
| `prop:profiles` (i)–(iv) | 飽和 / 多項式+有界径 / 指数+有界径 / 多項式+線形径 の 4 プロファイル `V_k(S) ≤ …` | medium（(i),(iii) easy；(ii),(iv) は lem:log-split） |
| `prop:profiles-finite` | `|F| = r` ⇒ `|B(k,F)| ≤ r^{k+1}` ⇒ `N_k(ε) ≤ r^{k+1}` | easy |
| `tab:tradeoff` (EL/EP/PL/PP) | バランス深さ `k*` と平衡誤差（App. J）：EP `k* = (log n − γ log log n + O(1))/(2α)`，EL，PL（Lambert W），PP `k* ≍ n^{1/(2β+γ)}` | medium（漸近；PP は厳密に述べやすい） |

### 1.5 例・応用（App. G–O）

| ラベル | 内容 | 難度 |
|---|---|---|
| `prop:implementation` (= `prop:implementation-restated`) | (a) コンパクト `K` 上で稠密族 `𝒜` から有限実装クラス（サイズ `N(ℋ_k, ε/2)`）を作り `ε_imp ≤ ε`；(b) 層ごとの誤差 `δ, δ_H` と Lipschitz 定数 `Λ, L_H` から `ε_imp(k) ≤ δ_H + L_H δ Σ_{i<k} Λ^i`；(c) `ℝ^d` のアフィン遷移は幅 `2d` の ReLU 層で厳密実現，`ε_imp = 0` | (b) easy（望遠和の帰納法，最初の目標），(a) easy–medium，(c) easy（恒等式）/ medium（ReLU ネットの型を定義する場合） |
| `lem:cot-output` | `𝒜^ℕ` 上の窓 one-hot 特徴 `Φ_L` は `√2 θ^{1−L}`-Lipschitz，`Φ_∞` は `√(2/(1−θ²))`-Lipschitz ⇒ `prop:hilbert-sg` で `A_H = 1` | medium |
| `lem:cot-append-growth` | 追記のみのステップ `F_w = {x ↦ (a,x)}` は `N(B(k,F_w), d_∞, ε) ≤ m^{min{k,ℓ(ε)}+1}`，`V_k ≤ V_∞`（飽和） | medium |
| `prop:cot-append` | 追記型 scratchpad は EL regime，`k* = log n / (2 log(1/θ)) + O(1)` | hard（主定理に依存，`≲` の非形式的 statement） |
| `lem:cot-branch-growth` | 分岐型 `F_b`（subshift ping–pong）は `r^k ≤ N(B(k,F_b), d_∞, ε) ≤ r^{k+1}`，`V_k ≤ √((k+1) log r)` | easy–medium |
| `lem:fp-contraction` | 強凹 `μ`，`Λ_s`-smooth な勾配ステップ `Π_K(x + h s(x))` は `(1 − hμ)`-Lipschitz ⇒ P1 | medium |
| `prop:ode-fixedpoint` | 不動点反復は EL regime | hard（thm:bv に依存） |
| `lem:ode-saturation` | Euler スキーム族は `e^{Λ_s T}`-Lipschitz ⇒ 等連続・全有界 ⇒ 飽和 | medium |
| `prop:ode-horizon` | 固定ホライズン積分は PL regime（Euler の大域誤差 `C_E T² k^{−p}`） | hard |
| `prop:global_scalar_observable` | 大域スカラー観測 `u` が `U_{k,S}` 上で `κ`-co-Lipschitz なら `Ψ_k(f) = h_u ∘ f` が `ass:readout-realization` を満たす | easy |
| `prop:linear-interpolation` | 写像ごとの有限集合補間（右逆 `R_{A_j}`，`‖R‖ ≤ Λ_j`）で符号 `u^{(j)}` を実現 | easy–medium |
| `cor:finite-dim-feature` / `cor:rkhs-readout` | 有限次元特徴写像（`σ_min`），RKHS（Gram 行列 `λ_min`）版 | medium（Mathlib に RKHS 無し，内積空間 + Gram 行列で抽象化） |
| `thm:caa`, `thm:maa`, `lem:oaa`, `thm:pmaa`, `cor:aa-semigroup-saturation` | 自己写像版 Arzelà–Ascoli：コンパクト `X` で `H ⊆ C(X,X)` が `d_∞` 全有界 ⇔ 等連続；共通モジュラス判定；擬距離商 | medium（Mathlib `arzela_ascoli` に glue） |
| `cond:e3`, `cor:superexp`, `cor:doubleexp` | `X = ℓ_∞(E)`，`F = {r, A} ∪ {g_u : u ∈ G}` の記憶保存拡大．`W_k = {w_u}` は定数写像，`d_∞(w_u,w_v) = max_j min{1, λ^{k−j+1}‖u_j − v_j‖}`，`∏_j M(G, 2ε/λ^{k−j+1}) ≤ N(W_k, ε) ≤ ∏_j N(G, ε/λ^{k−j+1})` ⇒ `log N ≳ k²`（有限次元）/ `≳ λ^{pk}`（`δ^{−p}` エントロピー） | medium（積の被覆・パッキング） |
| `thm:guivarch-bass`, `cor:nilpotent-entropy`, `thm:breuillard-large-balls` | 引用定理 | 形式化対象外（P2 の仮定として置く） |

### 1.6 抽出時に見つかった原稿側の注意点（形式化で明示すべき仮定）

- `cond:p1-ucont` (P1'): 右辺の有限性には各 `N(F^ℓ, ε) < ∞` が必要（原稿は仮定していない）．
  結論は実際には全ての `k` で成立．`c = 0` の `log_{1/c}` は Lean では別扱い．
  被覆の中心が定数写像（外部中心）になるので `externalCoveringNumber` を使う．
- `cond:e1-free-iso` (E1): 仮定 (1) 語長ごとの単射性は (2) 一様分離から従う（冗長）．
- `cond:e1p-theoremC` (E1'): `r = |F|` が未定義（`F` 有限，`r ≥ 2` を仮定に加える）．
- `cond:e2-pingpong` (E2): 証明は `Δ > 0`（チャンバーの互いに素性）しか使わない．
- `cond:e3` 系: 「十分小さい `ε`」は実際には `ε < λ δ_0 / 2` が必要（`j = k` の項の半径 `ε/λ` が `k` に依存しない）．
  `N(W_k) ≤ N(B(2k+1,F))` は部分集合単調性を暗黙に使う（Mathlib の内部被覆数は単調でない．外部被覆数か `coveringNumber_subset_le` を使う）．
- `lem:cot-branch-growth`: `|B(k)| ≤ Σ_{j≤k} r^j ≤ r^{k+1}` は `r ≥ 2` が必要．
- `prop:implementation` (b): `Σ_{i<m} Λ^i ≤ Σ_{i<k} Λ^i` は `Λ ≥ 0` を使う（Lipschitz 定数なので OK）．
- `cor:aa-semigroup-saturation`: `B(0,F) = {id}` なので `id ∈ ⟨F⟩`（モノイド）を前提にする．

## 2. モジュール構成（Lean）（2026-09-25 リファクタリング後の実態）

```
（lean-rademacher 側，依存として使用: `FoML.ToMathlib`（Mathlib にあるべき補題）と `FoML.ToFoML`（FoML に無かった一般的な道具）．
  旧 `LeanDeepgen/ToMathlib`, `LeanDeepgen/ToFoML` は lean-rademacher へ移した（PR #12）；新しい一般的な道具はローカルの
  `LeanDeepgen/ToFoML` または `ToMathlib` スクラッチモジュールで開発し，同じ方法で upstream する）
LeanDeepgen/
  Setting/                   -- 定義（Challenge が import するのはこの層 + Profiles/Defs, Tradeoff/Defs, Growth/Defs）
    WordBall, Metrics, Covering, Hypothesis, Loss, Rademacher, Assumptions
  Profiles/   Defs, LogSplit, Profiles
  Tradeoff/   Defs, Regimes
  Growth/     Defs, Lemmas, Exponential, ArzelaAscoli, Saturation, Polynomial, MemoryExpansion
  Bounds/     BiasVariance, HiddenOutput, Sudakov, EntropyDecomp, EntropyDecompSample, Variance
  Examples/   Regimes, Implementation, Readout, ChainOfThought, ODE
comparator/   Challenge.lean（原稿の定理を sorry 付きで列挙），Solution.lean（ライブラリで証明），config.json
```

## 3. ステップ（依存順）

各ステップの成果物は「`lake build` が通る Lean ファイル + `@[blueprint]` annotation + `content.tex` の更新」．
`[S]` は statement のみ（証明 `sorry` 可），`[P]` は証明まで．

| # | ステップ | 対象 | 種別 | 依存 |
|---|---|---|---|---|
| 1 | 設定の定義 | `Setting/WordBall`, `Metrics`, `Covering`, `Hypothesis`, `Loss`, `Rademacher` | [P]（定義なので sorry なし） | — |
| 1' | FoML との接続 | `Setting/Rademacher` を FoML 定義で書き直し，`ToFoML/CoveringNumberBridge` | [P] | 1 |
| 2 | 基本補題 | App. F.2 の 6 補題 + `|B(k,F)| ≤ r^{k+1}` + `d_S ≤ d_∞` ⇒ covering 単調 | [P] | 1 |
| 3 | 指数下界 E1, E1', E2 | `Growth/E1`, `E2PingPong` | [P]（probes-packing から） | 2 |
| 4 | プロファイル | `lem:log-split`, `prop:profiles` (i)–(iv) | [P]（積分部分は sorry 許容） | 1 |
| 5 | 飽和 P1, P1' | Arzelà–Ascoli 自己写像版，`cond:p1`, `cond:p1-ucont` | [S] → [P] | 2 |
| 6 | 多項式 P2 | `cond:p2-nilp`（群の仮定は hypothesis として与える） | [P] | 2 |
| 7 | 主定理の statement | `thm:bv-general`, `thm:bv`, `ass:sg-increment`, `thm:hidden-decomp`, `ass:readout-realization`, `thm:sudakov-type`, `cor:sudakov-rates`, `cor:matching` | [S] | 1 |
| 8 | 系 (matching) の証明 | `cor:sudakov-rates`, `cor:matching`（thm:sudakov-type を仮定して代入） | [P] | 7 |
| 9 | トレードオフ | PP regime の厳密版，EP/EL/PL は漸近 statement | [S] → [P] | 4 |
| 10 | output layer の十分条件 | `prop:hilbert-sg`, `prop:finite-lipschitz-sg` | [S] → [P] | 7 |
| 11 | 例 | CoT，ODE，implementation，readout | [S] → [P] | 3, 5 |
| 12 | 主定理の証明 | `thm:bv`（FoML の一様偏差評価 + ERM oracle 不等式 + 縮約；無限クラスの縮約は `ToFoML/Contraction`），`thm:hidden-decomp`（FoML の Dudley を anchored process に適用），`thm:sudakov-type`（Sudakov minoration は `ToFoML`），`thm:rad.decomp.ent.ent` | [P]（長期） | 7 |
| 13 | E3 | `cond:e3`, `cor:superexp`, `cor:doubleexp` | [S] → [P]（長期） | 3 |

優先順位: 1 → 2 → 3 → 4 → 7 → 8 → 5 → 6 → 9 → 10 → 11 → 12 → 13．
ステップ 12（確率論の本体）は Mathlib 側の整備状況に依存するため最後に回す．

## 4. 形式化上の設計判断

- **covering number の型**: Mathlib の `coveringNumber ε A : ℕ∞`（`ε : ℝ≥0`，閉球，内部被覆）を採用．
  原稿の `N(A,ρ,ε)` は擬距離 `ρ` を陽に持つが，Lean では `d_∞` / `d_S` ごとに
  `PseudoMetricSpace` 構造（`d_S` は擬距離，`d_∞` は非コンパクト域で `∞` を取り得るため
  `EMetric` または有界距離 `d_b = min{1,d}` 版）を型として与える．
  metric entropy は `Real.log (coveringNumber ε A).toReal`（`⊤` の場合は別扱い）．
- **`d_∞` の有限性**: 原稿どおり，`d_∞` を使う命題では「`⟨F⟩` 上で有限」または「有界距離に置換」を仮定に入れる．
  最初は `𝒳` を `BoundedSpace` / `CompactSpace` として扱い，非コンパクト版は後回し．
- **Rademacher 複雑度**: FoML の定義に接続する．集合 `G : Set (X → ℝ)` に対し
  `empRademacher S G := empiricalRademacherComplexity_without_abs n (fun g : G => (g : X → ℝ)) S`
  （原稿の `\erad_S` は絶対値なしの sup）．FoML の高確率評価は絶対値付き版なので `without_abs ≤ abs` で橋渡しする．
  covering number は Mathlib 版（`ℕ∞`，閉球）を主とし，Dudley を使う箇所で FoML 版（`ℕ`，開球）へ `ToFoML/CoveringNumberBridge` で変換する
  （閉球 `ε` 被覆 ⊆ 開球 `2ε` 被覆，など）．
- **半群 `⟨F⟩`**: `Submonoid.closure` を `Function.End 𝒳`（合成をモノイド構造とする）上で使うか，`B(k,F)` を再帰的に定義するか．
  `B(k,F)` を `Set (𝒳 → 𝒳)` として `Nat.rec` で定義し（`B(k+1,F) = B(k,F) ∪ F ∘ B(k,F)`），
  `⟨F⟩ = ⋃ k, B(k,F)` とする方が補題が書きやすい（採用）．連続性は必要な補題でだけ仮定する．
- **定数 `C`, `c`（universal constant）**: `∃ C > 0, ∀ …` の形で述べる．
- **`≍`, `O(·)`（Sec. 5）**: `Asymptotics.IsBigO` / `IsTheta` と `Filter.atTop` で述べる．
- **引用定理**（Guivarc'h–Bass，Breuillard）: 形式化対象外とし，P2 では「球のエントロピー上界」を仮定に置く（原稿もそうしている）．

## 5. 原稿より緩められる仮定・強められる結論（**W4–W28 採用**（2026-09-24 ユーザー判断）；W1–W3 は現状維持）

Lean の証明が実際に使った仮定・与えた結論から抽出．「現状」は Lean の現在の statement（原稿準拠），「候補」は変更案．
採用分のうち Lean の statement 変更を要するもの: W5, W7, W11, W14, W15（実施済み，`35d44fe`）．W8 も実施済み（`2e4ea0e`）：標本到達集合上の Lipschitz 性と押し出し標本上の被覆数（`pushedCoveringNumber`）で述べ，`F` のスケールは `x/(8L_H)`．その他は既に Lean がその形なので原稿側の記述変更のみ（ToDraft.md §「採用した緩和・強化」）．

### 5.1 主定理

| # | 対象 | 現状 | 候補（緩和 / 強化） | 影響 |
|---|---|---|---|---|
| W1 | `thm:bv-general` gap | η-経験最小化元について | **全ての `f ∈ ℋ` について**成立（既に Lean はこの形；原稿を強化） | なし |
| W2 | `thm:bv-general` 可分性 | sup-norm で可算稠密部分集合 | 各点評価が連続な位相での可分性（積位相）でも FoML の枠組みは動くが，一様偏差の可測性のために第一可算性が必要 → sup-norm 版が実質最弱．**現状維持推奨** | — |
| W3 | `thm:bv-general` 損失 | `ℓ : ℝ × 𝒴 → [0,b]` 有界 | 有界性は McDiarmid に必須．Lipschitz 性は「予測値方向」だけでよい（現状どおり） | — |
| W4 | `thm:hidden-decomp` | Rademacher 過程 `Z_f` に限定 | `ToFoML.dudley_subgaussian_finite_space` は **任意の有限確率空間上の sub-Gaussian 過程**で成立（定数 12，anchor 任意）．原稿の定理を「一般の sub-Gaussian 増分過程」として述べ，Rademacher は系にできる | 記述のみ |
| W5 | `thm:hidden-decomp` | `id ∈ F` を仮定 | anchor は `F` の任意の点 `f₀` でよく，その場合右辺は `R̂_S(H ∘ f₀)`（`= E Z_{f₀}`）．`id ∈ F` は `B(k,F)` では自動 | 記述のみ |
| W6 | `prop:hilbert-sg` | Hilbert 空間 | **任意の実内積空間**（完備性不要）．tail 定数 2 は最良 | 記述のみ |
| W7 | `thm:sudakov-type` | `B_k = B(k,F)` | **任意の部分集合 `B ⊆ C(X,X)`** で成立（word ball の構造は不使用）．また有界クラス版 `cor:sudakov-type-bounded`（`∀ g ∈ ℋ_k, ∀ i, |g(X_i)| ≤ C`）を用意済み | 記述のみ |
| W8 | `thm:rad.decomp.ent.ent` | `H` の一様 Lipschitz 性 `L_H` | 合成被覆補題は `L_H` を通じてしか使わないので，`H` の各元が **標本上で** `L_H`-Lipschitz なら十分（`d_S` 版） | 中（Lean 変更要） |

### 5.2 増大度条件

| # | 対象 | 現状 | 候補 | 影響 |
|---|---|---|---|---|
| W9 | `thm:caa` | `X` コンパクト | 逆向き（全有界 ⇒ 等連続）は **コンパクト性不要**（連続性のみ）．順向きは `thm:maa` により **`X` 全有界（擬距離）で十分** | 記述のみ（Lean は既にこの形） |
| W10 | `cond:p1` (1) | `X` コンパクト | (1)（`⟨F⟩` precompact）のみなら **コンパクト性不要** | 記述のみ |
| W11 | `cond:p1-ucont` (P1') | `k ≥ m(ε)`，`A` コンパクト，`K` コンパクト | **全ての `k`**，`A` は非空・不変のみ，`K` は有界のみ | 記述のみ |
| W12 | `cond:p2-nilp` (P2) | `k ≥ 1` | **`k ≥ 0`**．加えて直径評価 `D_k(S) ≤ 2 L_α R_S k` を結論に含める（`tab:profiles` で使用） | 記述のみ |
| W13 | `cond:e1-free-iso` (E1) | 自由性 (1) + 一様分離 (2) | **(2) のみ** | 記述のみ |
| W14 | `cond:e1p-theoremC` (E1') | 等長 + `d_∞` 有限 + 自由 + 同長分離 | **同長分離のみ**（E1 に帰着）．等長性は「`d_∞` が有限で被覆数が意味を持つ」ための注意にすぎない | 記述のみ |
| W15 | `cond:e2-pingpong` (E2) | `dist(U_i,U_j) ≥ Δ` | **チャンバーが互いに素**で十分（`Δ` の値は不使用）；`V_i ≠ ∅` は (2) から従う | 記述のみ |
| W16 | `cond:e3` 系 | `G` コンパクト | **`G` は任意**（上界は `N(δ,G)`，下界は `M(δ,G)` の仮定のみ）．`cor:superexp/doubleexp` は `N(δ,G) < ∞` と `ε < λδ₀/2, ε < 1/2` を明示 | 記述のみ |
| W17 | `cond:e3` (iii) 上界 | `λ > 1`, `ε < 1/2` | 上界は **`λ ≠ 0`，任意の `ε`** で成立 | 記述のみ |

### 5.3 プロファイル・トレードオフ

| # | 対象 | 現状 | 候補 | 影響 |
|---|---|---|---|---|
| W18 | `prop:profiles` (iii) | `ψ ≥ 0`（暗黙） | **`ψ`, `α` の符号条件不要**（`√(a+b) ≤ √a + √b` は全実数で成立） | 記述のみ |
| W19 | `prop:profiles` (i) | `D̄ > 0` | **`D̄ ≥ 0`** | 記述のみ |
| W20 | `prop:profiles`「有限 `F`」 | 距離空間 | **距離構造不要**（`|B(k,F)| ≤ r^{k+1}` と `N ≤ |·|` のみ） | 記述のみ |
| W21 | `tab:tradeoff` | `≍`（発見的） | EL/EP/PL は **両側 `Θ`，定数明示**；PP は **厳密等式＋全 `k` に対する下界**（因子 2 で最適） | 記述のみ |
| W22 | balancing principle | 説明のみ | 補題化: `bias` 単調減少・`var` 単調増加・`bias(k₀) = var(k₀)` ⇒ `∀k, gen(k) ≥ bias(k₀)`, `gen(k₀) = 2 bias(k₀)` | 記述のみ |

### 5.4 例

| # | 対象 | 現状 | 候補 | 影響 |
|---|---|---|---|---|
| W23 | `prop:implementation` (a) | `K` コンパクト，`𝒜` が `C(K)` で稠密 | **`X` 任意**，`ℋ_k` が sup-norm 全有界，`𝒜` が `ℋ_k` 上で稠密なら十分 | 記述のみ |
| W24 | `prop:implementation` (b) | `f̃`, `h̃` 連続 | **連続性不要**（既に原稿に注記あり） | — |
| W25 | `lem:cot-append-growth` | `ε ∈ (0,1]` | **全ての `ε > 0`** | 記述のみ |
| W26 | `lem:ode-saturation` | 時刻整合スキーム `B_T(k)` | **時刻整合を外した上位クラス**でも `e^{Λ_s T}`-Lipschitz ⇒ 飽和 | 記述のみ |
| W27 | `prop:linear-interpolation` | `z_{j,i}` 相異なる | **不要**（右逆写像の仮定に含まれる） | 記述のみ |
| W28 | `lem:cot-output` (`Φ_∞`) | 重み付き無限 one-hot | 窓版 `Φ_L`（`‖Φ_L‖ = 1`, `√2 θ^{1−L}`-Lipschitz）で十分；`Φ_∞` 版は未形式化 | — |

### 5.5 逆に「強める必要がある」仮定（既に Lean で追加済み；ToDraft.md 参照）

可積分性（D5, D6），sup の有界性（D1, D7），E3 の `ε < λδ₀/2`（D17），P1' の `N(F^ℓ,ε) < ∞`（D12），`r ≥ 2`（D26）．

## 6. 残作業の計画（2026-09-24 第 2 セッション）

| # | 作業 | 規模 | 状態 |
|---|---|---|---|
| R1 | リファクタリング: Mathlib 向け補題を `LeanDeepgen/ToMathlib/` へ分離（名前は維持），`UnifSelf` → `UnifMaps` 統合，ODE の重複補題削除，lint 修正 | 中 | 進行中 |
| R2 | informal 命題の厳密化: `prop:cot-append`, `prop:ode-fixedpoint`（EL），`prop:ode-horizon`（PL，Euler 大域誤差 `lem:ode-euler-error` を含む） | 中〜大 | 進行中 |
| R3 | 片側 symmetrization（`ToFoML/OneSidedDeviation`）で `thm:bv` の定数を原稿の `4β_ℓ` / `2β_ℓ` に回復 | 中 | 進行中 |
| R4 | `bernoulli_sudakov` の形式化（§7） | 大 | **done** |
| R5 | `ToFoML/`+`ToMathlib/` を lean-rademacher の `ss` ブランチへ反映（blueprint 注釈はコメントアウト） | 小〜中 | **done**（ブランチ `ss`；PR は `ss-pr`（`ss` からスクリプトを除いたもの）→ `main`: https://github.com/auto-res/lean-rademacher/pull/12） |
| R6 | 公開リポジトリへの `publish-code.sh` / `publish-page.sh` | 小 | ユーザー指示待ち |
| R7 | W8: `thm:rad.decomp.ent.ent` の経験距離版 | 中 | **done**（`2e4ea0e`，`Bounds/EntropyDecompSample`） |
| R8 | Comparator（challenge/solution）の整備 | 中 | **done**（`47f5cf3`，55 定理，「Your solution is okay!」） |
| R9 | リファクタリング（定義モジュール分離，名前空間統一，重複除去） | 中 | **done**（`0fab33a`, `61565e2`, `458672d`） |

## 7. Bernoulli–Sudakov minoration（`thm:bernoulli-sudakov`）の形式化計画（未着手；採否はユーザー判断）

対象: `ToFoML/SudakovMinoration.lean` の `bernoulli_sudakov`（唯一の `sorry`）．使用箇所は `Bounds/Sudakov.lean` の `sudakov_type` のみ．
系 `cor:sudakov-rates` / `cor:matching` は `min{κε√(log M/n), κ²ε²/R}` の両枝と普遍定数 `c` をそのまま必要とする．

### 7.0 環境調査（Mathlib v4.32.0 / FoML）
- **ある**: `gaussianReal`（積率・MGF），`stdGaussian`，`multivariateGaussian`（共分散 API），`IsGaussianProcess`，Fernique，`HasSubgaussianMGF`（和・Azuma–Hoeffding），1 次元部分積分，積分下の微分（`hasFDerivAt_integral_of_dominated_loc_of_lip`）．
- **ない**: Slepian / Sudakov–Fernique / Gordon，多変量 Gaussian の部分積分（Stein 恒等式），Gaussian 集中，log-Sobolev，Mills 比下界，Khintchine，Paley–Zygmund．
- **FoML**: `Signs n` 上の計数平均，有限クラス縮約，Massart，maximal inequality．Gaussian 過程は無し．
- **本プロジェクト**: Khintchine 下界・4 次モーメント（`SudakovMinoration`），`VectorHoeffding`（Hoeffding 裾），`DudleySubGaussian`（裾 → max 期待値）．

### 7.1 R1: 教科書ルート（Gaussian Sudakov + Bernoulli–Gaussian 比較；Ledoux–Talagrand Thm 4.15 / Talagrand 2014 §5.3）

| # | 補題 | 行数目安 | 難度 | 置き場 |
|---|---|---|---|---|
| G1 | `Measure.pi (fun _ ↦ gaussianReal 0 1)` 上の独立性・可積分性 | 200 | 低 | ToMathlib |
| G2 | Mills 比下界 `P(g>t) ≥ t/(1+t²)·φ(t)` | 150 | 低 | ToMathlib |
| G3 | iid `N(0,1)` M 個の `E max ≥ c√log M` | 250 | 中 | ToMathlib |
| G4 | Gaussian 部分積分 `E[g_i F(g)] = E[∂_i F(g)]` | 400 | 中 | ToMathlib |
| G5 | Sudakov–Fernique（補間 `√θX+√(1−θ)Y`，soft-max の Hessian，積分下の微分） | 1000–1200 | 高 | ToMathlib |
| G6 | `max ≤ LSE_β ≤ max + log M/β` | 100 | 低 | ToMathlib |
| G7 | Gaussian Sudakov `E max_j⟨u_j,g⟩ ≥ c a√log M` | 200 | 中 | ToMathlib |
| B1 | 積空間 `Signs n × (Fin n → ℝ)` と `law(σ_i|g_i|) = law(g_i)` | 300 | 中 | ToFoML |
| B2 | 制限補題（Jensen）`E sup Σ_{i∈J} ε_i t_i ≤ E sup Σ_i ε_i t_i` | 100 | 低 | ToFoML |
| B3 | ℓ∞ 下の比較（Talagrand）`E_g sup ≤ L(E_ε sup + b log M)` 型 | 800–1200 | **高** | ToFoML |
| B4 | 部分族選択で `a√log M` 枝と `a²/b` 枝を交換 | 200 | 低 | ToFoML |
| B5 | 正規化・定数整理 | 150 | 低 | ToFoML |

合計 **3500–5000 行，45–60 補題**．リスク: (i) B3 の正確な形（素朴な打ち切り + 縮約は `√(2 log n)` の損失で n 依存になる；原典の転記で形を確定させる必要），(ii) G5 の解析的帳簿，(iii) FoML の有限和と Mathlib 測度の往復（B1）．

### 7.2 R2: 初等的直接ルート（部分成果として有用，代替としては不採用）
- 帰着補題（200 行）: 部分族選択により「`R√log M ≤ ρ√n/L` の領域で `E ≥ cρ√(log M/n)`」と同値．
- Rademacher 下側裾（500–700 行）: `P(Σσ_i a_i ≥ λ) ≥ c exp(−Cλ²/‖a‖₂²)`（`λ ≤ ‖a‖₂²/(C‖a‖_∞)`），指数傾斜 + Chebyshev．
- 第二モーメント（Chung–Erdős，150 行）．
- 到達範囲: 完全な形が出るのは `u_j` の台が互いに素（独立）な場合のみ．一般の分離族では第二モーメント法は破綻（Gaussian でも Slepian か集中が必要）．特殊ケース版では系が追加仮定付きになり論文の主張の弱化．

### 7.3 R3: 仮定化
`bernoulli_sudakov` を `Prop` 値の仮定（`def BernoulliSudakov : Prop := ∃ c > 0, ∀ …`）に切り出し，`sudakov_type` 以下 7 定理に明示引数で渡す．
長所: `sorry` フリー，`#print axioms` で可視化，blueprint に「Talagrand 1993 に依拠」と明記，将来 R1 で証明したら引数を埋めるだけ．短所: 7 定理の signature 変更；論文の定理が形式上は条件付き．

### 7.4 決定（2026-09-24 ユーザー判断）: **R1 教科書ルートを長期プランとして進める**．仮定化（R3）は行わない（`#print axioms` は `propext, Classical.choice, Quot.sound` のみであること；後に Comparator で検査）．参考文献は `00data/`（git 管理外）．

フェーズ:
| Phase | 内容 | 置き場 | 状態 |
|---|---|---|---|
| P0 | 数学的青写真の抽出（正確な statement・定数・証明の分解）→ `00note/sudakov-math.md` | note | done |
| P1 | G1–G3: Gaussian 積測度，裾（Mills 比），iid max の下界 | ToMathlib | done |
| P2 | G4, G6: Gaussian 部分積分（Stein 恒等式），log-sum-exp | ToMathlib | done |
| P3 | G5, G7: Sudakov–Fernique 補間，Gaussian Sudakov minoration | ToMathlib | done |
| P4 | B1–B6, B8, B10: 対称化・打ち切り・縮約・計数 | ToFoML | done |
| P5 | B7, B9, B11, B12: 臨界ケース・部分族選択・多重スケール反復・組立 | ToFoML | **done（sorry 0，`e2aafba`）** |

### 7.5 旧・推奨（参考）
1. **即時**: R3 + R2 の帰着補題・Rademacher 下側裾・独立ケースを実装し，`sorry` を Gaussian 由来の核心のみに縮める（中規模，1 エージェント）．
2. **中期（R1-lite）**: Gaussian Sudakov（G7）を Mathlib 向け statement で公理化し，B1–B5 を証明．B3 の原典確認を先行．
3. **長期**: G1–G7 を `ToMathlib/` で証明し upstream．
