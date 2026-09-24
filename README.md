# Generalization error bounds for deep models

自動形式化プロジェクト用のテンプレートです。**開発用の private リポジトリ**（このリポジトリ）で Lean project と blueprint を開発し、
スクリプトで**公開用の public リポジトリ**に Lean project 一式と blueprint（GitHub Pages）を公開します。

- Blueprint は [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) の `@[blueprint]` annotation から生成します
  （LaTeX を別途手書きする必要はありません）。
- Web / PDF 版のレンダリングは [leanblueprint](https://github.com/PatrickMassot/leanblueprint) を使います。

```
開発用 (private)                               公開用 (public)
┌──────────────────────────┐   publish-code.sh    ┌──────────────────────┐
│ Lean project + blueprint │ ───────────────────▶ │ main      (Lean 一式) │
│                          │                      │                      │
│ generate.sh → site/      │ ───────────────────▶ │ gh-pages  (静的サイト) │──▶ GitHub Pages
└──────────────────────────┘   publish-page.sh    └──────────────────────┘
```

## 必要なツール

| ツール | 用途 | インストール |
| --- | --- | --- |
| [elan](https://github.com/leanprover/elan) (`lean`, `lake`) | Lean のビルド | `curl https://elan.lean-lang.org/elan-init.sh -sSf \| sh` |
| Python 3 + `leanblueprint` | blueprint のレンダリング | `pip install leanblueprint` (依存: `graphviz`, `pygraphviz`) |
| TeX Live (`latexmk`, `xelatex`) | PDF 版（任意） | `--no-pdf` で省略可 |
| [GitHub CLI](https://cli.github.com/) (`gh`) | 公開リポジトリの作成・Pages 設定 | `brew install gh && gh auth login` |

## セットアップ

1. このテンプレートから **private** リポジトリを作成し、clone します。
2. プロジェクト名・Lean バージョン・公開リポジトリをまとめて設定します。

```sh
./script/init.sh --name LeanDeepgen --lean v4.34.0 --public-repo <owner>/<public-repo> \
  --title "My formalization project" --author "Your Name"
```

`init.sh` は次を一括で書き換え、`lake update` と `lake exe cache get` まで実行します。

| 設定 | 反映先 |
| --- | --- |
| `--name` | `lakefile.toml`（package 名・lib 名）、ルートモジュール `LeanDeepgen.lean` / `LeanDeepgen/`、`blueprint/src/*.tex`、`README.md`、`home_page/index.html` |
| `--lean` | `lean-toolchain`、`lakefile.toml` の Mathlib と LeanArchitect の `rev`（同名タグに固定） |
| `--public-repo` | `publish.env` の `PUBLIC_REPO`、`blueprint/src/web.tex` の `\home` `\github` `\dochome`、home page のリンク |
| `--title` / `--author` | `\title` `\author`、home page、README の見出し |

何度でも再実行できます（名前の変更、バージョンの変更）。`--help` で全オプションを表示します。

## 開発

### Lean と blueprint annotation

`@[blueprint]` を付けた宣言が blueprint のノードになります（例: [`LeanDeepgen/Basic.lean`](LeanDeepgen/Basic.lean)）。

```lean
import Mathlib
import Architect

@[blueprint "thm:my-theorem"
  (statement := /-- For every natural number $n$, ... -/)]
theorem my_theorem (n : ℕ) : ... := by
  /-- Proof sketch shown in the blueprint. -/
  sorry
```

- 依存関係（`\uses`）は statement / proof で使われている定数から自動で推論されます。`sorry` の有無から `\leanok` も自動で付きます。
- `blueprint/src/content.tex` で章立てを書き、`\inputleanmodule{LeanDeepgen.Basic}`（モジュール全体）または
  `\inputleannode{thm:my-theorem}`（個別ノード）で取り込みます。
- オプションの一覧（`uses :=`, `proofUses :=`, `title :=`, `latexEnv :=` など）は
  [LeanArchitect の README](https://github.com/hanwenzhu/LeanArchitect#specifying-the-blueprint) を参照してください。

### ローカルで blueprint を生成・確認

```sh
./script/generate.sh            # ビルド → 抽出 → web / pdf → site/ を組み立て
./script/generate.sh --serve    # 生成後に http://localhost:8000/ で確認
./script/generate.sh --no-pdf   # TeX 環境が無い場合
```

内部では `lake build`, `lake build :blueprint`, `leanblueprint web`, `leanblueprint pdf`, `lake exe checkdecls` を順に実行します。
成果物は `blueprint/web/`, `blueprint/print/print.pdf`, `site/`（home page + blueprint + PDF）です。いずれも git 管理外です。

## Comparator による検証

[Comparator](https://github.com/leanprover/comparator) で「原稿の定理（`comparator/Challenge.lean`，`sorry` 付き statement）が
ライブラリで証明されている（`comparator/Solution.lean`）こと」と「使用公理が `propext`, `Quot.sound`, `Classical.choice` のみであること」を検査します．

```sh
# 一度だけ: ツールを ../comparator-tools/ に用意（comparator 本体と，本プロジェクトの Lean 版の lean4export）
mkdir -p ../comparator-tools && cd ../comparator-tools
git clone https://github.com/leanprover/comparator.git && (cd comparator && lake build comparator)
git clone --branch v4.32.0 https://github.com/leanprover/lean4export.git lean4export-v4.32.0 && (cd lean4export-v4.32.0 && lake build)
cd -
./script/comparator.sh        # 約 1 分．Linux では landrun があれば自動で使う（macOS は fake-landrun）
```

`comparator/config.json` の `theorem_names` が検査対象です．Challenge の import 閉包（本ライブラリの定義モジュール）は信頼済みとみなします．

## 公開

公開リポジトリは `publish.env` の `PUBLIC_REPO`（または環境変数 `PUBLIC_REPO`）で指定します。
**未指定の場合、`publish-*.sh` はエラーで停止します。**

### Lean project の公開

```sh
./script/publish-code.sh --create   # 公開リポジトリが無ければ作成
./script/publish-code.sh            # 2 回目以降
./script/publish-code.sh --dry-run  # 変更内容の確認のみ
```

- コミット済みの `HEAD` のスナップショットを公開リポジトリの `main` に 1 コミットとして積みます。
  開発リポジトリの履歴は公開されません。
- [`.publishignore`](.publishignore) に列挙したパス（`00note/`, `publish.env`, 公開用スクリプトなど）は除外されます。
- 作業ツリーに未コミットの変更があると停止します（`--allow-dirty` で続行）。

### Blueprint (GitHub Pages) の公開

```sh
./script/generate.sh
./script/publish-page.sh            # site/ を gh-pages ブランチへ push
```

- `site/` の内容を公開リポジトリの `gh-pages` ブランチに push します。同ブランチ上の
  [`pages.yml`](.github/workflows/pages.yml) workflow が GitHub Pages にデプロイします（Lean のビルドは不要なので数十秒で反映されます）。
- 公開リポジトリの Pages 設定（Source: GitHub Actions）は初回に自動で有効化します。
- 公開先 URL は `https://<owner>.github.io/<public-repo>/` です。

## GitHub Actions

| workflow | 実行場所 | 内容 |
| --- | --- | --- |
| [`ci.yml`](.github/workflows/ci.yml) | 両方 | `lake build :blueprint` と `leanblueprint web`, `checkdecls` による検証。デプロイはしません。 |
| [`blueprint.yml`](.github/workflows/blueprint.yml) | 公開のみ（`main` への push） | Lean のビルド、blueprint（web 版）を生成し GitHub Pages にデプロイ（PDF・API ドキュメントは含まない）。 |
| [`pages.yml`](.github/workflows/pages.yml) | 公開のみ（`gh-pages` への push） | `publish-page.sh` が push した静的サイトをそのままデプロイ。 |
| `create-release.yml`, `update.yml` | 両方 | Lean テンプレート標準の release tag 付与と Mathlib 更新（手動）。 |

### ビルド時間の短縮（キャッシュ）

- `leanprover/lean-action` が `.lake`（プロジェクトと Mathlib の olean）を GitHub Actions cache に保存します。
  キーは `lean-toolchain` と `lake-manifest.json` のハッシュなので、依存を変えない限り 2 回目以降は差分ビルドで済みます。
  Mathlib 本体は `lake exe cache get` で取得します。
- ローカルで生成した blueprint を `publish-page.sh` で公開する経路では GitHub 側のビルドが不要です。

`blueprint.yml` は `main` への push で web 版 blueprint をデプロイし、`publish-page.sh` は
ローカル生成物（PDF 付き）を即座にデプロイします。両方を実行した場合は後に完了した方が公開されます。

## ファイル構成

```
.
├── LeanDeepgen.lean, LeanDeepgen/   Lean ソース（@[blueprint] annotation）
├── blueprint/src/                               leanblueprint のソース（content.tex, web.tex, print.tex, ...）
├── home_page/index.html                         GitHub Pages のトップページ（静的 HTML）
├── script/
│   ├── init.sh            プロジェクト名・Lean バージョン・公開先の一括設定
│   ├── generate.sh        ローカルで blueprint を生成し site/ を組み立て
│   ├── publish-code.sh    Lean project を公開リポジトリへ反映
│   ├── publish-page.sh    site/ を公開リポジトリの GitHub Pages へ公開
│   └── lib.sh             共通処理
├── publish.env            公開先の設定（PUBLIC_REPO など）
├── .publishignore         公開時に除外するパス
└── .github/workflows/     ci.yml, blueprint.yml, pages.yml, ...
```

## 依存関係のバージョン

`lakefile.toml` では LeanArchitect と Mathlib を同じタグ（例: `v4.34.0`）に固定しています。
LeanArchitect は Lean のリリースごとにタグを切っているため、`init.sh --lean` で両方を同時に切り替えられます。
`require` の順序は「LeanArchitect → checkdecls → mathlib」で、Mathlib を最後に置くことで共通依存（batteries など）は Mathlib のバージョンが優先されます。
