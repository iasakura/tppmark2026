# TPPmark 2026: Othello の解決結果の形式化（Lean 4）

[TPPmark 2026](https://auto-res.github.io/tpp2026/ja/tpp2026mark/)「Othello の解決結果を定理証明支援系で形式化せよ」への解答です。
証明支援系は **Lean 4**（v4.35.0、Mathlib 不使用・標準ライブラリのみ）です。

*English summary.* A Lean 4 formalization of n × n Othello with machine-checked proofs that
White wins 4 × 4 Othello (optimal result 3–11; checked by the Lean kernel alone) and that
6 × 6 Othello ends 16–20 under optimal play (checked with `native_decide`).  The 8 × 8
result (a draw) is stated and reduced to a finite computation, but **not proved**.

## 結果の一覧

| 問題 | 主張 | 定理 | 状況 |
|---|---|---|---|
| 1 (4×4) | 後手（白）が勝つ | `Othello.white_wins_4x4`（さらに最善結果は 3–11：`Othello.othello_4x4`） | **証明済み**（計算は Lean カーネルが検査） |
| 2 (6×6) | 後手（白）が 20–16 で勝つ | `Othello.othello_6x6` | **証明済み**（探索は `native_decide`） |
| 3 (8×8) | 引き分け | `Othello.Othello8Draw`（主張の定義） | **未証明**。主張の定式化、有限計算への帰着、周辺事実のみ |

定理の主張（`Othello/Spec.lean` の定義だけで読めます）:

```lean
-- 問題 1
theorem white_wins_4x4 : Secures 4 .white 1 (initial 2) .black
theorem othello_4x4    : OptimalResult 4 (initial 2) .black (-8)
-- 問題 2
theorem othello_6x6    : OptimalResult 6 (initial 3) .black (-4)
-- 問題 3（主張のみ）
def Othello8Draw : Prop := OptimalResult 8 (initial 4) .black 0
```

## 「最善手でプレイした場合」の定式化

仕様は `Othello/Spec.lean`（約 170 行）にまとめてあり、ビットボードも探索も登場しません。

* 盤面は `Board := Int × Int → Option Color`（各マスにどの石があるか）。盤の大きさ `n` は規則のパラメータです。
* `flips`（返る石）、`Legal`（合法手：盤上の空きマスで、1 枚以上返る）、`play`（着手後の盤面）、
  `moves`（合法手の一覧）、`margin`（石数の差）。
* 手番側に合法手があれば必ず打ち、なければパス、双方に合法手がなければ終局。
* **`Secures n p v b c`**：盤面 `b`・手番 `c` から、プレイヤー `p` が「相手がどう打っても、終局時の石差
  （自分 − 相手）が `v` 以上になる」ことを保証する戦略を持つ。帰納的述語で、導出木がそのまま戦略です
  （`over` 終局 / `pass` パス / `choose` 自分の手番で 1 手選ぶ / `reply` 相手の手番ですべての手に応じる）。
* **`OptimalResult n b c v`** := 黒が `v` 以上を保証でき、かつ白が `-v` 以上を保証できる
  （＝双方最善なら黒から見た石差がちょうど `v`）。

したがって `othello_6x6 : OptimalResult 6 (initial 3) .black (-4)` は
「白は 4 石差以上の勝ちを保証でき、黒は 4 石差以内の負けに抑えられる」、すなわち最善進行の結果が 16–20
（白の 20–16 勝ち）であることを述べています。

`Othello/Lemmas.lean` では、この定式化の健全さを支える事実を証明しています。

* `Secures.consistent` / `OptimalResult.unique`：双方が同時に得をする保証は不可能で、最善結果は一意。
* `mem_flips_iff`：仕様の（実行可能な）`flips` が、ルールブック通りの
  「同一直線上で自分の石に挟まれた相手の石の連なり」と一致すること。

## 証明の構成

```
Othello/Spec.lean       仕様（規則と Secures）                      ← 信頼すべき定義はここだけ
Othello/Lemmas.lean     仕様に関する基本補題
Othello/Bits.lean       UInt64 を「ビット位置の集合」として扱う補題
Othello/Bitboard.lean   ビットボードの配置と、シフトによる「歩行」の意味
Othello/Refine.lean     ビットボード上の着手生成が仕様と一致することの証明
Othello/Search.lean     検証付きゲーム木探索 secMe / secOp と健全性定理 sec_sound
Othello/Four.lean       問題 1
Othello/Six/*.lean      問題 2（Hints.lean は探索順のヒント、Popcount.lean は石数計算の検証）
Othello/Six.lean        問題 2 の定理
Othello/Reference.lean  仕様を直接実行する参照探索（任意の n、低速）
Othello/Eight.lean      問題 3（主張・帰着・周辺事実）
tools/                  ヒント生成用の外部ソルバー（信頼不要）
```

1. **ビットボードの正当性**（`Refine.lean`）。局面を 2 つの 64 ビット語（手番側の石・相手の石）で表し、
   マス `(x, y)` をビット `8y + x` に対応させます。盤の幅が 6 以下なら各行の上位ビットが番兵になり、
   1・7・8・9 ビットのシフトがそのまま 8 方向への 1 歩になります。この表現の上の
   `BB.flips`・`BB.mobility` が仕様の `flips`・`Legal` と一致すること、着手が `play` と一致することを証明しています
   （`mem_flips_spec`, `mem_mobility_spec`, `Repr.play`, `Repr.margin_eq`）。
2. **探索の健全性**（`Search.lean`）。`secMe` / `secOp` は null-window の αβ 探索に相当する
   AND/OR 木探索です（Knuth–Moore [5] の意味で、各節点は「1 手見つければよい」か「全部の手に応じる」かのどちらか）。
   `sec_sound`：探索が `true` を返せば、仕様の意味での戦略 `Secures` が存在する。
3. **計算**。初期局面に対して探索を実行し、`true` になることを Lean に計算させます。

探索順のヒント（`Othello/Six/Hints.lean`）と手の並べ替えヒューリスティックは**探索の順序にしか影響せず**、
`sec_sound` は任意のヒントに対して成り立つので、信頼する必要がありません
（ヒントは `tools/gen.cpp` の未検証の C++ ソルバーで生成しました）。

## 何を信頼しているか

* **問題 1**：計算は `decide +kernel`、つまり Lean カーネル自身の簡約で検査しています。
  `#print axioms Othello.white_wins_4x4` は `propext, Classical.choice, Quot.sound` のみです。
* **問題 2**：探索は数十億〜数百億ノードになり、カーネルでは評価できません（実測でカーネルは毎秒数百ノード）。
  そのため `native_decide`（コンパイルされたコードの実行結果を信頼する）を使っています。
  `#print axioms Othello.othello_6x6` には上記に加えて `Lean.ofReduceBool`（と `Lean.trustCompiler`）が現れます。
  つまり **Lean のコンパイラとランタイムを信頼しています**。また終局時の石数計算（popcount）の正しさは
  `bv_decide`（SAT ソルバー＋検証済みチェッカー、これも `ofReduceBool` に依存）で証明しています。
* 仕様（`Spec.lean`）が実際の Othello の規則を表していること。これを補強するため、
  `Othello/Eight.lean` で、仕様から数えた 8×8 の局面数（perft）が既知の値 4, 12, 56, 244, 1396, 8200 と一致することを確認しています。

## 問題 3（8×8）について

**8×8 が引き分けであることは証明していません。** これは Takizawa [1] の結果で、その証明は約 1.5 × 10¹⁸ 局面の
計算機探索です。証明支援系の中で同程度の計算をやり直す必要があり、本開発の検証付き探索（1 コアあたり毎秒 10⁷ ノード程度）
では到底届きません。`Othello/Eight.lean` に含まれるのは次の内容です。

* `Othello8Draw`：主張の定式化（問題 1・2 と同じ枠組み）。
* `othello8_draw_of_search`：参照探索 `refSecures` が黒・白の双方について成功すれば引き分けが従う、という
  有限計算への帰着（その計算自体は実行不可能な規模です）。
* `perft8`：仕様を `n = 8` で実行したときの局面数が既知の値と一致すること。
* `takizawa_line`：[1] に掲載されている最善進行（60 手）が、仕様の意味で合法な完全な棋譜であり 32–32 で終わること。

## ビルド方法

```
# Lean 4 (v4.35.0)。elan があれば lean-toolchain に従って自動で導入されます。
lake build
```

問題 2 の `native_decide` に時間がかかります（4 コアのマシンで十数分程度。詳細は下の「計算量」を参照）。

公理の確認:

```lean
import Othello
#print axioms Othello.white_wins_4x4   -- [propext, Classical.choice, Quot.sound]
#print axioms Othello.othello_6x6      -- 上記 + Lean.ofReduceBool, Lean.trustCompiler
```

ヒントの再生成（任意）:

```
g++ -O3 -march=native -o gen tools/gen.cpp
./gen 6 B -4 24 5 26 black    # 黒が -4 以上を保証する側のヒント → black.hint
./gen 6 W  4 24 5 26 white    # 白が  4 以上を保証する側のヒント → white.hint
python3 tools/hints_to_lean.py black.hint white.hint 24 Othello/Six/Hints.lean
```

## AI の利用について

本解答は、AI（Anthropic の Claude。Claude Code 上で 1 セッション）に問題ページの URL を渡し、
「それぞれの問に対して解法を考えて、実行して」と依頼して作成したものです。

* 方針の立案（仕様の設計、`Secures` による「最善手」の定式化、ビットボードへの詳細化、
  null-window 探索＋ヒントという証明戦略）、Lean のコードと証明、ヒント生成用の C++/Python ツール、
  この README は、すべて AI が作成しました。
* AI は Lean のコンパイラでの検査（`lake build`）を繰り返しながら証明を完成させています。
  証明の正しさは AI ではなく Lean が保証しており、信頼の前提は上の「何を信頼しているか」の通りです。
* 人間（提出者）が行ったのは、課題の指示、証明支援系の選択（Lean 4）、作業環境に関する許可、
  および成果物の確認です。
* 既知の値（4×4 は 3–11、6×6 は 16–20、8×8 の perft 値、[1] の最善進行）は AI が文献知識として持っていたもので、
  それぞれ本開発の中で機械的に検査しています（8×8 の引き分けそのものは除く）。

## 参考文献

1. H. Takizawa. *Othello is Solved.* arXiv:2310.19387, 2023.
2. J. Feinstein. *6x6 Othello.* 1993.
3. H. J. van den Herik, J. W. H. M. Uiterwijk, J. van Rijswijck. *Games Solved: Now and in the Future.* Artificial Intelligence 134, 2002.
4. V. Allis. *Searching for Solutions in Games and Artificial Intelligence.* Ph.D. thesis, 1994.
5. D. E. Knuth, R. W. Moore. *An Analysis of Alpha-Beta Pruning.* Artificial Intelligence 6, 1975.
