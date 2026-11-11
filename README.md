# TPPmark 2026: Othello の解決結果の形式化（Lean 4）

[TPPmark 2026](https://auto-res.github.io/tpp2026/ja/tpp2026mark/)「Othello の解決結果を定理証明支援系で形式化せよ」への解答です。
証明支援系は **Lean 4**（v4.35.0、Mathlib 不使用・標準ライブラリのみ）です。

*English summary.* A Lean 4 formalization of n × n Othello with machine-checked proofs that
White wins 4 × 4 Othello (optimal result 3–11; all computation is done by the Lean kernel and
the proof is re-checked by independent checkers) and that 6 × 6 Othello ends 16–20 under optimal
play (two game-tree searches run with `native_decide`).  The 8 × 8 result (a draw) is stated and
reduced to a finite computation, but **not proved**.

## 結果の一覧

| 問題 | 主張 | 定理 | 状況 |
|---|---|---|---|
| 1 (4×4) | 後手（白）が勝つ | `white_wins_4x4`（最善結果は 3–11：`othello_4x4`） | **証明済み**。計算は Lean カーネルが実行 |
| 2 (6×6) | 後手（白）が 20–16 で勝つ | `othello_6x6` | **証明済み**。探索 2 本は `native_decide` |
| 3 (8×8) | 引き分け | `Othello8Draw`（主張の定義） | **未証明**。定式化・有限計算への帰着・周辺事実のみ |

主張は次の通りです（`Othello/Spec.lean` の定義だけで読めます。名前空間は `Othello`）。

```lean
-- 問題 1
theorem white_wins_4x4 : Secures 4 .white 1 (initial 2) .black
theorem othello_4x4    : OptimalResult 4 (initial 2) .black (-8)
-- 問題 2
theorem othello_6x6    : OptimalResult 6 (initial 3) .black (-4)
-- 問題 3（主張の定義のみ。証明はありません）
def Othello8Draw : Prop := OptimalResult 8 (initial 4) .black 0
```

## 「最善手でプレイした場合」の定式化

仕様は `Othello/Spec.lean`（約 170 行）にまとめてあり、ビットボードも探索も登場しません。

* 盤面は `Board := Int × Int → Option Color`（各マスにどの石があるか）。盤の大きさ `n` は規則のパラメータ。
* `flips`（返る石）、`Legal`（合法手：盤上の空きマスで 1 枚以上返る）、`play`（着手後の盤面）、
  `moves`（合法手の一覧）、`margin`（石数の差。空きマスは数えません）。
* 手番側に合法手があれば必ず打ち、なければパス、双方に合法手がなければ終局。
* **`Secures n p v b c`**：盤面 `b`・手番 `c` から、プレイヤー `p` が「相手がどう打っても、終局時の石差
  （自分 − 相手）が `v` 以上になる」ことを保証する戦略を持つ。帰納的述語で、導出木がそのまま戦略です
  （`over` 終局 / `pass` パス / `choose` 自分の手番で 1 手選ぶ / `reply` 相手の手番ですべての手に応じる）。
* **`OptimalResult n b c v`** := 黒が `v` 以上を保証でき、かつ白が `-v` 以上を保証できる
  （＝双方最善なら黒から見た石差がちょうど `v`）。

したがって `othello_6x6 : OptimalResult 6 (initial 3) .black (-4)` は
「白は 4 石差以上の勝ちを保証でき、黒は 4 石差以内の負けに抑えられる」こと、すなわち最善進行の結果が
16–20（白の 20–16 勝ち）であることを述べています。

Allis [4] の分類でいえば、問題 1・2 は初期局面のゲーム値と、それを達成する双方の戦略の存在を示す
「弱解決（weakly solved）」に当たります（戦略は `Secures` の証明項として得られます）。

この定式化が妥当であることを支える一般的な定理も証明しています（任意の `n`）。

* `Secures.consistent` / `OptimalResult.unique`（`Lemmas.lean`）：最善結果は高々 1 つ。
* `exists_optimalResult`（`Determinacy.lean`）：どの局面にも最善結果が存在する（後退帰納法）。
  つまり「最善手でプレイした場合の結果」はどの盤サイズでも well-defined で、問題 3 の主張も意味を持ちます。
* `mem_flips_iff`（`Lemmas.lean`）：仕様の（実行可能な）`flips` が、ルールブック通りの
  「同一直線上で自分の石に挟まれた相手の石の連なり」と一致する。

## 証明の構成

```
Othello/Spec.lean        仕様（規則と Secures）              ← 定理の意味を決める定義はここだけ
Othello/Lemmas.lean      仕様に関する基本補題（一意性、flips の特徴付け）
Othello/Determinacy.lean 最善結果の存在
Othello/Bits.lean        UInt64 を「ビット位置の集合」として扱う補題
Othello/Bitboard.lean    ビットボードの配置と、シフトによる「歩行」の意味
Othello/Refine.lean      ビットボード上の着手生成が仕様と一致することの証明
Othello/Search.lean      検証付きゲーム木探索 secMe / secOp と健全性定理 sec_sound
Othello/HintParse.lean   ヒント文字列の読み込み（信頼不要）
Othello/Four.lean        問題 1
Othello/Six/*.lean       問題 2 の部品（Hints: ヒント、Popcount: 石数計算の検証、Black / White: 探索）
Othello/Six.lean         問題 2 の定理
Othello/Reference.lean   仕様を直接実行する参照探索と棋譜の検査（任意の n、低速）
Othello/Eight.lean       問題 3（主張・帰着・周辺事実）
Othello/Lines.lean       最善結果を実現する具体的な棋譜（4×4: 3–11、6×6: 16–20）
Othello/Axioms.lean      主要定理が依存する公理の一覧（ビルド時に表示）
tools/                   ヒント生成用の外部ソルバーなど（信頼不要）
```

1. **ビットボードの正当性**（`Refine.lean`）。局面を 2 つの 64 ビット語（手番側の石・相手の石）で表し、
   マス `(x, y)` をビット `8y + x` に対応させます。盤の幅が 6 以下なら各行の上位ビットが番兵になり、
   1・7・8・9 ビットのシフトがそのまま 8 方向への 1 歩になります。この表現上の
   `BB.flips`・`BB.mobility` が仕様の `flips`・`Legal` と一致し、着手が `play` と一致することを証明しています
   （`mem_flips_spec`, `mem_mobility_spec`, `Repr.play`, `Repr.margin_eq`）。
2. **探索の健全性**（`Search.lean`）。`secMe` / `secOp` は null-window の αβ 探索に相当する AND/OR 木探索です
   （各節点は「1 手見つければよい」か「全部の手に応じる」かのどちらか）。
   `sec_sound`：探索が `true` を返せば、仕様の意味での戦略 `Secures` が存在する。
3. **計算**。初期局面に対して探索を実行し、`true` になることを Lean に計算させます。

探索順のヒント（`Six/Hints.lean`）と手の並べ替えヒューリスティックは**探索の順序にしか影響せず**、
`sec_sound` は任意のヒントに対して成り立つので、信頼する必要はありません
（ヒントは `tools/gen.cpp` の未検証の C++ ソルバーで生成しました）。

## 何を信頼しているか

### 問題 1（4×4）

探索の実行は `decide +kernel`、つまり Lean カーネル自身の簡約です。コンパイラは信頼していません。

```
'Othello.white_wins_4x4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

さらに、証明を `lean4export` で書き出し、Lean 4.35.0 の配布物に同梱されている外部チェッカー
（`nanoda_bin`、`con-leche`、`con-ron`）で再検査しました。いずれも受理します
（`tools/check_external.sh`。nanoda には上記 3 公理のみを許可）。

### 問題 2（6×6）

探索は 2 本合わせて数百億ノードになり、カーネルでは評価できません（実測でカーネルは毎秒数十〜数百ノード）。
そこで `native_decide`（コンパイルされたコードの実行結果を公理として採用する）を使っています。
Lean 4.35 では `native_decide` ごとに「計算結果そのもの」を述べる公理が 1 つ導入され、
`othello_6x6` が依存する公理は標準の 3 つに加えて次の 3 つだけです。

```
search_black6._native.native_decide.ax_1_1 :
  decide (BB.secMe true masks6 mask6 5 (-4) 80 (parseHint hintBlack6) black6 white6 = true) = true
search_white6._native.native_decide.ax_1_1 :
  decide (BB.secOp true masks6 mask6 5 4 80 (parseHint hintWhite6) black6 white6 = true) = true
popcount_eq_cntBits6._native.bv_decide.ax_1_8 :   -- SAT 証明書の検査結果
  Std.Tactic.BVDecide.Reflect.verifyBVExpr … = true
```

* 最初の 2 つが黒側・白側のゲーム木探索の結果です。**Lean のコンパイラとランタイムが、この 2 つの閉じた式を
  正しく評価したこと**を信頼しています。
* 3 つ目は、終局時の石数計算（ビット並列の popcount）が 1 ビットずつ数える定義と一致することの証明
  （`bv_decide`）で使われる、SAT 証明書チェッカーの実行結果です。
* これら 3 つの公理を許可した上で、`othello_6x6` の残りの部分全体（11,778 宣言）は外部チェッカー nanoda でも
  再検査できます（`tools/check_external.sh`）。

### 仕様そのもの

定理が Othello について述べていると言えるためには、`Spec.lean` が実際の規則を表している必要があります。
これを補強する検査として、仕様を直接実行して次を確認しています（`native_decide`）。

* `perft8`：8×8 の初期局面からの 1〜6 手の進行数が既知の値 4, 12, 56, 244, 1396, 8200 と一致する。
* `takizawa_line`：[1] の最善進行（60 手）が合法な完全な棋譜で、32–32 で終わる。
* `line4_finished` / `line6_finished`：4×4 で 3–11、6×6 で 16–20 に終わる完全な棋譜が存在する
  （外部ソルバーが各手番で最善手を選んだ進行。6×6 は盤が埋まって終わるので、石差 −4 はちょうど 16–20 です）。

## 問題 3（8×8）について

**8×8 が引き分けであることは証明していません。** これは Takizawa [1] の結果で、その証明は約 1.5 × 10¹⁸ 局面の
計算機探索です。証明支援系の中で同程度の規模の計算をやり直す必要があり、本開発の検証付き探索
（1 コアあたり毎秒 10⁷ ノード程度。しかも現在のビットボードは幅 6 までしか扱えません）では到底届きません。
`Othello/Eight.lean` にあるのは次の内容です。

* `Othello8Draw`：主張の定式化（問題 1・2 と同じ枠組み）。
* `othello8_result_exists`：8×8 の最善結果が一意に存在すること（一般の決定性定理の系）。問題 3 はその値が 0 だという主張です。
* `othello8_draw_of_search`：参照探索 `refSecures` が黒・白の双方について成功すれば引き分けが従う、という
  有限計算への帰着（その計算自体は実行不可能な規模です）。
* `perft8`、`takizawa_line`：上記の通り。
* `takizawa_line_tail`：[1] の最善進行の**最後の 14 手は実際に最善**であること。すなわち 46 手目以降に現れる
  すべての局面について、最善結果が引き分けであることを参照探索で証明しています。
  （残り 14 マスより前に遡ると参照探索では急激に時間がかかります。）

## 計算量

| 計算 | 規模 | 所要時間 |
|---|---|---|
| 4×4：白 8 石差勝ち / 黒 8 石差負け以内（カーネル） | 各 400 ノード弱 | 各約 10 秒 |
| 6×6：黒が −4 以上を保証（`search_black6`） | 約 3.7 × 10⁹ ノード | CPU 約 6 分 |
| 6×6：白が +4 以上を保証（`search_white6`） | 約 2 × 10¹⁰ ノード（推定） | CPU 約 35 分 |

6×6 の探索はヒントで指定された節点を並列（`Task`）に評価するので、4 コアのマシンで全体のビルド（`lake build`）は
約 10 分です（実測 10 分 24 秒、CPU 時間 約 41 分）。
参考までに、ヒント生成に使った未検証の C++ ソルバー（置換表つき αβ）でも値は −4 で、
空きマスを勝者に加算する数え方でも同じ −4 になることを確認しています（こちらは形式化していません）。

## ビルドと検証

```
lake build                      # Lean 4.35.0（lean-toolchain 参照）。主要定理の公理一覧が表示されます
./tools/check_external.sh       # 外部チェッカーによる再検査（任意。Lean 4.35.0 同梱のツールを使用）
```

ヒントの再生成（任意）:

```
g++ -O3 -march=native -o gen tools/gen.cpp
./gen 6 B -4 24 5 26 black      # 黒が -4 以上を保証する側 → black.hint
./gen 6 W  4 24 5 27 white      # 白が  4 以上を保証する側 → white.hint
python3 tools/hints_to_lean.py black.hint white.hint 24 Othello/Six/Hints.lean
```

`./gen 6 P -4 0 0 27 x` は双方最善の進行（`Othello/Lines.lean` の `line6`）を出力します。
`tools/crosscheck.py` は、配列ベースの素朴な実装で perft 値と [1] の棋譜を確認するスクリプトです。

## AI の利用について

本解答は AI（Anthropic の Claude。Claude Code 上の 1 セッション）によって作成されました。
提出者は問題ページの URL を渡して「それぞれの問に対して解法を考えて、実行して」と依頼し、
途中で証明支援系の選択（Lean 4）と作業環境に関する許可を行いました。

* 方針の立案（仕様の設計、`Secures` による「最善手」の定式化、ビットボードへの詳細化、
  null-window 探索＋ヒントという証明戦略、問題 3 の扱い）、Lean のコードと証明、
  ヒント生成用の C++ / Python ツール、およびこの README は、すべて AI が作成しました。
* AI は `lake build` による検査を繰り返しながら証明を完成させています。証明の正しさを保証しているのは
  AI ではなく Lean（および上記の外部チェッカー）で、前提は「何を信頼しているか」に書いた通りです。
* 4×4 が 3–11、6×6 が 16–20 であること、8×8 の perft 値、[1] の最善進行は、AI が知識として持っていた値で、
  それぞれ本開発の中で機械的に確認しています（8×8 が引き分けであること自体を除く）。
* 仕様 `Othello/Spec.lean` が意図通りの規則を表しているかどうかは、最終的には人間が読んで確認すべき部分です。

## 参考文献

1. H. Takizawa. *Othello is Solved.* arXiv:2310.19387, 2023.
2. J. Feinstein. *6x6 Othello.* 1993.
3. H. J. van den Herik, J. W. H. M. Uiterwijk, J. van Rijswijck. *Games Solved: Now and in the Future.* Artificial Intelligence 134, 2002.
4. V. Allis. *Searching for Solutions in Games and Artificial Intelligence.* Ph.D. thesis, 1994.
5. D. E. Knuth, R. W. Moore. *An Analysis of Alpha-Beta Pruning.* Artificial Intelligence 6, 1975.
