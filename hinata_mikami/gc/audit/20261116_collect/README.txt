2026-11-16 JST: sweep の alloc / Free 境界と collect 仕様の確認

確認対象は現在の src/main.rs、手書き Rocq 証明、対応する stdlib shim と
Radium の意味論。実装の挙動、モデル上の証明、具体的な実行検査を区別する。

完了結果: cargo refinedrust、dune build、公理監査、実行検査がすべて成功。
公理監査は 84 件を検査し、通常 .vo とソースの一致を確認した。
許可済みの関数外延性・証明無関係性以外の公理依存は検出されなかった。

1. alloc は本物の Rust ヒープに確保しているか

実装はそうなっている。Heap::alloc は make_node を呼び、make_node は
std の Box::new(Node { ... }) と Box::into_raw を使う。
Node は i32 等を持つ非ゼロサイズ型なので、Box のゼロサイズ型の例外には
該当しない。make_node / Heap::alloc の本体は今回変更していない。

根拠:
  hinata_mikami/gc/src/main.rs:120  make_node の所有権・freeable_nz 契約
  hinata_mikami/gc/src/main.rs:126  make_node の Box::new / Box::into_raw
  hinata_mikami/gc/src/main.rs:186  Heap::alloc の本体
  hinata_mikami/gc/src/main.rs:92   Heap の各 Node の所有権と解放権限
  https://doc.rust-lang.org/std/boxed/struct.Box.html#method.new
  https://doc.rust-lang.org/std/boxed/struct.Box.html#method.into_raw

ただし、実 allocator までの形式検証が完結しているとは言えない。
make_node_proof と Heap_alloc_proof は、呼出し先が契約を満たすことを
前提とする型付け定理。Box::new / box_new の shim 本体の証明は存在するが、
その先の alloc::alloc は only_spec。また Box::into_raw も only_spec。

  stdlib/boxed/src/lib.rs:147       box_new は alloc::alloc を呼ぶ
  stdlib/boxed/src/lib.rs:165       Box::new の shim
  stdlib/boxed/src/lib.rs:202       Box::into_raw は only_spec
  stdlib/alloc/src/lib.rs:73        alloc::alloc は only_spec
  stdlib/boxed/output/boxed/proofs/proof_Box_T_new.v
  stdlib/boxed/output/boxed/proofs/proof_box_new.v
  stdlib/boxed/output/boxed/generated/generated_template_box_new.v:24
    alloc_alloc_loc の関数仕様が定理の前提であることを明示する。
  hinata_mikami/gc/output/gc/generated/generated_template_make_node.v:35
    Box::into_raw / Box::new の関数仕様が定理の前提であることを明示する。

検証上の freeable_nz は単なるアドレスの集合ではない。非ゼロサイズでは
freeable となり、割当て ID と al_alive=true の所有権を持つ。
したがってモデル上の生きた HeapAlloc と Node の内容を扱っている。
このモデルと実 allocator の対応に上記の信頼境界がある。

  theories/refinedrust/radium/ghost_state.v:177  freeable_def
  theories/refinedrust/radium/ghost_state.v:209  freeable_nz

2. Iris 上なら Free の概念もあるのではないか

このプロジェクトには明示的にある。対象言語 Radium が Alloc と Free の
操作的意味論を定義し、Iris 上でその規則を証明している。
FreeS は free_block を要求し、free_block はセルを heap_free で削除し、
割当てメタデータの al_alive を true から false に変える。
wps_free はセル所有権と全解放権限を使ってこの実際のモデル状態遷移を扱う。

  theories/refinedrust/radium/lang.v:641        AllocS
  theories/refinedrust/radium/lang.v:729        FreeS
  theories/refinedrust/radium/heap.v:386        alloc_new_block
  theories/refinedrust/radium/heap.v:406        free_block
  theories/refinedrust/radium/lifting.v:2296    wps_free
  stdlib/alloc/theories/shims.v:4              Alloc の code shim
  stdlib/alloc/theories/shims.v:19             Free の code shim

一方、「解放権限を持つ」「事後条件に権限が残らない」から、Free の実行は
導けない。Iris の資源は論理上破棄できる。今回追加した memory_boundary.v は、
deallocation_permission_can_be_discarded : freeable l size 1 HeapAlloc -∗ emp
を証明し、権限の消失だけでは実行履歴にならないことを確かめる。
同じファイルの free_block_marks_allocation_dead は、操作的な free_block が
実行された場合には、割当てメタデータが実際に false になることを証明する。
前者は論理上の推論、後者はプログラム状態の遷移についての命題。

  hinata_mikami/gc/output/gc/audit/memory_boundary.v:10
  hinata_mikami/gc/output/gc/audit/memory_boundary.v:17
  https://iris-project.org/pdfs/2022-lmcs-actris2-final.pdf
    本文 pp.13-14 の affine separation logic と資源の破棄規則。

現在の sweep は、実際の Vec 更新と生存ノードの所有権を検証する。
未マーク分岐には remove -> from_raw -> Drop の呼出しがあり、その並びと
引数スロットを drop_calls.v が生成 CFG に対して検査している。
ただしこの静的な検査は、全ループの実行履歴と各 Node の Free の対応を
証明するものではない。Box の drop glue の証明も destructor の仕様に依存し、
Box::drop 自体は only_spec。Free の概念がモデルに存在することと、sweep の
全削除対象について実 allocator の dealloc まで証明したことは別々に確認が必要。

  hinata_mikami/gc/src/main.rs:434             未マーク分岐
  hinata_mikami/gc/output/gc/audit/drop_calls.v:99
  hinata_mikami/gc/output/gc/audit/drop_calls.v:118
  stdlib/boxed/src/lib.rs:174                  Box::drop は only_spec
  stdlib/boxed/output/boxed/generated/generated_template_drop_glue_Box.v:23
    destructor の関数仕様が drop glue の定理の前提になっている。
  stdlib/alloc/src/lib.rs:85                   dealloc も only_spec

3. collect のアノテーションの変更

collect_post の定義と呼出しをなくし、アノテーションに直接、次の契約を書く。

  前提: 0 < length locs、all_unmarked marks、通常の Heap 不変条件
  事後: forall l, reachable_loc locs nexts l <-> l ∈ alive

locs / nexts は開始時のグラフ。root は開始時の locs[0]。
alive は終了後の実際の all_nodes の内容で、observe と Heap 不変条件が
その対応を保証する。生存は mark ビットではなく終了後の所属で定義する。
marks_after は mark 直後のマーク列で、終了後のマーク列はすべて false。

さらに、終了前後の到達可能なアドレスが同じことと全マークのリセットを、
別々の ensures としてそのまま維持した。observe による value / next の
フィルタと、生存 Node の所有権・freeable_nz の保証も維持している。
事前条件から事後条件が導かれるので、要求された
unmarked ⇒ (reachable ⇔ 生存) が契約に直接現れる。
空の Heap は引き続き collect の事前条件を満たさない。

  hinata_mikami/gc/src/main.rs:440             説明と直接の契約
  hinata_mikami/gc/src/main.rs:454             Hunmarked
  hinata_mikami/gc/src/main.rs:459             observe
  hinata_mikami/gc/src/main.rs:469             reachable ⇔ 生存
  hinata_mikami/gc/src/main.rs:476             到達可能性の保存
  hinata_mikami/gc/src/main.rs:482             マークのリセット
  hinata_mikami/extra_proofs/gc/collect_contract.v
    ラッパー述語を使わない数学的な合成定理。
  hinata_mikami/gc/output/gc/proofs/proof_Heap_collect.v
    実際の collect 本体の型付け証明。sweep 後の資源から Heap 不変条件を再構成。

生存集合への所属は、除去された全ノードが Free 済みという命題ではない。
上記は正常復帰時の契約であり、全実行の終了性や Free の実行履歴を新たに
証明したとするものではない。

4. 実 Rust の allocator を観測する具体的な実行検査

check_runtime.py は現在の src/main.rs を一時ディレクトリにコピーし、
空の main だけを検査用 main に置換する。GC の関数本体とアノテーションは
現在のソースのまま。追加した global allocator は System.alloc / dealloc に
委譲し、割当てアドレス・サイズ・アラインメントごとのイベントを、
割当てを行わない固定長の atomic 配列に記録する。

グラフ: Node 0 -> 1 -> 2 -> 1、到達不能な Node 3 <-> 4。
全ノードの開始時マークは false。collect を 2 回連続して実行する。

  Node 0, 1, 2: 各アドレスに System.alloc 1 回、dealloc 0 回、生存
  Node 3, 4:    各アドレスに System.alloc 1 回、dealloc 1 回、除去

生存 Node の value / next の保持と mark のリセットも検査する。
2 回目の collect でも同じ 3 ノードが残り、解放回数は増えない。
出力には元の src/main.rs の SHA256 と rustc のバージョンを含める。
これは実 allocator を通る具体的な実行の証拠であり、全実行に対する形式証明
ではない。また allocator の dealloc は OS へのページ返却を意味しない。

  check_runtime.py       再実行用の観測器と検査
  runtime.log.txt        実行結果と元ソースの SHA256

5. ビルド・公理監査の再現

  cd /home/mikam/RefinedRust/hinata_mikami/gc
  source ./activate.sh
  cargo refinedrust -- --locked --offline
  dune build
  python3 audit/check_assumptions.py --date 2026-11-16 \
    --report audit/20261116_collect/assumptions.log.txt \
    --raw-output audit/20261116_collect/assumptions-raw.log.txt
  python3 audit/20261116_collect/check_runtime.py

結果:
  cargo-refinedrust.log.txt   Rust から Rocq への再生成
  dune-build.log.txt          最終の Dune ビルド出力
  check-status.log.txt        ビルド・公理監査の終了コード
  assumptions.log.txt        通常 .vo とソース一致を確認した定理ごとの公理一覧
  assumptions-raw.log.txt    Rocq の Print Assumptions の生出力

公理監査は functional_extensionality_dep と proof_irrelevance のみを許可する。
only_spec の呼出し先契約は型付け定理の前提なので、この監査で検出する
グローバル公理とは別の信頼境界として上記 1、2 で明記した。
このセッションでは ben-mcp のツールが提供されていないため、個別証明の
確認と状態照会には同じ Rocq 9.2 の compile / repl を直接使用した。
