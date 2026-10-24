GC の追加検査（2026-10-23）

主要な事後条件は ../src/main.rs の sweep と、
../../extra_proofs/gc/sweep_contract.v にある。
このディレクトリは生成されたコードを独立に検査するためのもの。
生成ファイルは編集しない。
GC の生成 theory は output/dune-project の私有 theory なので、
それを読む手書きの検査 theory も output/gc/audit/ に配置している。
この audit ディレクトリは自動生成される generated/ とは別物。

../output/gc/audit/drop_calls.v が証明すること:
  * 既存の Radium stmt_step に一意の Call 観測を付けられる。
    観測は実際の成功した Call 遷移と関数表の解決を必要とする。
    観測を消すと元の意味論の遷移に戻る。
  * 実際の Heap_sweep_def の未マーク分岐の通常経路は
    remove -> from_raw -> Drop の順に呼ぶ。生存分岐は set_marked を呼ぶ。
    ここで「通常経路」は各 callee が正常復帰する方を選んだ静的な射影。
  * from_raw の返す Box のスロット __20 が Drop の引数である。
    from_raw の引数 __21 に、選択済み node_ptr をコピーすることも検査する。
    Box のスロットのアドレスと、Node のアロケーションのアドレスは異なる。
  * Drop ブロックを jump に替えた変異では、3呼出という検査が成立しない。

これらは、sweep 全体の実行履歴や物理的な Free の証明ではない。
sweep_drop_targets の重複なし等は数学的な候補列に関する補題であり、
各対象の Drop が実行済みであることは表していない。
全ループの実行と観測列の対応には、追加の意味論的な接続証明が必要。
Box::drop / allocator 等の only_spec の本体検証も別途必要。

再実行（bash）:

  cd /home/mikam/RefinedRust/hinata_mikami/gc
  source ./activate.sh
  cargo refinedrust -- --locked --offline
  dune build
  python3 audit/check_assumptions.py \
    --report verification_assumptions_20261023.txt \
    --raw-output /tmp/gc-assumptions.txt

check_assumptions.py は、手動ソースが Dune 内のコピーと一致し、通常の
.vo が存在することを確認してから Print Assumptions を実行する。
許可した関数外延性・証明無関係性以外の公理が現れれば失敗する。
ただし only_spec の呼び出し先契約は定理の前提であり、この監査で
ライブラリ本体の検証が済むわけではない。
