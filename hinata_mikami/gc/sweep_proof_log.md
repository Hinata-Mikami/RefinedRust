# sweepの形式検証 作業ログ

## 最終結果と保証範囲

**現行のsweep仕様の手動証明は完成し、Rocqカーネルによる検査とGC全体の
ビルドに成功した。実際の解放イベントまで含む要求全体については、後述の
Dropの翻訳上の限界が残るため、完全に達成したとは扱わない。**

- `Heap_sweep_proof`は`Time Qed.`で完了し、`proof_Heap_sweep.vo`が生成された。
- 当初の13個の`Admitted`はすべて`Qed`に置き換えた。13補題それぞれの
  `Print Assumptions`はすべて`Closed under the global context`だった。
- sweep本体の`Print Assumptions`は`ProofIrrelevance.proof_irrelevance`と
  `FunctionalExtensionality.functional_extensionality_dep`だけだった。
  既存の未証明Vec用補題2個とGCの未証明補題への依存はない。
  上記2個は既存の論理基盤の原理であり、本作業で追加した公理ではない。
- sweep関数の事前条件・事後条件の注釈は作業開始時のコピーと完全一致する。
  ループの所有権述語から未使用の添字だけを除いた。
- `Vec::remove`の戻り値が元の要素と等しいことは現在のstdlib仕様に含まれない。
  その戻り値を捨て、直前に読み出した同じポインタを`Box::from_raw`へ渡す
  等価な実装へ変更した。stdlibの信頼する仕様を強化する変更は行っていない。
- 他の9個の関数証明、`collect`以降のRustコード、既存の未コミットのコメントは
  保存した。生成ファイルの直接編集やパッケージの再インストールは行っていない。

### 最終ビルド・検査

| 場所 | コマンド・確認 | 結果 | 実時間 |
|---|---|---|---|
| `hinata_mikami/extra_proofs/gc` | `dune build -j 1 --display=short` | 成功（最終依存グラフ確認） | 0.31秒 |
| `hinata_mikami/gc` | `cargo +nightly-2026-02-28 refinedrust -- --locked --offline` | 成功、10関数を翻訳 | 0.92秒 |
| 同上 | `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo` | 未証明Vec依存を除いた最終ソースのコンパイルに成功 | 254.59秒 |
| 同上 | `dune build -j 1 --display=short` | GC全体成功（最終依存グラフ確認） | 0.41秒 |
| 同上 | sweep本体と13補題の`Print Assumptions` | 期待する基盤原理のみ／13補題は閉じている | 24.17秒 |

最終全体確認はキャッシュを利用した。sweepは直前に最終ソースから再コンパイル
しており、他の9証明も同じ生成コードに対するビルドを済ませている。
最終Rust生成以降の変更は手動Rocq証明だけなので、古いテンプレートは使っていない。
sweepの`Qed`だけで88.552秒、子プロセスの最大RSSは4,024,216 KiBだった。
8 MiB、64 MiB、256 MiBのスタック上限でSIGSEGVが発生した試行があり、
最終的にはsoftスタック上限を解除し、並列数1で成功した。

### 再現するためのコマンド

```sh
cd /home/mikam/RefinedRust
eval "$(opam env --switch=refinedrust-rocq91 --set-switch)"
export PATH="/home/mikam/.cargo/bin:$PATH"
ulimit -S -s unlimited

cd /home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc
dune build -j 1 --display=short

cd /home/mikam/RefinedRust/hinata_mikami/gc
cargo +nightly-2026-02-28 refinedrust -- --locked --offline
dune build -j 1 --display=short
```

`ulimit -S`は当該シェルと子プロセスのsoft上限だけを変更する。
システム設定やopamのインストール状態を変更する操作ではない。

### Duneのバージョンエラーが出た場合

`(lang dune 3.21)`が未対応というエラーは、システム側のDune 3.14を使った場合に
発生する。既存のopam switchにはDune 3.23.1とRocq 9.1.0があるので、
再インストールや`dune-project`の変更は不要。ビルドを実行するターミナルで
次を実行する。エージェントの子シェルの環境切替は、ユーザーの別ターミナルに
自動では反映されない。

```sh
eval "$(opam env --switch=refinedrust-rocq91 --set-switch)"
hash -r
command -v dune  # /home/mikam/.opam/refinedrust-rocq91/bin/dune
dune --version  # 3.23.1
ulimit -S -s unlimited
dune build -j 1 --display=short
```

### 依存関係の検査

既存の`proofs/_RocqProject`の引数を適用したRocqセッションで次を実行した。
最終結果を含むログは`/tmp/rr-sweep-verified-assumptions.log`にある。

```coq
From hinata_mikami.extra_proofs.gc Require Import gc_defs heap_lemmas.
From refinedrust.examples.gc.proofs Require Import proof_Heap_sweep.
Print Assumptions Heap_sweep_proof.
Print Assumptions sweep_marks_length.
Print Assumptions sweep_marks_0.
Print Assumptions keep_marked_suffix_step_true.
Print Assumptions sweep_marks_step_true.
Print Assumptions keep_marked_suffix_step_false.
Print Assumptions sweep_marks_step_false.
Print Assumptions sweep_nodes_inv_init.
Print Assumptions sweep_nodes_inv_step.
Print Assumptions sweep_nodes_inv_done.
Print Assumptions keep_marked_length_same_mask.
Print Assumptions keep_marked_NoDup.
Print Assumptions keep_marked_Forall.
Print Assumptions marks_closed_keep_marked_next_valid.
```

### 証明した性質と残る境界

現行仕様に対して、`all_nodes`が元のマーク済みノードだけから成り、値とnextを
保ち、マークがすべてfalseになること、保持ノードの所有権・解放可能性・長さ・
NoDup・非NULL性・nextの有効性を保持することを証明した。
未マークノードをVecから取り除き、対応するノード所有権と`freeable_nz`を使って
`Box::from_raw`の前提条件を満たすことも検査される。

ただし、このフロントエンドはMIRのDropから実際の解放処理を生成しない。
現行事後条件も、削除したアドレスがallocatorの生存集合から消えたことまでは
要求していない。Irisの資源を事後条件へ残さないことだけでは、実解放や
メモリリークがないことの証明にはならない。従って「実際の解放イベント」まで
Rocqで保証したとは主張しない。これは未証明補題を残して解決した問題ではなく、
翻訳・意味論・仕様が観測する性質の範囲の問題である。
既存のstdlib仕様と`vec_index`等の`only_spec`も検証の信頼境界として残る。
`collect`は本作業の検証対象ではない。

以下は試行の経過と、修士論文に利用できる技術的知見の詳細である。


## 2026-10-19: 作業開始と基準ビルド

対象は`Heap::sweep`とその補助定義・証明。`collect`は対象外。
作業開始時の変更は`src/main.rs`のコメント・空白のみだった。既存の差分を保持し、
主要4ファイルの作業開始時点のコピーを`/tmp/rr-sweep-original/`に保存した。

各ビルドでは以下の環境を適用する。

```sh
eval "$(opam env --switch=refinedrust-rocq91 --set-switch)"
export PATH="/home/mikam/.cargo/bin:$PATH"
```

| 実行場所 | コマンド | 結果 | 実時間 |
|---|---|---|---|
| `hinata_mikami/extra_proofs/gc` | `dune build --display=short` | 成功。ただし既存13補題は`Admitted` | 0.35秒 |
| `hinata_mikami/gc` | `dune build --display=short` | 失敗。現在の`proof_Heap_sweep.v:173`で`This proof is focused, but cannot be unfocused this way` | 22.41秒 |

基準ビルドのログは`/tmp/rr-sweep-initial-aux.log`と
`/tmp/rr-sweep-initial-gc.log`。現在の失敗は`Hkeep_vals`の未完了ブロックであり、
過去ログの`Qed`失敗とは区別する。

## 補題の設計上の問題

- `sweep_nodes_inv_step`は`Vec::remove`後も任意の添字依存述語`Φ k ...`を
  保持すると主張していた。削除による添字の変化でこれは一般には成立しない。
  実際のノード所有権は添字に依存しないので、その性質を定義に反映する。
- `marks_closed_keep_marked_next_valid`は元のnextの有効性を仮定していなかった。
  Heapの既存不変条件にある`Forall (fun n => n = NULL_loc ∨ n ∈ locs) nexts`
  を前提に追加する必要がある。sweepの事後条件を弱める変更ではない。

元の命題が一般には成立しないことは、次の反例でも分かる。

- 添字依存の`Φ k v l n m := ⌜v = Z.of_nat k⌝`を考え、`vals = [0; 1]`、
  `marks = [false; true]`、`cut = 1`とする。削除前には添字0の値0、添字1の値1
  でΦが成立する。未マークの先頭を削除すると残る値1の添字が0となり、
  元の一般的なステップ補題は`1 = 0`を要求してしまう。
- 元のnext有効性補題では、`locs = [a]`、`nexts = [b]`、`marks = [true]`、
  `b ≠ NULL_loc`かつ`b ∉ locs`とする。`marks_closed`は、bを指すlocsの添字が
  存在しないので成立するが、残存nextの有効性という結論は成立しない。

今後、純粋なリスト補題、所有権不変条件、sweep本体の順で証明し、補助側の
ビルド後にGC側の再生成とビルドを行う。生成ファイルの直接編集は行わない。

## 純粋なsweep補題の証明

`gc_defs.v`の6個の`Admitted`をすべて`Qed`へ置き換えた。
`keep_marked_suffix`と`sweep_marks`の1ステップの性質は、処理位置に関する
構造帰納法で証明できる。リスト先頭を同時に除くことで、`delete`や更新の
添字計算を一般的な書換え探索に任せずに済んだ。

| 実行場所 | コマンド | 結果 | 実時間 |
|---|---|---|---|
| `hinata_mikami/extra_proofs/gc` | `dune build --display=short` | 成功 | 4.03秒 |
| `hinata_mikami/gc` | `cargo +nightly-2026-02-28 refinedrust -- --locked --offline` | 成功、sweepを含む10関数を翻訳 | 1.83秒 |
| `hinata_mikami/gc` | `dune build --display=short` | 他の9関数は成功、sweepは既存の173行目で失敗 | 159.15秒 |

GC全体の再ビルドには約2分40秒かかった。長時間タクティクを途中で打ち切らず、
終了コードとログを取得した。並行して補助側のDuneを起動した試行はロックで
即座に拒否されたため、以後Duneは同一ワークスペースで順次実行する。

所有権述語の引数から未使用の添字を除く変更に合わせ、sweepのループ注釈と
手動証明の`Φ`の引数を調整する。値、位置、next、mark、所有権および解放可能性
の内容は維持する。next有効性補題には既存Heapの非NULL性も前提として渡す。

## 所有権補題の完成と信頼境界

補助側のビルド`aux-08`で、当初の13個の`Admitted`をすべて除去した状態で成功。
`elem_of_keep_marked`を追加して、保持された要素から元の添字とtrueのマークを
取り出せるようにした。所有権の1ステップ補題は、処理位置とリストの構造に
沿う帰納法で証明した。添字に依存しない所有権を先頭と残部に分ける補題により、
削除後の添字のずれを所有権命題から切り離せる。

証明中の局所的な失敗には、stdppの補題名が`list_elem_of_lookup_2`であること、
`iFrame`が存在変数を自動的に具体化すること、`P -∗ P`には`iIntros`が必要である
ことがあった。これらを実際の定義・proof stateに合わせて修正した。
一度ルートからビルドを起動して対象が広がったため、その試行のみ中止し、
補助ディレクトリに限定して再実行した。正常に実行中の重い証明を時間で
打ち切る操作は行っていない。

### Dropの翻訳に関する保証の限界

`rr_frontend/translation/src/body/translation/terminator.rs`の
`mir::TerminatorKind::Drop`分岐は`DropE`を`_drope`として構築するが、出力文へ
追加せず次のブロックへ進む。sweepの生成コードでも`Box::from_raw`の後には
`local_dead "__20"`があり、明示的な解放呼び出しはない。

従って、既存仕様に対する証明は、未マークノードのVecからの削除、
`Box::from_raw`に渡すノード所有権・`freeable_nz`の整合性、保持ノードの
所有権と値・next・マークの事後条件を検査する。一方、実際に解放イベントが
発生することやメモリリークがないことは、現状の翻訳と事後条件だけでは
保証しない。RustのDrop動作と、翻訳された意味論で検証される性質を区別する。
この限界を補題や事後条件の弱化で隠さない。

既存の`wrappers::vec_index`は`only_spec`であり、その仕様を信頼する。
既存のループ中の`#[rr::ignore] || {}`は不変条件を付ける空のマーカーで、
ノード処理を除外するものではない。新たな`ignore`や`only_spec`は追加しない。

## sweep本体と自動証明の接続

- 初期不変条件の所有権は`aligned_nodes`から`sweep_nodes_inv_init`で構築する。
  Lithiumが`keep_marked_suffix`のbig-separationをprefixとsuffixへ分解するため、
  初期位置ではsuffixが空であることを明示し、prefixへ所有権を渡す必要がある。
- ループ本体では`sweep_nodes_inv_step`から対象ノードと継続（生存分岐では
  マーク解除後の所有権を受け取るwand）を取り出す。
- `apply_update updateable_strip_guards`は任意の判断に適用できるわけではない。
  `FindLoc`まで自動証明を進めた後では`Updateable`インスタンスがなく失敗する。
  `rep <-! liRStep`で直前の更新可能な判断まで戻してからguardを外す。
- `Z.to_nat (ic - 1)`と`(Z.to_nat ic - 1)%nat`は定義的に同じではない。
  算術で等式を証明し、Vecのtotal lookup、ノード所有権、関数呼び出しの
  refinementを同じ表現へ揃える必要がある。これにより`Node::set_marked`の
  呼び出し前で止まっていた自動証明が通過し、マーク解除後のループ不変条件
  再構成まで進んだ。
- 終了分岐では`ic = 0`を示して`sweep_nodes_inv_done`を適用すると、空マークの
  所有権を事後条件へ渡せる。長さ、NoDup、非NULL性、next有効性は純粋な補題で
  別途解決する。

ここまでの失敗はRocqの型・命題・タクティクの適用条件に関するものであり、
タイムアウトとは区別した。長い試行では実行中プロセスのCPU使用率も記録し、
`rocqworker`が計算を継続していることを確認している。

### Vec::removeの戻り値の仕様不足と実装の等価な変更

`stdlib/vec/src/lib.rs`の`Vec::remove`には`rr::returns`がなく、生成された
`type_of_Vec_TA_remove`は戻り値を任意の`ret`として存在量化している。
削除後のリストは`delete i xs`と規定されるが、返るraw pointerが元のi番目の
ポインタであることは、この仕様からは導けない。その戻り値をそのまま
`Box::from_raw`へ渡しても、手元のノード所有権に結び付けられない。

標準ライブラリの`only_spec`契約を強めて新しい仮定を導入することを避け、
sweepの未マーク分岐を以下の等価な形へ変更した。

```rust
let _ = nodes.remove(i);
let _ = Box::from_raw(node_ptr);
```

`node_ptr`は直前の同一インデックスから読み出した値であり、その後removeまでに
Vecの要素を変更していない。実際のRustでは元のremoveの戻り値と一致するため、
削除・Boxへの再所有化という動作を保持する。証明ではremoveの戻り値に関する
未提供の保証に依存しなくなる。事後条件の変更や新しい`only_spec`の追加はない。
この実装変更後は必ず再生成し、新しいテンプレートに対してビルドする。

### 削除後の型比較とリストの正規化

再生成したコードでは、removeの任意の戻り値を捨て、既知のポインタを
`Box::from_raw`に渡す証明義務へ進めた。さらに、Vecのrefinementは
`delete i (PlaceIn <$> xs)`という形で更新される一方、ループ不変条件は
`PlaceIn <$> keep_marked_suffix ...`という形になる。
`list_fmap_delete`の逆向きの書換えと、証明済みの削除ステップ補題を使い、
両者を同じリストに正規化する必要があった。

生存分岐では、`Node::set_marked`が返した所有権を、credit storeから取得した
資源と`guarded_intro`で再びguardedにし、`sweep_nodes_inv_step`の継続へ渡す。
その後、big-separationをprefixとsuffixへ分けてLithiumへ渡す。
削除分岐でも同じprefix/suffixの分解を使うが、Vecの型比較を先に進める必要が
あるため、`prove_with_subtype_default`を適用する位置は生存分岐と異なる。

診断タクティクの表示に現れた`Inhabited P`は、実際の未解決命題`P`を表示する
ために診断側が追加するラッパーだった。純粋条件の証明では`P`自体へリスト補題
や算術を適用する必要があり、`constructor`でラッパーを外す方針は誤りだった。
この点を修正した試行`sweep-14`では純粋な未解決条件は残らず、最後の削除分岐の
所有権prefixへの接続だけが残った。

## sweep単体の証明成功

`sweep-15`で`Heap_sweep_proof`の`Qed`と`.vo`生成が初めて成功した。
実時間は196.03秒。生存・削除・終了の各分岐と、保留していた純粋条件の
すべてを同じビルドで解決できた。

成功後、未解決goalを表示するために置いていた`print_remaining_goal`と
`print_remaining_sidecond`を手動証明から除去した。最終ソースには
`Admitted`、`admit`、`Axiom`、`Abort`やこれらの診断呼び出しはない。
この状態で補助側のビルドとGCの再生成に成功し、GC全体を最終確認する。

差分監査では`collect`以降のRustコードと、sweep以外の9個の関数証明が
元の内容と一致した。既存の未コミットのコメントも保存されている。

## 全体ビルドにおけるRocqワーカーの異常終了

診断コード除去後のGC全体ビルドで、既存の`proof_Heap_mark`と
`proof_Heap_alloc`のワーカーが`got signal SEGV`で終了した。
これらの証明ソースは変更していない。証明の未解決goalやタイムアウトとは
区別する。実行中のsweepとmark_fromは中断せず終了を待つ。

このシェルのスタックsoft上限は8192 KiB、hard上限は無制限だった。
メモリは調査時点で約5 GBが利用可能だったが、これだけで異常終了の原因を
断定することはできない。次の再試行では`ulimit -s 65536`により子プロセスの
スタック上限を64 MiBへ増やし、`dune build -j 1 --display=short`で並列実行を
避ける。システム設定や依存パッケージ、既存の証明内容は変更しない。

なお、sweepの関数に付けた事前条件・事後条件の注釈部分は、作業開始時の
コピーと完全一致することを比較で確認した。

## Print Assumptionsで発見した標準ライブラリへの未証明依存

64 MiBスタック・並列数1でのGC全体ビルドは83.03秒で成功した。
しかし`Print Assumptions Heap_sweep_proof`では、標準的なproof irrelevanceと
functional extensionalityに加え、次の2個がaxiomとして列挙された。

- `generated_specs_vec.resolve_ghost_Vec_T_owned`
- `generated_specs_vec.resolve_ghost_Vec_T_uniq`

これらの元ソースは`stdlib/vec/extra_specs.v`にあり、既存の`Admitted`である。
一方、`sweep_nodes_inv_step`と`marks_closed_keep_marked_next_valid`は
`Closed under the global context`だった。従って、GCの13補題を証明して
ビルドを成功させただけでは、未証明依存なしという完了条件は満たさない。

sweepでVecが保持する要素はすべて具体的なraw pointerであり、要素内の
ghost variableを再帰的に解決する必要はない。上記2個の自動証明インスタンスを
sweepの証明内でのみ無効化し、`program_rules.v`で証明済みの
`resolve_ghost_id`等の一般規則を使って同じ証明義務を処理する方針を採る。
仕様、プログラム、検証対象の処理は変えず、標準ライブラリの生成ファイルも
直接編集しない。この変更をコンパイルと依存関係検査で確認する。

### ビルド記録: aux-06

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build --display=short`
- 終了コード: 1、実時間: 2.46秒
- 詳細ログ: `/tmp/rr-sweep-aux-06.log`

```text
Entering directory '/home/mikam/RefinedRust'
        rocq hinata_mikami/extra_proofs/gc/.hinata_mikami.extra_proofs.theory.d
        rocq hinata_mikami/extra_proofs/gc/heap_lemmas.{glob,vo} (exit 1)
File "./hinata_mikami/extra_proofs/gc/heap_lemmas.v", line 308, characters 44-48:
Error: No applicable tactic.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: aux-07

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build --display=short`
- 終了コード: 1、実時間: 2.59秒
- 詳細ログ: `/tmp/rr-sweep-aux-07.log`

```text
  
  Σ : gFunctors
  RRGS : refinedrustGS Σ
  vals : list Z
  locs, nexts : list loc
  marks : list bool
  Φ : Z → loc → loc → bool → iProp Σ
  Hv : length vals = length marks
  Hl : length locs = length marks
  Hn : length nexts = length marks
  ============================
  aligned_nodes vals locs nexts marks Φ -∗
  aligned_nodes vals locs nexts marks Φ
File "./hinata_mikami/extra_proofs/gc/heap_lemmas.v", line 309, characters 0-4:
Error:  (in proof sweep_nodes_inv_init): Attempt to save an incomplete proof
(there are remaining open goals).

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: aux-08

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build --display=short`
- 終了コード: 0、実時間: 3.76秒
- 詳細ログ: `/tmp/rr-sweep-aux-08.log`

### ビルド記録: generate-02

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo +nightly-2026-02-28 refinedrust -- --locked --offline`
- 終了コード: 0、実時間: 0.86秒
- 詳細ログ: `/tmp/rr-sweep-generate-02.log`

### ビルド記録: sweep-01

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 27.58秒
- 詳細ログ: `/tmp/rr-sweep-sweep-01.log`

```text
  "Hsweep" : sweep_nodes_inv (length marks) vals locs nexts marks Φ
  --------------------------------------∗
  [∗ list] i↦x ∈ take (Z.to_nat (length locs)) vals, 
  [{ ∃ (l n : loc) (m : bool),
     exhale ⌜keep_marked_suffix (Z.to_nat (length locs)) locs marks !! i =
             Some l⌝;
     exhale ⌜keep_marked_suffix (Z.to_nat (length locs)) nexts marks !! i =
             Some n⌝;
     exhale ⌜sweep_marks (Z.to_nat (length locs)) marks !! i = Some m⌝;
     exhale guarded true
              (l ◁ₗ[ π, Owned] # -[# x; # n; # m] @ (◁ (Node_ty <INST!>)));
     {freeable_nz l (ly_size (use_layout_alg' Node_sls)) 1 HeapAlloc}
  }]
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 153, characters 10-25:
Error: Tactic failure: iExact: "Hsweep" :
(sweep_nodes_inv (length marks) vals locs nexts marks Φ) does not match goal.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-02

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 24.49秒
- 詳細ログ: `/tmp/rr-sweep-sweep-02.log`

```text
H14 : (Forall (λ l : loc, loc_a l ≠ 0) locs)
H15 : (marks_closed locs nexts marks)
H16 : (arg_self `has_layout_loc` void*)
H17 : (0 ≤ length locs)
H18 : (length locs ≤ MaxInt usize)
Hvals_marks : (length vals = length marks)
Hlocs_marks : (length locs = length marks)
Hnexts_marks : (length nexts = length marks)
---------------------------------------
(Inhabited (<#> locs = <#> keep_marked_suffix (length locs) locs marks))


File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 172, characters 0-4:
Error:  (in proof Heap_sweep_proof): Attempt to save an incomplete proof
(the proof term is not complete because of given up (admitted) goals).
If this is really what you want to do, use Admitted in place of Qed.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-03

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 58.56秒
- 詳細ログ: `/tmp/rr-sweep-sweep-03.log`

```text
H29 : (MinInt usize ≤ 0 ≤ MaxInt usize)
H30 : (MinInt usize ≤ ic)
H31 : (ic ≤ MaxInt usize)
H32 : (ic > 0)
H33 : (MinInt usize ≤ 1 ≤ MaxInt usize)
H34 : (MinInt usize ≤ ic - 1 ≤ MaxInt usize)
H35 : (0 ≤ ic - 1)
H36 : (ic - 1 ≤ MaxInt usize)
---------------------------------------
(Inhabited (ic - 1 < length (keep_marked_suffix (Z.to_nat ic) locs marks)))


File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 173, characters 0-4:
Error:  (in proof Heap_sweep_proof): Attempt to save an incomplete proof
(the proof term is not complete because of given up (admitted) goals).
If this is really what you want to do, use Admitted in place of Qed.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-04

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 44.80秒
- 詳細ログ: `/tmp/rr-sweep-sweep-04.log`

```text
Entering directory '/home/mikam/RefinedRust'
        rocq hinata_mikami/gc/output/gc/proofs/.refinedrust.examples.gc.theory.d
File "hinata_mikami/gc/output/gc/proofs/dune", lines 2-7, characters 0-1236:
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
Did 97 steps.
Did 2155 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 190, characters 4-19:
Error: Uncaught Ltac2 exception: Rep.RepBacktrack (Rep.BacktrackPoint 1)

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-05

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 80.12秒
- 詳細ログ: `/tmp/rr-sweep-sweep-05.log`

```text
---------------------------------------
(Inhabited
   (Updateable
      [{ '(existT rt2 (lt2, r2, b2, π2)) ← find_in_context 
         FindLoc lc;
         exhale ⌜π2 = π⌝;
         {typed_place [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_1]
          [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 1} []] (π, _fid) lc lt2 r2 UpdStrong b2
          [GetMemberPCtx Node_sls "marked"] HIDDEN_CONT}
      }]))


File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 203, characters 0-4:
Error:  (in proof Heap_sweep_proof): Attempt to save an incomplete proof
(the proof term is not complete because of given up (admitted) goals).
If this is really what you want to do, use Admitted in place of Qed.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-06

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 79.46秒
- 詳細ログ: `/tmp/rr-sweep-sweep-06.log`

```text
H30 : (MinInt usize ≤ 0)
H32 : (¬ 0 > 0)
H33 : (length (keep_marked locs marks) = length (keep_marked vals marks))
H34 : (length (keep_marked nexts marks) = length (keep_marked vals marks))
H35 : (NoDup (keep_marked locs marks))
H36 : (Forall (λ l : loc, loc_a l ≠ 0) (keep_marked locs marks))
---------------------------------------
(Inhabited
   (Forall (λ n : loc, n = NULL_loc ∨ n ∈ keep_marked locs marks)
      (keep_marked nexts marks)))


File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 204, characters 0-4:
Error:  (in proof Heap_sweep_proof): Attempt to save an incomplete proof
(the proof term is not complete because of given up (admitted) goals).
If this is really what you want to do, use Admitted in place of Qed.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-07

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 97.09秒
- 詳細ログ: `/tmp/rr-sweep-sweep-07.log`

```text
H30 : (MinInt usize ≤ 0)
H32 : (¬ 0 > 0)
H33 : (length (keep_marked locs marks) = length (keep_marked vals marks))
H34 : (length (keep_marked nexts marks) = length (keep_marked vals marks))
H35 : (NoDup (keep_marked locs marks))
H36 : (Forall (λ l : loc, loc_a l ≠ 0) (keep_marked locs marks))
---------------------------------------
(Inhabited
   (Forall (λ n : loc, n = NULL_loc ∨ n ∈ keep_marked locs marks)
      (keep_marked nexts marks)))


File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 208, characters 0-4:
Error:  (in proof Heap_sweep_proof): Attempt to save an incomplete proof
(the proof term is not complete because of given up (admitted) goals).
If this is really what you want to do, use Admitted in place of Qed.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-08

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 63.18秒
- 詳細ログ: `/tmp/rr-sweep-sweep-08.log`

```text
Entering directory '/home/mikam/RefinedRust'
        rocq hinata_mikami/gc/output/gc/proofs/.refinedrust.examples.gc.theory.d
File "hinata_mikami/gc/output/gc/proofs/dune", lines 2-7, characters 0-1236:
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
Did 97 steps.
Did 2144 steps.
Did 1123 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 193, characters 22-69:
Error: Unknown interpretation for notation "_ ◁ₗ[ _ , _ ] _ @ _".

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-09

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 62.18秒
- 詳細ログ: `/tmp/rr-sweep-sweep-09.log`

```text
Entering directory '/home/mikam/RefinedRust'
        rocq hinata_mikami/gc/output/gc/proofs/.refinedrust.examples.gc.theory.d
File "hinata_mikami/gc/output/gc/proofs/dune", lines 2-7, characters 0-1236:
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
Did 97 steps.
Did 2144 steps.
Did 1123 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 193, characters 6-84:
Error: No matching clauses for match.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-10

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 2.67秒
- 詳細ログ: `/tmp/rr-sweep-sweep-10.log`

```text
Entering directory '/home/mikam/RefinedRust'
        rocq hinata_mikami/gc/output/gc/proofs/.refinedrust.examples.gc.theory.d
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 92, characters 2-8:
Error: Could not find an instance for "Delete Z (list A)" in
environment:
Σ : gFunctors
RRGS : refinedrustGS Σ
A : Type
cut : nat
xs : list A
marks : list bool


Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-11

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 134.77秒
- 詳細ログ: `/tmp/rr-sweep-sweep-11.log`

```text
H30 : (MinInt usize ≤ 0)
H32 : (¬ 0 > 0)
H33 : (length (keep_marked locs marks) = length (keep_marked vals marks))
H34 : (length (keep_marked nexts marks) = length (keep_marked vals marks))
H35 : (NoDup (keep_marked locs marks))
H36 : (Forall (λ l : loc, loc_a l ≠ 0) (keep_marked locs marks))
---------------------------------------
(Inhabited
   (Forall (λ n : loc, n = NULL_loc ∨ n ∈ keep_marked locs marks)
      (keep_marked nexts marks)))


File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 265, characters 0-4:
Error:  (in proof Heap_sweep_proof): Attempt to save an incomplete proof
(the proof term is not complete because of given up (admitted) goals).
If this is really what you want to do, use Admitted in place of Qed.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: generate-03

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo +nightly-2026-02-28 refinedrust -- --locked --offline`
- 終了コード: 0、実時間: 0.97秒
- 詳細ログ: `/tmp/rr-sweep-generate-03.log`

### ビルド記録: sweep-12

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 103.35秒
- 詳細ログ: `/tmp/rr-sweep-sweep-12.log`

```text
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
Did 97 steps.
Did 2144 steps.
Did 1123 steps.
Did 90 steps.
Did 2104 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 229, characters 6-21:
Error: The RHS of Hindex
    (Z.to_nat (ic - 1))
does not match any subterm of the goal

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-13

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 93.38秒
- 詳細ログ: `/tmp/rr-sweep-sweep-13.log`

```text
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
Did 97 steps.
Did 2144 steps.
Did 1123 steps.
Did 90 steps.
Did 2104 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 233, characters 6-39:
Error: Tactic failure: iApply: cannot apply
(?Goal19 ∗ ?Goal20 ?Goal16 [] True -∗
 prove_with_subtype ?Goal15 ?Goal16 ?Goal17 ?Goal18 ?Goal19 HIDDEN_CONT)%I.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-14

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 159.41秒
- 詳細ログ: `/tmp/rr-sweep-sweep-14.log`

```text
                                                 # -[# x; # n; # m] @
                                                 (◁ (Node_ty <INST!>)));
                                                 {
                                                 freeable_nz l
                                                 (ly_size
                                                 (use_layout_alg' Node_sls))
                                                 1 HeapAlloc}
                                              }]
HIDDEN_CONT


Did 1028 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 279, characters 0-4:
Error:  (in proof Heap_sweep_proof): Attempt to save an incomplete proof
(the proof term is not complete because of given up (admitted) goals).
If this is really what you want to do, use Admitted in place of Qed.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-15

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 0、実時間: 196.03秒
- 詳細ログ: `/tmp/rr-sweep-sweep-15.log`

### ビルド記録: final-aux

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build --display=short`
- 終了コード: 0、実時間: 0.31秒
- 詳細ログ: `/tmp/rr-sweep-final-aux.log`

### ビルド記録: final-generate

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo +nightly-2026-02-28 refinedrust -- --locked --offline`
- 終了コード: 0、実時間: 0.92秒
- 詳細ログ: `/tmp/rr-sweep-final-generate.log`

### ビルド記録: final-gc

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build --display=short`
- 終了コード: 1、実時間: 247.18秒
- 詳細ログ: `/tmp/rr-sweep-final-gc.log`

```text
Did 1211 steps.
Did 152 steps.
Did 15 steps.
Did 416 steps.
Did 162 steps.
Did 15 steps.
Did 475 steps.
Did 959 steps.
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo}
Did 97 steps.
Did 2144 steps.
Did 1123 steps.
Did 90 steps.
Did 2104 steps.
Did 312 steps.
Did 90 steps.
Did 1028 steps.
Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: assumptions

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `/usr/bin/python3 -B /tmp/rr-sweep-assumptions.py`
- 終了コード: 0、実時間: 26.57秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(67108864, 67108864)`
- 詳細ログ: `/tmp/rr-sweep-assumptions.log`

### ビルド記録: final-gc-serial

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、実時間: 83.03秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(67108864, 67108864)`
- 詳細ログ: `/tmp/rr-sweep-final-gc-serial.log`

### ビルド記録: sweep-no-vec-axioms

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 99.20秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(67108864, 67108864)`
- 詳細ログ: `/tmp/rr-sweep-sweep-no-vec-axioms.log`

```text
File "hinata_mikami/gc/output/gc/proofs/dune", lines 2-7, characters 0-1236:
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
Did 97 steps.
Did 2145 steps.
Did 1124 steps.
Did 90 steps.
Did 2419 steps.
Did 92 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 250, characters 6-22:
Error: Expected a single focused goal but 0 goals are focused.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-no-vec-axioms-02

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 116.99秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(67108864, 67108864)`
- 詳細ログ: `/tmp/rr-sweep-sweep-no-vec-axioms-02.log`

```text
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (exit 1)
Did 97 steps.
Did 2145 steps.
Did 1124 steps.
Did 90 steps.
Did 2419 steps.
Did 92 steps.
Did 1027 steps.
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 285, characters 17-21:
Error: No applicable tactic.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-no-vec-axioms-03

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 116.97秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(67108864, 67108864)`
- 詳細ログ: `/tmp/rr-sweep-sweep-no-vec-axioms-03.log`

```text
    MinInt usize
    ≤ loc_a
        (keep_marked_suffix (Z.to_nat ic) locs marks
         !!! (Z.to_nat ic - 1)%nat)
  H44 :
    loc_a
      (keep_marked_suffix (Z.to_nat ic) locs marks !!! (Z.to_nat ic - 1)%nat)
    ≤ MaxInt usize
  x1 : loc
  H45 : x1 `has_layout_loc` Node_sl
  ============================
  delete (Z.to_nat ic - Z.to_nat 1)%nat
    (<#> keep_marked_suffix (Z.to_nat ic) locs marks) =
  <#> keep_marked_suffix (Z.to_nat ic - Z.to_nat 1) locs marks
File "./hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.v", line 287, characters 17-21:
Error: No applicable tactic.

Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-no-vec-axioms-04

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 226.94秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(67108864, 67108864)`
- 詳細ログ: `/tmp/rr-sweep-sweep-no-vec-axioms-04.log`

```text
Entering directory '/home/mikam/RefinedRust'
        rocq hinata_mikami/gc/output/gc/proofs/.refinedrust.examples.gc.theory.d
File "hinata_mikami/gc/output/gc/proofs/dune", lines 2-7, characters 0-1236:
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (got signal SEGV)
Did 97 steps.
Did 2145 steps.
Did 1124 steps.
Did 90 steps.
Did 2419 steps.
Did 92 steps.
Did 1027 steps.
Leaving directory '/home/mikam/RefinedRust'
```

## 未証明依存を除いた版のコンパイラ異常終了への対応

一般規則への切替後、削除分岐の手動prefix接続が不要になったため除去した。
保留された`delete i (<#> xs) = <#> ys`には純粋条件側でも
`list_fmap_delete`を逆向きに適用し、証明済みの削除補題を使う。
この1条件を診断で確認した後、診断コードを除去した。

`sweep-no-vec-axioms-04`は全タクティクの実行後、226.94秒でRocqワーカーが
SIGSEGVになった。64 MiBスタック・並列数1でも発生したため、単に並列実行
だけが原因とは言えない。証明内容を変えずにスタック条件の影響を調べるため、
次の`sweep-no-vec-axioms-05`は同じソースに対し、子プロセスのスタック上限
だけを256 MiB (`ulimit -s 262144`)へ増やして実行する。
必要なら、証明済みの恒等規則をVec向けに局所的に具体化して、汎用ADTの
不要な展開を避ける方法も検討する。

### ビルド記録: sweep-no-vec-axioms-05

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 170.58秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(268435456, 268435456)`
- 詳細ログ: `/tmp/rr-sweep-sweep-no-vec-axioms-05.log`

```text
Entering directory '/home/mikam/RefinedRust'
File "hinata_mikami/gc/output/gc/proofs/dune", lines 2-7, characters 0-1236:
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (got signal SEGV)
Did 97 steps.
Did 2145 steps.
Did 1124 steps.
Did 90 steps.
Did 2419 steps.
Did 92 steps.
Did 1027 steps.
Leaving directory '/home/mikam/RefinedRust'
```

### ビルド記録: sweep-no-vec-axioms-06

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、実時間: 183.40秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(268435456, -1)`
- 詳細ログ: `/tmp/rr-sweep-sweep-no-vec-axioms-06.log`

```text
Entering directory '/home/mikam/RefinedRust'
        rocq hinata_mikami/gc/output/gc/proofs/.refinedrust.examples.gc.theory.d
File "hinata_mikami/gc/output/gc/proofs/dune", lines 2-7, characters 0-1236:
2 | (rocq.theory
3 | (flags -w -notation-overridden -w -redundant-canonical-projection)
4 | (name refinedrust.examples.gc.proofs)
5 | (modules proof_Node_set_next proof_Heap_mark_one proof_Node_set_marked proof_Heap_new proof_Heap_mark proof_make_node proof_Heap_mark_from proof_Heap_sweep proof_read_next_value proof_Heap_alloc)
6 | (generate_project_file)
7 | (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib hinata_mikami.extra_proofs.gc rrstd.alloc.alloc.generated rrstd.alloc.theories rrstd.alloc.vec.generated rrstd.arithops.arithops.generated rrstd.boxed.boxed.generated rrstd.clone.clone.generated rrstd.closures.closures.generated rrstd.cmp.cmp.generated rrstd.cmp.theories rrstd.controlflow.controlflow.generated rrstd.index.index.generated rrstd.iterator.iterator.generated rrstd.iterator.theories rrstd.mem.mem.generated rrstd.mem.theories rrstd.num.num.generated rrstd.option.option.generated rrstd.ptr.ptr.generated rrstd.ptr.theories rrstd.ptr_advanced.ptr_advanced.generated rrstd.range.range.generated rrstd.result.result.generated rrstd.result.theories rrstd.rr_internal.rr_internal.generated rrstd.rr_internal.theories rrstd.sized.sized.generated rrstd.stdlib.stdlib.generated refinedrust.examples.gc.generated))
        rocq hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.{glob,vo} (got signal SEGV)
Did 97 steps.
Did 2145 steps.
Did 1124 steps.
Did 90 steps.
Did 2419 steps.
Did 92 steps.
Did 1026 steps.
Leaving directory '/home/mikam/RefinedRust'
```

256 MiBでもSIGSEGVとなったため、`resolve_ghost_Vec_concrete`を局所補題として
追加した。これは`resolve_ghost_ofty_default`を直接適用するだけの証明で、
同じ`resolve_ghost`判断に対して参照値を変えずに継続へ渡す。既存の未証明補題
を再利用するものではない。この規則を局所インスタンスとして優先する。
それでも`sweep-no-vec-axioms-06`は183.40秒でSIGSEGVとなった。

次の試行では`Time Qed.`で証明を閉じる段階を計測し、`ulimit -S -s unlimited`
でsoftスタック上限のみを無制限にした。`/proc`から実際のRocqワーカーにも
無制限の上限が伝わっていることを確認した。実行中のRSSも取得して、
タクティクの失敗・コンパイラの異常終了・実行資源の問題を区別して調べる。
標準ライブラリやRocq本体、opamパッケージの変更・再インストールは行わない。

Dropについて追加確認すると、`register_drop_shim_for`自体もTODOの実装であり、
`DropE`の表示は`AnnotExpr 0 DropAnnot`である。実際の解放イベントの検証には、
単にsweepの手動証明を完成させる以上の、Dropの翻訳・意味論・仕様の対応が
必要になる。この点は証明の成功とは別の保証の限界として残す。

### ビルド記録: sweep-no-vec-axioms-07

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 0、実時間: 254.59秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(-1, -1)`
- 子プロセスの最大RSS: 4024216 KiB
- 詳細ログ: `/tmp/rr-sweep-sweep-no-vec-axioms-07.log`

### ビルド記録: verified-aux

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、実時間: 0.31秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(-1, -1)`
- 子プロセスの最大RSS: 46024 KiB
- 詳細ログ: `/tmp/rr-sweep-verified-aux.log`

### ビルド記録: verified-gc

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、実時間: 0.41秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(-1, -1)`
- 子プロセスの最大RSS: 88476 KiB
- 詳細ログ: `/tmp/rr-sweep-verified-gc.log`

### ビルド記録: verified-assumptions

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `/usr/bin/python3 -B /tmp/rr-sweep-assumptions.py`
- 終了コード: 0、実時間: 24.17秒
- プロセスのスタック上限（soft, hard、byte単位。-1は無制限）: `(-1, -1)`
- 子プロセスの最大RSS: 1956584 KiB
- 詳細ログ: `/tmp/rr-sweep-verified-assumptions.log`
