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


## 2026-10-23：公式最新版への移行開始

ユーザーの指示により RR 本体と依存環境の更新を実行する。公式 main はネットワーク経由で再確認し、`fd52421ed8cdada51bb911f69a7287ab2b3ac73d`（2026-10-12）だった。作業開始時の HEAD は `ce336481289897f353ff55ce6374dd97bbffbfa4`。未コミット変更は `gc/src/main.rs` のコメント変更のみ。

更新前の全追跡ソース、hinata_mikami・stdlib の作業ツリー、未コミット差分、無視対象 dune-project、opam 9.1 switch の export、旧フロントエンドバイナリを `/tmp/refinedrust-upgrade-backup-20261023` に退避した。旧 switch `refinedrust-rocq91` と旧 nightly は保持する。専用ブランチ `codex/refinedrust-20261023` で公式 main を統合し、ローカルの統合コミットは `b15cbf2f`。旧サンプル等の競合48ファイルは各ステージと作業内容を退避し、対象を個別指定して公式最新版へ解決した。GC の手動証明には競合がなかった。

新環境は nightly-2026-08-28、Rocq core 9.2.0、stdlib 9.1.0、Equations 1.3.2+9.2、および公式 manifest に固定された Iris/stdpp 等を使用する。opam switch は `refinedrust-rocq92-upgrade` として別に作成する。

最新版は MIR Drop terminator を drop glue の Call に翻訳する。一方、Box Drop や allocator、Vec 等には only_spec / trust_me が残る。ビルド成功と Rust 標準ライブラリの実装検証・実際の全解放の証明は区別して監査する。

既存の補助補題・関数証明の imports と手書き dune の依存名を caesium から radium に移行した。生成ファイルを直接編集して証明義務を消すことはしない。collect は変更しない。

### 更新ビルド generate-stdlib (2026-10-23T03:22:38)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `make generate_stdlib`
- 終了コード: 2、所要時間: 0.3秒
- 詳細ログ: `/tmp/refinedrust-upgrade-generate-stdlib.log`

### 更新ビルド generate-stdlib-02 (2026-10-23T03:23:40)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `make generate_stdlib`
- 終了コード: 2、所要時間: 0.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-generate-stdlib-02.log`

### 更新ビルド generate-stdlib-03 (2026-10-23T03:24:20)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `make generate_stdlib`
- 終了コード: 2、所要時間: 19.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-generate-stdlib-03.log`

### 更新ビルド generate-stdlib-04 (2026-10-23T03:24:53)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `make generate_stdlib`
- 終了コード: 0、所要時間: 11.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-generate-stdlib-04.log`

### 更新ビルド generate-gc-01 (2026-10-23T03:25:11)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo refinedrust -- --locked --offline`
- 終了コード: 0、所要時間: 0.3秒
- 詳細ログ: `/tmp/refinedrust-upgrade-generate-gc-01.log`

### 環境構築と仕様の再生成

- `/usr/bin/rustup toolchain install nightly-2026-08-28 --profile minimal --component rustc-dev --component llvm-tools-preview` は成功。
- `rr_frontend` で `./refinedrust build --locked` は依存取得のネットワーク制限を解除した再試行で成功（1分45秒）。`./refinedrust install` も成功し、退避済みの旧インストールを最新版に更新した。バージョン表示は nightly-2026-08-28 / b15cbf2f。
- `make generate_stdlib` の初回は `missing field assoc_tys` で失敗。バイナリを新版へ統一しても再現し、`stdlib/*/target/verify` の旧 rrlib が再帰検索されることが原因と判明。12ディレクトリを削除せずバックアップへ移動した。
- その後の stdlib 再生成は spin の依存取得でネットワーク制限に当たり、接続を許可した再試行で成功（11.1秒）。公式ライブラリの linking requirements は有効。
- GC 側も `find_stdlib=false` にしてこの作業ツリーの stdlib を明示使用し、`generate_linking_requirements=true` を設定した。`generate_dune_project=false` として既存の研究用 Dune 構成を保持する。
- GC で `cargo refinedrust -- --locked --offline` は成功（0.3秒）。生成された sweep の `_bb10` は `CallS drop_glue_Box_Node_std_alloc_Global_loc ... None` を含む。旧版の Drop 欠落はこの経路では解消している。
- opam 新 switch の OCaml 4.14.2+flambda は導入成功。依存導入の ppxlib ネイティブコンパイルで `Command got signal SEGV` を検出した。まずスタック上限を解除した再試行で切り分ける。GC 証明の不成立とは別の事象。
- 新 RR の `prove_with_subtype` には累積資源 `Acc` が追加されているため、既存の補助補題と呼び出しを資源を保持する形へ移植中。

### 更新ビルド generate-ptr-advanced-05 (2026-10-23T03:30:04)

- 実行場所: `/home/mikam/RefinedRust/stdlib/ptr_advanced`
- コマンド: `cargo refinedrust -- --locked --offline`
- 終了コード: 0、所要時間: 0.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-generate-ptr-advanced-05.log`

### 更新ビルド index-probe (2026-10-23T03:33:01)

- 実行場所: `/tmp/refinedrust-upgrade-index-probe`
- コマンド: `cargo refinedrust -- --offline`
- 終了コード: 101、所要時間: 0.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-index-probe.log`

### Vec のインデックス実装の再確認

`/tmp/refinedrust-upgrade-index-probe` に既存 vec_index と同じ仕様・本体を置き、only_spec を付けず `skip_unsupported_features=false` で `cargo refinedrust -- --offline` を実行した。結果は終了コード101。`core::slice::index::SliceIndex` の trait impl が未登録という翻訳エラーになった（`/tmp/refinedrust-upgrade-index-probe.log`）。したがって、この公式最新コミットと指定 nightly の組合せでは wrapper の本体検証は依然通らない。既存 wrapper の only_spec は保持し、その仕様と実装の対応は信頼境界として報告する。失敗した probe は研究ソースには追加していない。

更新前バックアップは一時領域に加え `/home/mikam/RefinedRust-backups/20261023` に永続保存した。新公式から消えた Unique::empty の旧ローカル証明と旧テンプレートも退避し、現行 stdlib のビルド対象に混入させない。

### 更新ビルド versions (2026-10-23T03:34:32)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `rustc --version; cargo refinedrust --version; dune --version; rocq --version`
- 終了コード: 0、所要時間: 0.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-versions.log`

### 依存ライブラリでの SIGSEGV の切り分け

初回 opam 導入（終了31）は ppxlib のネイティブコンパイルと Stdlib `QArith/Qpower.vo` の Rocq コンパイルで SIGSEGV。`ulimit -S -s unlimited` を設定した再試行では ppxlib と Elpi は成功したが、Stdlib `ZArith/Zdiv.vo` が終了139となった（`/tmp/refinedrust-upgrade-opam-install-unlimited-stack.log`）。したがって、現時点でスタック制限だけが唯一の原因とは断定できない。

失敗した Stdlib のビルドディレクトリで、`ulimit -S -s unlimited; opam exec --switch=refinedrust-rocq92-upgrade -- /bin/sh -c 'ulimit -S -s; rocq --version; make -j1 ZArith/Zdiv.vo'` を実行すると成功した。これは Rocq の証明を飛ばす実行ではなく通常の .vo コンパイルである。続けて `opam install --jobs=1 --reuse-build-dir` により並列数を下げ、成功した成果を再利用する。

### Stdlib ビルドの並列数指定に関する追加調査

Stdlib のトップレベル Makefile は `+$(MAKE) -j -C theories $@` を実行するため、`opam --jobs=1` だけでは内部の Rocq コンパイルは直列にならないことが判明した。内部 Makefile は `ROCQMAKEOPTIONS` を受け付けるので、厳密に制限する場合は `ROCQMAKEOPTIONS=-j1` も指定する。実行中の rocqworker の `/proc/<pid>/limits` から、スタックの soft/hard limit がともに unlimited であることも確認した。

3回目（`--jobs=1 --reuse-build-dir`）の再試行で rocq-stdlib 9.1.0 の導入は成功し、Equations 1.3.2+9.2 の導入も成功した。これだけをもって SIGSEGV の単一の原因が確定したとは扱わない。

### 新 opam 環境の導入完了

3回目の opam 導入が終了コード0で完了した。指定された Rocq core 9.2.0 / stdlib 9.1.0 / Equations 1.3.2+9.2 / stdpp / Iris / iris-contrib / lifetime-logic の全パッケージが揃った。`_opam` のシンボリックリンクを新 switch へ切り替えた。旧 switch と旧 toolchain は残っている。

新しい検査が旧 .vo や旧バイナリキャッシュに依存しないように、従来の `_build` とルート `.lia.cache` をバックアップへ移動し、空のビルド状態から検査する。GC `main.rs` は作業開始時の未コミットコメントを含め、一字一句保持されていることをバックアップと照合した。

### 更新ビルド generate-gc-strict (2026-10-23T03:54:35)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo refinedrust -- --locked --offline`
- 終了コード: 0、所要時間: 0.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-generate-gc-strict.log`

### 未対応機能の黙示スキップを禁止した生成

GC の `RefinedRust.toml` に `skip_unsupported_features=false` を設定して再生成し、終了0を確認した。翻訳できない検証対象関数を黙って除外して成功扱いにすることを避けるためであり、仕様を弱める変更ではない。既存の vec_index の明示的 only_spec は保持される。

### 更新ビルド effective-config (2026-10-23T04:02:03)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo refinedrust --show-config`
- 終了コード: 0、所要時間: 0.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-effective-config.log`

### 更新ビルド aux-direct-01 (2026-10-23T04:11:03)

- 実行場所: `/tmp/refinedrust-gc-aux92`
- コマンド: `rocq compile -w -notation-overridden -Q /home/mikam/RefinedRust/_build/default/theories/refinedrust/lithium lithium -Q /home/mikam/RefinedRust/_build/default/theories/refinedrust/radium radium -Q /home/mikam/RefinedRust/_build/default/theories/refinedrust/rust_typing refinedrust -Q . hinata_mikami.extra_proofs.gc gc_defs.v && rocq compile -w -notation-overridden -Q /home/mikam/RefinedRust/_build/default/theories/refinedrust/lithium lithium -Q /home/mikam/RefinedRust/_build/default/theories/refinedrust/radium radium -Q /home/mikam/RefinedRust/_build/default/theories/refinedrust/rust_typing refinedrust -Q . hinata_mikami.extra_proofs.gc heap_lemmas.v`
- 終了コード: 0、所要時間: 8.9秒
- 詳細ログ: `/tmp/refinedrust-upgrade-aux-direct-01.log`

### 更新ビルド typesystem-01 (2026-10-23T04:22:21)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `dune build -j 2 --display=short theories/refinedrust`
- 終了コード: 0、所要時間: 1881.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-typesystem-01.log`

### 更新ビルド aux-dune-01 (2026-10-23T04:24:02)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、所要時間: 6.3秒
- 詳細ログ: `/tmp/refinedrust-upgrade-aux-dune-01.log`

### 更新ビルド gc-dune-01 (2026-10-23T04:32:31)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 512.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-dune-01.log`

### 更新ビルド ptr-gdb (2026-10-23T04:39:45)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-debug-ptr.py`
- 終了コード: 1、所要時間: 254.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-ptr-gdb.log`

### 更新ビルド stack-probe (2026-10-23T04:40:49)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `/bin/sh -c "ulimit -S -s"; /bin/bash -c "ulimit -S -s"; opam exec -- /bin/sh -c "ulimit -S -s"`
- 終了コード: 0、所要時間: 0.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-stack-probe.log`

### RR 本体・補助補題の新カーネル検査

`dune build -j2 theories/refinedrust` は終了0、1881.8秒で成功した。最後の shims の汎用 tuple drop glue の検査だけでも長時間を要したが、CPU使用率とメモリ使用量を確認して待ち、証明省略なしで完了した。補助補題は一時ディレクトリでの直接 `rocq compile`（8.9秒）と、本来のディレクトリでの `dune build -j1`（6.3秒）の両方で成功した。

### 新版の ptr 仕様での SIGSEGV

初回の GC `dune build -j1` は512.4秒で終了1。GC の手動証明に到達する前に、stdlib ptr の `generated_specs_ptr.v` が signal SEGV となった。64変種 AlignmentEnum の証明を含むファイルであり、観測時に単一 rocqworker の RSS は6,802,076 KiBまで増えた。

システムへのインストールは行わず、Ubuntu のパッケージから gdb と必要な共有ライブラリを /tmp に展開して診断した。生成ソースは変更せず、同じファイルを `-time` と gdb 下で単独検査すると約254秒で inferior は正常終了した。`solve_mk_enum_tag_inj_roundtrip` に約86秒かかることを確認した。診断スクリプトの終了1は、正常終了した inferior に対して後続の `info registers` が失敗したためであり、Rocq の証明失敗ではない。詳細は `/tmp/refinedrust-upgrade-ptr-gdb.log`。

通常 Dune の再試行でも ptr の .vo コンパイルが成功した。実際の Dune 子 rocqworker について stack の soft/hard limit がともに unlimited であることも確認した。この再発はスタック上限の解除だけでは説明できず、根本原因は未確定。最新版に更新しただけで SIGSEGV が完全に直ったとは主張しない。生成コード・義務を削除する回避は行っていない。

### 更新ビルド gc-dune-02 (2026-10-23T04:48:22)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 460.9秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-dune-02.log`

### 更新ビルド regenerate-gc-field (2026-10-23T04:50:25)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo refinedrust -- --locked --offline`
- 終了コード: 0、所要時間: 1.0秒
- 詳細ログ: `/tmp/refinedrust-upgrade-regenerate-gc-field.log`

### 更新ビルド gc-dune-03 (2026-10-23T04:50:29)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 3.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-dune-03.log`

### 更新ビルド rfn-probe (2026-10-23T04:52:57)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-rfn-probe.py`
- 終了コード: 0、所要時間: 2.9秒
- 詳細ログ: `/tmp/refinedrust-upgrade-rfn-probe.log`

### 更新ビルド rfn-probe-02 (2026-10-23T04:54:20)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-rfn-probe.py`
- 終了コード: 0、所要時間: 2.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-rfn-probe-02.log`

### 更新ビルド rfn-probe-03 (2026-10-23T04:55:29)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-rfn-probe.py`
- 終了コード: 0、所要時間: 2.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-rfn-probe-03.log`

### 更新ビルド gc-dune-04 (2026-10-23T05:01:43)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 309.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-dune-04.log`

### 更新ビルド debug-drop (2026-10-23T05:05:54)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py drop`
- 終了コード: 0、所要時間: 15.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-drop.log`

### 更新ビルド debug-mark-from (2026-10-23T05:06:17)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py mark_from`
- 終了コード: 0、所要時間: 38.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-mark-from.log`

### 更新ビルド debug-sweep-exit (2026-10-23T05:07:21)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py sweep`
- 終了コード: 0、所要時間: 103.0秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-sweep-exit.log`

### 更新ビルド debug-drop-unshelve (2026-10-23T05:13:11)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py drop 'Unshelve. all: try done. rep <-! liRStep; liShow. Close Scope rr_hidden.'`
- 終了コード: 0、所要時間: 13.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-drop-unshelve.log`

### 更新ビルド debug-drop-unit (2026-10-23T05:16:01)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py drop 'iApply type_val. iApply type_val_unit. rep <-! liRStep; liShow. Close Scope rr_hidden.'`
- 終了コード: 0、所要時間: 14.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-drop-unit.log`

### 更新ビルド debug-drop-guards (2026-10-23T05:20:03)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py drop 'apply_update updateable_strip_guards. iApply type_val. iApply type_val_unit. rep <-! liRStep; liShow. Close Scope rr_hidden.'`
- 終了コード: 0、所要時間: 13.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-drop-guards.log`

### 更新ビルド debug-drop-nodes (2026-10-23T05:24:35)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py drop @/tmp/refinedrust-drop-body.v`
- 終了コード: 0、所要時間: 16.9秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-drop-nodes.log`

### 更新ビルド debug-drop-nodes-02 (2026-10-23T12:25:20)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py drop @/tmp/refinedrust-drop-body.v`
- 終了コード: 0、所要時間: 21.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-drop-nodes-02.log`

### 更新ビルド gc-dune-05 (2026-10-23T12:25:24)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 130、所要時間: 26186.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-dune-05.log`

### 更新ビルド debug-drop-nodes-03 (2026-10-23T12:27:02)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py drop @/tmp/refinedrust-drop-body.v`
- 終了コード: 0、所要時間: 23.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-drop-nodes-03.log`

### 更新ビルド debug-mark-from-02 (2026-10-23T12:28:04)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py mark_from "Close Scope rr_hidden."`
- 終了コード: 0、所要時間: 124.5秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-mark-from-02.log`

### 更新ビルド drop-check-01 (2026-10-23T12:28:26)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-check.py proof_drop_glue_Heap`
- 終了コード: 1、所要時間: 21.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-check-01.log`

### 更新ビルド debug-mark-before (2026-10-23T12:28:44)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py mark_before "Close Scope rr_hidden."`
- 終了コード: 0、所要時間: 61.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-mark-before.log`

### 更新ビルド drop-check-02 (2026-10-23T12:30:02)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-check.py proof_drop_glue_Heap`
- 終了コード: 1、所要時間: 21.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-check-02.log`

### 更新ビルド drop-check-03 (2026-10-23T12:31:11)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-check.py proof_drop_glue_Heap`
- 終了コード: 0、所要時間: 31.0秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-check-03.log`

### 更新ビルド debug-mark-restore (2026-10-23T12:31:24)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py mark_before @/tmp/refinedrust-mark-restore.v`
- 終了コード: 0、所要時間: 58.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-mark-restore.log`

### 2026-10-23 続行時の証明診断

- `gc-dune-05` の `Heap_mark_proof` は `.vo` を生成済み。長時間実行中だったのは `Heap_mark_from_proof` で、約7時間 CPU を使い続けていたため SIGINT により今回のチェックを中断した。未検証のまま成功とは扱わない。
- 新しく利用可能となった `.agents/skills/refinedrust-{verification,specifications,proofs}/SKILL.md` を読んだ。proofs skill が指定する `ben-mcp_rocq_*` ツールは現在のツール一覧に存在しないため、同じ Rocq 9.2 の対話実行で代替する。
- `mark_from` の既マーク分岐では、新版の `prove_with_subtype_stratify` がノード所有権を前提とする含意を生成する。これを処理せず big-separation アクセサ補題を適用すると、巨大な継続を含む単一化が長時間続く。所有権の再構成を明示する方針へ切り替えた。
- `gc-alloc-06` で `Heap_alloc_proof` と `Heap_mark_one_proof` の Dune コンパイルが通った。sweep は続けて検査中。
- 新規 `drop_glue_Heap` は、guarded な各ノード所有権の later を、保持されている正規の later credit によって外し、生成された ghost-drop 条件へ渡す。未解決条件の削除や仮定の追加は行わない。

### 更新ビルド gc-alloc-06 (2026-10-23T12:31:54)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `dune build -j 1 --display=short hinata_mikami/gc/output/gc/proofs/proof_Heap_alloc.vo hinata_mikami/gc/output/gc/proofs/proof_Heap_mark_one.vo hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.vo`
- 終了コード: 1、所要時間: 301.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-alloc-06.log`

### 更新ビルド mark-from-check-01 (2026-10-23T12:33:48)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-check.py proof_Heap_mark_from`
- 終了コード: 1、所要時間: 76.0秒
- 詳細ログ: `/tmp/refinedrust-upgrade-mark-from-check-01.log`

### 更新ビルド assumptions-partial (2026-10-23T12:36:13)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-upgrade-assumptions.py gc_defs heap_lemmas proof_Heap_alloc proof_Heap_mark proof_Heap_mark_one proof_Heap_new proof_Node_set_marked proof_Node_set_next proof_make_node proof_read_next_value`
- 終了コード: 0、所要時間: 166.9秒
- 詳細ログ: `/tmp/refinedrust-upgrade-assumptions-partial.log`

### 更新ビルド gc-sweep-drop-07 (2026-10-23T12:36:47)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `dune build -j 1 --display=short hinata_mikami/gc/output/gc/proofs/proof_Heap_sweep.vo hinata_mikami/gc/output/gc/proofs/proof_drop_glue_Heap.vo`
- 終了コード: 1、所要時間: 224.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-sweep-drop-07.log`

### 更新ビルド mark-from-check-02 (2026-10-23T12:37:15)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-check.py proof_Heap_mark_from`
- 終了コード: 0、所要時間: 174.8秒
- 詳細ログ: `/tmp/refinedrust-upgrade-mark-from-check-02.log`

### 更新ビルド debug-sweep-side (2026-10-23T12:38:58)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py sweep_side "Close Scope rr_hidden."`
- 終了コード: 0、所要時間: 98.9秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-sweep-side.log`

### 2026-10-23 証明と信頼境界の監査（継続中）

`assumptions-partial` で補助35補題と GC 8関数の `Print Assumptions` を実行した。補助補題は global context に対して閉じていた。`alloc`, `mark`, `mark_one`, `new` は上流 `generated_specs_vec.resolve_ghost_Vec_T_owned`（`stdlib/vec/extra_specs.v` の Admitted）に依存していた。この依存を残さないよう、sweep と同じく未証明の Vec resolver hints をローカルで外し、証明済み `resolve_ghost_ofty_default` による具体的 refinement 用ルールへ切り替えた。`mark_from` にも適用し、全対象を再チェック中。上流の Admitted を新たに利用する回避はしない。

`mark-from-check-02` は全分岐・副条件と `Qed` を通常の Rocq コンパイルで完了した（174.8秒）。以後の resolver 変更も含めた Dune 全体確認を実施する。`drop_glue_Heap` も Dune で通常の .vo を生成済み。

更新前の作業ツリーを含む tar と `gc/src/main.rs` を比較した結果、Rust の差分は `Heap.all_nodes` の `#[rr::field("<#> locs")]` を `#[rr::field("#(<#> locs)")]` にする1行だけだった。ユーザーのコメント変更、実行本体、collect、vec_index wrapper、sweep の事後条件は保持した。

`source /home/mikam/RefinedRust/hinata_mikami/gc/activate.sh` の後の実測は rustc 1.100.0-nightly (2026-08-27)、cargo 1.100.0-nightly、Rocq 9.2 / OCaml 4.14.2、Dune 3.23.1、switch refinedrust-rocq92-upgrade、soft stack unlimited。

### 更新ビルド debug-sweep-side-02 (2026-10-23T12:42:24)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py sweep_side "Close Scope rr_hidden."`
- 終了コード: 0、所要時間: 178.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-debug-sweep-side-02.log`

### 更新ビルド gc-dune-08 (2026-10-23T12:46:44)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 532.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-dune-08.log`

### 2026-10-23 最新版で確認した適用範囲と残存する信頼境界

1. 旧 MIR Drop 翻訳の欠落は最新版では解消されている。`rr_frontend/translation/src/body/function_translation/terminator.rs` の Drop 分岐は `needs_drop_raw` を調べ、drop glue の場所を登録し、通常継続と unwind 継続を持つ `Stmt::Call` を構築する。GC の `generated_code_gc.v` の `Heap_sweep_def`、`_bb10` に `CallS drop_glue_Box_Node_std_alloc_Global_loc` が実在する。古い `_drope` を捨てる実装に対する説明を、そのまま新版へ当てはめない。
2. `only_spec` は廃止されていない。`stdlib/boxed/src/lib.rs` の `impl Drop for Box<T,A>` は今も `#[rr::only_spec]`。解放処理の Rust 本体はあるが、その本体の検証をこの設定では生成しない。Vec/RawVec 等にも only_spec / trust_me が残る。呼び出し元の型付け定理が通ることと、全ライブラリの Rust 実装まで証明済みであることを区別する。
3. ユーザーの `wrappers::vec_index` も引き続き only_spec として保持している。削除した一時 probe は strict unsupported=false で `core::slice::index::SliceIndex` の trait impl 登録エラーとなった（index-probe ログ）。この実験は本体の wrapper を変更していない。
4. 現在の定理は、各関数の事前条件と呼び出し先の仕様を前提とする Radium/Iris の関数型付け定理である。`generate_linking_requirements=true` で linking 条件も生成したが、whole-program の linking/adequacy 定理、Rust 全体の意味との接続、終了性、解放イベントの回数を数える定理は本研究の既存証明にはない。`Print Assumptions` だけでは only_spec 呼び出し先への依存は検出できない（呼び出し先の仕様は定理の前提に現れる）。
5. sweep の既存の事後条件は維持している。マーク済みノードの順序・value・next の保持、marked=false、未マークノードの Vec からの除去、残存ノードの所有権/freeable、NoDup・非NULL・長さ・next の有効性が対象。実際の allocator による解放の完了まで無条件に証明した、という主張はしない。
6. collect は当初の指示通り未検証・未変更。現在の mark は先頭1ノードを根とする等の事前条件を持つ。任意のルート集合や collect 全体の正当性へは自動的には一般化しない。Heap を最後に drop する際の生存ノードの漏れなしも主張しない。
7. SIGSEGV はアップデート後にも依存導入と ptr 仕様のチェックで発生した。通常の再実行で通ったが原因は未確定であり、「更新だけで完治した」とは扱わない。生成された義務を削除したり、admit フラグを使ったりしていない。

### 更新ビルド sweep-check-08 (2026-10-23T12:47:34)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-check.py proof_Heap_sweep`
- 終了コード: 0、所要時間: 278.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-check-08.log`

### 2026-10-23 最終ソースでの sweep 証明チェック

`sweep-check-08` は通常の `rocq compile` によって `Time Qed` まで成功した。全体278.6秒、最後の kernel check は104.3秒。残っていた整数範囲0/1の副条件は `elem_of_int_type_0_to_127` で証明した。`Admitted`、新しい公理、義務の削除、事後条件の弱化はない。

`gc-dune-08` では Vec の未証明 resolver を外した alloc・mark・mark_from・mark_one・new が全て .vo を生成した。この Dune 実行は開始時に取った古い sweep ソース（最終0/1補題の追加前）をチェックしたため、sweep の既知の範囲義務で終了1となった。元ソースと `_build/default/.../proof_Heap_sweep.v` の差を確認した。次の最終 Dune 実行で最新のソースを取り込む。

ユーザー向けの `activate.sh` を source する実際の Bash 環境で、`cargo refinedrust -- --locked --offline` が終了0（cargo 表示0.75秒）だった。ログは `/tmp/refinedrust-upgrade-gc-final-generate.log`。SliceIndex/Zip 等の shim 登録警告は上流と現在の nightly の対応に関するもの。strict unsupported=false で対象関数の翻訳は成功しており、出力 proof modules と Drop 呼び出しを併せて監査する。

### 2026-10-23 ユーザー向け通常コマンドの最終成功

`activate.sh` を source した Bash で、次を順番に実行し、両方とも終了コード0だった。

```bash
cd /home/mikam/RefinedRust/hinata_mikami/gc
source ./activate.sh
cargo refinedrust -- --locked --offline
dune build
```

- cargo ログ: `/tmp/refinedrust-upgrade-gc-final-generate.log`
- Dune ログ: `/tmp/refinedrust-upgrade-gc-final-dune.log`
- Dune は12:49開始・12:53終了。`Heap_sweep_proof` の最後の kernel check は100.876秒、通常の `.vo` は約10MB。`-vos`、admit、義務の削除による短縮は行っていない。
- GC persistent proof modules 全12（既存10関数 + 新規 Heap drop glue + その subsumption）をチェック済み。補助35補題も通常の Dune でチェック済み。
- 証明を使い回せる新しい環境を `activate.sh`、`rust-toolchain.toml`、`opam-rocq92.export`、root Dune project の控え `dune-project.root` に記録した。
- この最終実行では SIGSEGV は発生していない。過去の更新作業中の再発と根本原因が未確定である事実は別途保持する。

### 更新ビルド assumptions-final (2026-10-23T12:57:52)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-upgrade-assumptions.py`
- 終了コード: 0、所要時間: 198.5秒
- 詳細ログ: `/tmp/refinedrust-upgrade-assumptions-final.log`

### 更新ビルド gc-dune-drop-final (2026-10-23T12:59:16)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、所要時間: 23.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-gc-dune-drop-final.log`

### 更新ビルド assumptions-drop-final (2026-10-23T13:00:10)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-upgrade-assumptions.py proof_drop_glue_Heap`
- 終了コード: 0、所要時間: 20.5秒
- 詳細ログ: `/tmp/refinedrust-upgrade-assumptions-drop-final.log`

## 2026-10-23 更新作業の最終結果

- 公式 main `fd52421ed8cdada51bb911f69a7287ab2b3ac73d` を統合した `codex/refinedrust-20261023` 上で作業完了。統合コミット `b15cbf2f`。push は行っていない。
- 新環境: Rust nightly-2026-08-28、Rocq core 9.2.0 / Stdlib 9.1.0、OCaml 4.14.2+flambda、Dune 3.23.1、opam switch `refinedrust-rocq92-upgrade`。旧 switch・旧 nightly・旧フロントエンドのバックアップを保持。
- `cargo refinedrust -- --locked --offline` はユーザー向け activate.sh を source した環境で終了0。GC の通常 `dune build` も終了0。最後の drop-glue 修正後の全体 Dune も終了0（gc-dune-drop-final）。
- 既存10関数の証明、新規 Heap drop glue、その仕様 subsumption の計12モジュール、および補助35補題が通常の .vo 生成で成功した。sweep の既存の事後条件は弱めていない。
- 47件の `Print Assumptions` の監査では、最後に `drop_glue_Heap_proof` のみに未証明 Vec resolver 依存を検出した。この proof にもローカルで証明済み generic resolver を適用し、Dune（23.4秒）と当該定理の `Print Assumptions`（20.5秒）を再実行して依存を除去した。他の46件は変更していない。
- 最終的に、補助35補題は global context に対して閉じ、GC12定理の公理は `FunctionalExtensionality.functional_extensionality_dep` と `ProofIrrelevance.proof_irrelevance` のみ。新規の公理・Admitted・admit・義務を消す ignore は追加していない。上流 Vec の2つの Admitted 自体は変更していないが、この GC の定理はそれらに依存しない。
- 監査の定理別結果とソース SHA256 は `verification_assumptions_20261023.txt`。47件の生ログと Drop 修正後の生ログは元の検出結果も含めて保持する。
- Rust 作業ツリーの差分は既存コメント変更を保持したうえで Heap field annotation の1行のみ（`<#> locs` → `#(<#> locs)`）。Rust の本体・sweep の事前/事後条件・vec_index wrapper・collect は元の作業ツリーと同一であることを tar との比較で確認した。
- 実際の Drop 呼び出しを落とす旧フロントエンドの問題は新版では解消。Git 履歴では初期対応 `033fc28a`（2026-05-25, feature: initial handling for drop glue calls）があり、その後 unwind 対応も進んでいる。ただし Box::drop 等は現在も only_spec であり、呼び出し先仕様を前提とする関数型付けと、実装全体の解放イベントまで含む無条件の完全証明は区別する。collect、whole-program linking/adequacy、終了性、全体の漏れなしは未検証。
- 更新作業中の SIGSEGV 再発は記録通り。最終ビルドは stack unlimited・DUNE_JOBS=1 で成功したが、根本原因の特定・完治を主張しない。
- 更新前のソースと環境は `/home/mikam/RefinedRust-backups/20261023` に保持。更新後のソースと実行ログも同ディレクトリの `post-upgrade` に保存する。

再実行コマンド:

```bash
cd /home/mikam/RefinedRust/hinata_mikami/gc
source ./activate.sh
cargo refinedrust -- --locked --offline
dune build
```

ルートの dune-project は研究用 package を保持した既存ファイルを使う。控えは `gc/dune-project.root`。root Makefile の setup-dune で研究用 package を上書きしないこと。

## 2026-10-23 sweep の仕様強化と教授コメントへの対応（開始）

- 更新済みの通過済み証明を `/tmp/refinedrust-sweep-contract-backup-20261023` に保存した。既存の未コミット変更は保持する。
- 方針: 保持対象と破棄対象の厳密な分割、保持 iff 開始時 marked、mark の完全性を仮定した保持 iff reachable、ノードのアドレスを使った到達可能性の保存を証明する。既存の sweep の事前条件は marks_closed であり、任意の過剰マークを許すため、保持 iff reachable は mark の結果を使う条件付き結論とする。
- sweep は marked を false にリセットするため「物理的な mark ビットが不変」は仕様と矛盾する。代わりに、未処理部分の開始時マークの保存と、保持ノードの value/next・グラフ到達可能性の保存を扱う。削除後の添字の不変は主張しない。
- only_spec のライブラリ本体検証は今回の対象外。Drop については、独立に更新できるゴーストログだけで実行済みを主張せず、生成された Call と Radium の遷移に結び付く小さな検査から進める。
- RefinedRust verification/specifications/proofs skills を再確認した。指定の ben-mcp_rocq_* は現在も利用できないため、同じ Rocq の対話実行と通常コンパイルを用いる。

### 追加仕様の意味と適用範囲

- `extra_proofs/gc/sweep_contract.v` に `reachable_loc`（ノードの添字でなくアドレスを使う到達可能性）と `sweep_post` を追加した。
- `sweep_post` の第一項は「元のリストのノードが残る iff 開始時の mark が true」。第二項は「開始時に marked iff reachable が成立するなら、残る iff 開始時に reachable」。第三項は「root が marked なら、終了後のグラフと開始時のグラフの到達可能なアドレス集合が同じ」。到達可能性の保存はフィルタ後の異なる添字の間で証明しており、同じスナップショットを両辺に置いた自明な等式ではない。
- `sweep_fields_preserved` は、残った各レコードの value と next が元の同じアドレスのレコードと一致することを表す。実際のメモリとの対応は、既存の observe とノードの所有権に関する事後条件を保持して接続する。
- marks_closed は過剰な mark を許す。この事前条件だけで reachable iff 保持を無条件に主張するのは誤り。既存の事前条件を強めず、正確な mark を入力とする条件付き結論を追加した。`mark_sweep_exact` と `mark_sweep_reachability_preserved` により、既存の mark_from_rel の結論からその条件を導いた。collect 本体の検証は行わない。
- 元の物理的 mark が不変という要求は、sweep の false へのリセットと両立しない。`sweep_unprocessed_marks_unchanged` は未処理 prefix のみ開始時の mark と同じであることを示し、終了時には既存のメモリ事後条件に加えて `all_unmarked` を明記した。元の marks という数学的スナップショットと、変更されるメモリ上のビットを区別する。
- 保持集合と除去集合の完全な分割・排他性、逆順の未マーク対象列の重複なし・元の非到達ノードとの一致も証明した。`sweep_drop_targets` は対象候補列であり、実行済み Drop/Free の履歴ではない。

### Drop に関する小規模な接続検査

- `gc/output/gc/audit/drop_calls.v` の `observed_stmt_step` は元の Radium の `stmt_step` と一意の観測を組にしたもの。観測を消すと元の遷移に戻ること、元の各遷移に一意の観測が付くこと、Call 観測が実際の関数解決・callee frame への遷移を伴うことを証明した。独立したゴースト更新だけでイベントを発行するものではない。
- 同じファイルで生成済み `Heap_sweep_def` の静的な通常経路を検査した。未マーク分岐は remove/from_raw/Drop の3呼出、生存分岐は set_marked の1呼出。from_raw の返す Box のスロット `__20` が Drop に渡ることも検査した。
- Drop の基本ブロックを次のブロックへの jump に置き換えた変異では呼出数が2となり、3呼出の検査に反することを通常の Rocq の補題として証明した。生成ファイルは直接変更していない。
- ここで検査した CFG の通常経路は、callee の正常復帰を選ぶ静的射影であり、callee の本体や unwind、sweep の全実行を表す定理ではない。単一遷移の観測器と loop の Iris 型付けを結合した、全周回のイベント列の意味論的証明は未実装。したがって「各対象について実行済み Drop がちょうど1回」「Free が実行済み」という結論には格上げしない。
- Box::drop / allocator 等の only_spec の実装検証を今回の対象外とする方針は維持する。この点は Rust の sweep が間違っている、という意味ではない。

### 仕様追加作業の最終結果

- `main.rs` に `sweep_contract` の import と、sweep_post / sweep_fields_preserved / all_unmarked の ensures を追加した。既存の事前条件・所有権の事後条件は維持した。開始時の控えとの比較で、Rust の sweep / mark / collect 本体、gc_defs.v と heap_lemmas.v の既存内容が変わっていないことを確認した。
- 新しい `sweep_contract.v` の23件の補題・定理・例を通常コンパイルした。既存の mark の結論を使った正確な保持と到達可能性保存は、仕様の論理的な合成として証明した。collect の型付け証明は追加していない。
- 新しい `output/gc/audit/drop_calls.v` の9件の検査・補題を通常コンパイルした。選択済み node_ptr を from_raw の引数 __21 にコピーする代入も、生成コードそのものについて検査した。
- sweep の追加の純粋条件は sidecond_hammer_normalize により3条件へ分解されていた。元の sweep_post_filter の適用に加え、分解後の sweep_kept_exact / sweep_reachable_exact / sweep_reachability_preserved の各補題を適用して解決した。通常の Qed のカーネル検査は322.363秒かかったが完了した。
- 途中の sweep-contract-dune-02 は、audit から私有の GC.generated theory が見えない配置の問題で終了1だったが、sweep の .vo 自体は正常生成された。GC は output/dune-project 内の別プロジェクトなので、手書きの audit theory を同プロジェクトの output/gc/audit/ に移し、package 指定を外した。generated/ や生成 dune は手動編集していない。
- 最終の `cargo refinedrust -- --locked --offline`（sweep-contract-cargo-final、2.2秒）は終了0。再生成前後の SHA256 比較で、全手動 proof と Drop audit が保持されたことも確認した。
- 最終の `dune build -j 1 --display=short`（sweep-contract-dune-final、5.6秒）は終了0。補助・生成・GC証明・audit の29ソースについて、_build 内コピーとの一致と、通常 .vo の存在を確認した。-vos は使用していない。
- `audit/check_assumptions.py` で79件を監査した。初回は結果マーカーに使う文字列 scope の import 漏れを正しくエラーとして検出した。Print Assumptions 自体の結果は67件 closed + 12件の基盤公理だったが、集計を成功扱いにせず保存した。明示的な Stdlib Strings.String import を追加し、同じ RR import 後のマーカー動作を単独確認したうえで、全監査を再実行した。
- 最終の全監査（sweep-contract-assumptions-final-02、303.5秒）は終了0。補助58件と audit9件の計67件は Closed under the global context。GC12定理は `FunctionalExtensionality.functional_extensionality_dep` と `ProofIrrelevance.proof_irrelevance` のみ。未証明 Vec resolver 依存は0件。新規の公理・Admitted・admit・義務を消す ignore は追加していない。
- 定理別結果とソース SHA256 は `verification_assumptions_20261023.txt`、日本語の説明は `sweep_contract_report_20261023.txt`。新規作業の実行ログ・失敗した初回監査の出力・成功した最終監査の生出力・開始時の証明の控えは `audit/artifacts/20261023/` に保存する。Cargo が更新した追跡対象の target/.rustc_info.json は作業開始時と同じ HEAD の内容に戻した。
- 適用範囲: 追加した機能的事後条件の証明は完了。Drop 候補列の数学的性質、生成 CFG、単一遷移観測の検査も完了。候補列を全ループの実行済み Drop 列に結び付ける証明、物理 Free の実行、only_spec 本体、collect / whole-program linking・adequacy・終了性は今回の成果に含めない。

### 更新ビルド sweep-contract-01 (2026-10-23T14:07:43)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 6.0秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-01.log`

### 更新ビルド sweep-contract-02 (2026-10-23T14:08:06)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 3.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-02.log`

### 更新ビルド sweep-contract-03 (2026-10-23T14:09:26)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 4.9秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-03.log`

### 更新ビルド sweep-contract-04 (2026-10-23T14:10:58)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 4.7秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-04.log`

### 更新ビルド sweep-contract-05 (2026-10-23T14:11:37)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 3.5秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-05.log`

### 更新ビルド sweep-contract-06 (2026-10-23T14:11:59)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、所要時間: 3.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-06.log`

### 更新ビルド sweep-contract-07 (2026-10-23T14:13:28)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 7.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-07.log`

### 更新ビルド sweep-contract-08 (2026-10-23T14:16:28)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/extra_proofs/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、所要時間: 7.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-08.log`

### 更新ビルド sweep-contract-cargo (2026-10-23T14:17:24)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo refinedrust -- --locked --offline`
- 終了コード: 0、所要時間: 1.4秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-cargo.log`

### 更新ビルド drop-audit-01 (2026-10-23T14:21:32)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-check-source.py /home/mikam/RefinedRust/hinata_mikami/gc/audit/drop_calls.v`
- 終了コード: 1、所要時間: 4.5秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-audit-01.log`

### 更新ビルド drop-audit-02 (2026-10-23T14:21:56)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-check-source.py /home/mikam/RefinedRust/hinata_mikami/gc/audit/drop_calls.v`
- 終了コード: 1、所要時間: 6.0秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-audit-02.log`

### 更新ビルド drop-audit-03 (2026-10-23T14:22:40)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-check-source.py /home/mikam/RefinedRust/hinata_mikami/gc/audit/drop_calls.v`
- 終了コード: 0、所要時間: 4.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-audit-03.log`

### 更新ビルド audit-format (2026-10-23T14:30:09)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `rocq repl -quiet < /tmp/refinedrust-audit-format.input`
- 終了コード: 0、所要時間: 0.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-audit-format.log`

### 更新ビルド sweep-contract-dune-01 (2026-10-23T14:33:39)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 952.7秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-dune-01.log`

### 更新ビルド sweep-contract-debug-side (2026-10-23T14:35:41)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-proof-debug.py sweep_side`
- 終了コード: 0、所要時間: 171.3秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-debug-side.log`

### 更新ビルド drop-audit-final-local (2026-10-23T14:46:34)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-check-source.py /home/mikam/RefinedRust/hinata_mikami/gc/output/gc/audit/drop_calls.v`
- 終了コード: 1、所要時間: 12.7秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-audit-final-local.log`

### 更新ビルド sweep-contract-dune-02 (2026-10-23T14:47:16)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 1、所要時間: 653.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-dune-02.log`

### 更新ビルド drop-audit-final-local-02 (2026-10-23T14:47:44)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-check-source.py /home/mikam/RefinedRust/hinata_mikami/gc/output/gc/audit/drop_calls.v`
- 終了コード: 0、所要時間: 8.1秒
- 詳細ログ: `/tmp/refinedrust-upgrade-drop-audit-final-local-02.log`

### 更新ビルド sweep-post-tactics-local (2026-10-23T14:48:53)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-check-source.py /tmp/test_sweep_post_tactics.v`
- 終了コード: 0、所要時間: 3.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-post-tactics-local.log`

### 更新ビルド sweep-contract-cargo-final (2026-10-23T14:49:47)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `cargo refinedrust -- --locked --offline`
- 終了コード: 0、所要時間: 2.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-cargo-final.log`

### 更新ビルド sweep-contract-dune-final (2026-10-23T14:49:59)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `dune build -j 1 --display=short`
- 終了コード: 0、所要時間: 5.6秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-dune-final.log`

### 更新ビルド sweep-contract-assumptions-final (2026-10-23T14:55:30)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `python3 audit/check_assumptions.py --report verification_assumptions_20261023.txt --raw-output audit/artifacts/20261023/assumptions.raw.txt`
- 終了コード: 1、所要時間: 315.3秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-assumptions-final.log`

### 更新ビルド audit-marker-after-import (2026-10-23T14:58:16)

- 実行場所: `/home/mikam/RefinedRust`
- コマンド: `python3 /tmp/refinedrust-check-source.py /tmp/test_audit_marker.v`
- 終了コード: 0、所要時間: 3.2秒
- 詳細ログ: `/tmp/refinedrust-upgrade-audit-marker-after-import.log`

### 更新ビルド sweep-contract-assumptions-final-02 (2026-10-23T15:01:58)

- 実行場所: `/home/mikam/RefinedRust/hinata_mikami/gc`
- コマンド: `python3 audit/check_assumptions.py --report verification_assumptions_20261023.txt --raw-output audit/artifacts/20261023/assumptions.raw.txt`
- 終了コード: 0、所要時間: 303.5秒
- 詳細ログ: `/tmp/refinedrust-upgrade-sweep-contract-assumptions-final-02.log`
