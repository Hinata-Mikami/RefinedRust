From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.alloc_tst.generated Require Import generated_code_alloc_tst generated_specs_alloc_tst generated_template_Heap_alloc.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma simplify_goal_big_sepL_app {A}
    (xs1 xs2 : list A)
    (Φ : nat → A → iProp Σ) T :
  ([∗ list] i ↦ x ∈ xs1, Φ i x) ∗
  ([∗ list] i ↦ x ∈ xs2,
      Φ (length xs1 + i)%nat x) ∗ T
  ⊢
  simplify_goal
    ([∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x) T.
Proof.
  (*
    simplify_goal の定義を展開する。

    この補題の目的は、

      xs1 上の big_sepL
      xs2 上の、添字を length xs1 だけずらした big_sepL

    をまとめて、

      xs1 ++ xs2 上の一つの big_sepL

    に変換できることを Lithium に教えることである。
  *)
  rewrite /simplify_goal.

  (*
    Iris の big_sepL_app により、

      [∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x

    を、

      xs1 の部分
      xs2 の部分

    に分解する。
    xs2 側の添字は自動的に length xs1 だけずれる。
  *)
  rewrite big_sepL_app.

  (*
    左辺に既に必要な三つの資源があるため、
    それぞれをそのまま右辺に渡す。
  *)
  iIntros "($ & $ & $)".
Qed.


(*
  上の補題を simplify_goal の型クラスインスタンスとして登録する。

  これにより Lithium が big_sepL_app に相当するゴールを見つけた際、
  この補題を自動的に利用できるようになる。

  10%N はインスタンスの優先度。
*)
Definition simplify_goal_big_sepL_app_inst :=
  [instance @simplify_goal_big_sepL_app with 10%N].

Global Existing Instance simplify_goal_big_sepL_app_inst.



Lemma Heap_alloc_proof (π : thread_id) :
  Heap_alloc_lemma π.
Proof.
  (*
    自動生成された Heap::alloc の証明環境を展開する。

    関数の引数、事前条件、Heap の invariant、
    Rust のローカル変数などが証明コンテキストに導入される。
  *)
  Heap_alloc_prelude.

  (*
    生成された typing judgment を、
    手動でリストの構造に応じた場合分けができる位置まで進める。

    <-! は Lithium の規則を逆方向にも利用しながら
    ゴールを適切な形に整える指定。
  *)
  rep <-! liRStep; liShow.

  (*
    Rust コード中の、返り値となるポインタを
    ローカル変数 "__0" から move する処理を進める。
  *)
  rep liRStep; liShow.

  (*
    Heap invariant を再構成するときに必要になる
    refinement の existential variable Hevar_x を決める。

    h は Heap に保存されている値のリスト。

    Heap が空なら、新しく追加した v が先頭になる。
    Heap が空でなければ、従来の先頭 x がそのまま先頭になる。
  *)
  liInst Hevar_x
    (match h with
     | [] => v
     | x :: _ => x
     end).

  (*
    先頭以外の値のリストに対応する refinement を決める。

    空の Heap に追加する場合：
      新しい Heap は要素一つなので tail は空。

    空でない Heap に追加する場合：
      従来の tail の末尾に v を追加する。
  *)
  liInst Hevar_x0
    (match h with
     | [] => []
     | _ :: xs => xs ++ [v]
     end).

  liShow.

  (*
    Heap に保存されている値のリスト h について場合分けする。

    1. h = []
       初めてノードを追加する場合。

    2. h = old_v :: h_tail
       既存の Heap の末尾にノードを追加する場合。
  *)
  destruct h as [| old_v h_tail].

  (* ================================================================ *)
  (* h = []：空の Heap に最初のノードを追加する場合                   *)
  (* ================================================================ *)
  - (*
      h0 はノードの location のリスト。

      値のリスト h が空なら、長さの invariant により
      location のリスト h0 も空でなければならない。

      h0 が非空のケースは simpl と lia で矛盾として除去される。
    *)
    destruct h0 as [| old_l h0_tail]; simpl in *; try lia.

    (*
      新しい値リストと location リストの長さが一致することを示す。

      空リストに要素を一つ追加したケースなので、
      この条件は簡約だけで成立する。
    *)
    split; first done.

    (*
      guarded true P を構築するには have_creds が必要になる。

      新規ノードの所有権を Heap invariant の中に
      guarded な形で格納するための credit を取得する。
    *)
    iAcquireCredits as "Hcred".

    (*
      x' は allocation によって得られた新規ノードの location。

      現在は生成された StructLtype として所有しているため、
      Heap invariant が要求する Node_ty に refold する。
    *)
    iApply (prove_with_subtype_stratify x').
    rep liRStep; liShow.

    (*
      stratification 後の通常の subtype 証明を完了する。
    *)
    iApply prove_with_subtype_default.

    (*
      allocation によって得られた、
      x' のメモリを解放可能であることを表す資源に名前を付ける。

      freeable_nz は、非ゼロの allocation を
      HeapAlloc によって解放可能であることを表す。
    *)
    iRename select
      (freeable_nz x' _ _ _)
      into "Hfree".

    (*
      現在のゴールを二つに分ける。

      左側：
        新しい Heap invariant を構築する。

      右側：
        invariant を使って Heap_ty 自体を再び fold する。

      Hcred と Hfree は invariant の構築に必要なので左側へ渡す。
    *)
    iSplitL "Hcred Hfree".
    {
      (*
        Lithium の inhale を一段進める。

        これにより、新しく確保した Node の所有権が
        Iris の空間的コンテキストに現れる。
      *)
      liRStep; liShow.

      (*
        コンテキスト中の新規 Node 所有権に名前を付ける。

        この所有権は guarded true の本体として使用される。
      *)
      iRename select
        (_ ◁ₗ[_, Owned] _ @ _)%I
        into "Hnode".

      (*
        Hcred、Hnode、Hfree を使用して、
        要素一つからなる Heap invariant を構築する。

        残りの True などの自明な部分も Lithium に処理させる。
      *)
      rep liRStep; liShow.
    }

    (*
      iSplitL の右側。

      構築済みの invariant を用いて Heap_ty を再び fold する。
      trigger_tc や SimpLtype などの型クラス呼び出しも
      Lithium に処理させる。
    *)
    rep liRStep; liShow.


  (* ================================================================ *)
  (* h = old_v :: h_tail：既存 Heap にノードを追加する場合            *)
  (* ================================================================ *)
  - (*
      値のリストが非空なので、長さ invariant により
      location のリスト h0 も非空でなければならない。

      h0 = [] のケースは lia により矛盾として除去される。
    *)
    destruct h0 as [| old_l h0_tail]; simpl in *; try lia.

    (*
      元の長さ条件は概ね、

        S (length h0_tail) = S (length h_tail)

      という形になっている。

      両辺から S を取り除き、

        length h0_tail = length h_tail

      を得る。
    *)
    injection Hlen as Hlen_tail.

    (*
      新しい tail の値リストは h_tail ++ [v]。

      新しい location 側の tail は h0_tail ++ [x']。

      その長さが一致するために、

        length (h_tail ++ [v])
          = S (length h0_tail)

      を示す。
    *)
    split.
    {
      rewrite length_app /=.
      lia.
    }

    (*
      既存の Heap invariant は概ね、

        先頭ノードの invariant
        ∗
        tail 全体の big_sepL

      という形になっている。

      まず全体を Hnodes として取得し、
      Hfirst と Htail に分解する。
    *)
    iRename select
      ((∃ l : loc, _) ∗ _)%I
      into "Hnodes".

    iDestruct "Hnodes" as "(Hfirst & Htail)".

    (*
      自動生成された refinement では、
      リストが list_fmap id の形で残ることがある。

      意味的には単なる h_tail なので、
      後の lookup 証明を簡単にするため通常のリストへ正規化する。
    *)
    assert (Hmap_h :
      list_fmap Z Z id h_tail = h_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    (*
      location のリストについても同様に
      list_fmap id を通常の h0_tail に正規化する。
    *)
    assert (Hmap_l :
      list_fmap loc loc id h0_tail = h0_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    (*
      Htail の内部に現れる list_fmap id を実際に書き換える。
    *)
    iEval (rewrite Hmap_h Hmap_l) in "Htail".

    (*
      既存の tail invariant を、新しい location リスト

        h0_tail ++ [x']

      に対応する形へ変換する。

      既存ノードの index n は append 前の範囲にあるため、
      末尾に x' を追加しても lookup の結果は変わらない。

      この段階では新規ノード自身はまだ追加せず、
      既存の h_tail に対応する部分だけを Htail_ext として作る。
    *)
    iAssert (
      [∗ list] n ↦ v6 ∈ h_tail,
        ∃ l : loc,
          ⌜(h0_tail ++ [x']) !! n = Some l⌝ ∗
          guarded true
            (l ◁ₗ[π, Owned]
              # -[#v6]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc
    )%I with "[Htail]" as "Htail_ext".
    {
      (*
        Htail の各要素について個別に変換を行う。
      *)
      iApply (big_sepL_impl with "Htail").

      (*
        n：
          tail 内の index。

        v6：
          その index に保存された値。

        Hlookup：
          h_tail !! n = Some v6。

        Hnode_old：
          その要素に対応する既存 invariant。
      *)
      iIntros "!>" (n v6 Hlookup) "Hnode_old".

      (*
        既存 invariant から、

        ・対応する location l
        ・lookup の事実 Hloc
        ・guarded な Node 所有権 Hown
        ・freeable 資源 Hfree_old

        を取り出す。
      *)
      iDestruct "Hnode_old" as (l)
        "(%Hloc & Hown & Hfree_old)".

      (*
        新しい invariant でも、同じ location l を witness とする。
      *)
      iExists l.

      iSplit.
      {
        (*
          lookup に関する命題は純粋な Coq 命題なので、
          Iris のゴールから純粋命題の証明へ移る。
        *)
        iPureIntro.

        (*
          Hlookup から n < length h_tail を得る。
        *)
        pose proof
          (lookup_lt_Some _ _ _ Hlookup)
          as Hlt.

        (*
          n は h0_tail の範囲内なので、

            (h0_tail ++ [x']) !! n

          は append 前の

            h0_tail !! n

          と同じである。
        *)
        rewrite lookup_app_l.

        - (*
            append 前と同じ lookup なので、
            元から保持している Hloc をそのまま使える。
          *)
          exact Hloc.

        - (*
            lookup_app_l を使うには、

              n < length h0_tail

            が必要。

            Hlen_tail により length h0_tail と
            length h_tail が等しいので Hlt から従う。
          *)
          rewrite Hlen_tail.
          exact Hlt.
      }

      (*
        guarded な所有権と freeable 資源は変更していないため、
        そのまま新しい invariant に渡す。
      *)
      iFrame.
    }

    (*
      新規ノードを guarded true の形で invariant に格納するため、
      have_creds を一つ取得する。

      既存ノードの guarded はそのまま再利用するので、
      既存ノード用の新しい credit は不要。
    *)
    iAcquireCredits as "Hcred_new".

    (*
      allocation 直後の x' の StructLtype を、
      invariant が要求する Node_ty に refold する。
    *)
    iApply (prove_with_subtype_stratify x').
    rep liRStep; liShow.

    iApply prove_with_subtype_default.

    (*
      新規ノード x' の freeable 資源に名前を付ける。
    *)
    iRename select
      (freeable_nz x' _ _ _)
      into "Hfree_new".

    (*
      ゴールを二分する。

      左側：
        更新後の Heap invariant を構築する。

      右側：
        Heap_ty 自体を再び fold する。

      Hfirst：
        既存の先頭ノード。

      Htail_ext：
        新しい location リストに合わせて lookup を更新した
        既存 tail。

      Hcred_new、Hfree_new：
        新規ノードの invariant に必要な資源。
    *)
    iSplitL "Hfirst Htail_ext Hcred_new Hfree_new".
    {
      (*
        Lithium を一段進め、新規ノード x' の所有権を
        Iris コンテキストに取り出す。
      *)
      liRStep; liShow.

      (*
        新規ノードの Node_ty 所有権に名前を付ける。
      *)
      iRename select
        (_ ◁ₗ[_, Owned] _ @ _)%I
        into "Hnew".

      (*
        更新後の tail 全体、

          h_tail ++ [v]

        に対する invariant を構築する。

        既存の h_tail 部分には Htail_ext を使い、
        末尾の [v] 部分には新規ノード x' を使う。
      *)
      iAssert (
        [∗ list] n ↦ v6 ∈ h_tail ++ [v],
          ∃ l : loc,
            ⌜(h0_tail ++ [x']) !! n = Some l⌝ ∗
            guarded true
              (l ◁ₗ[π, Owned]
                # -[#v6]
                @ (◁ (Node_ty <INST!>))) ∗
            freeable_nz l
              (ly_size (use_layout_alg' Node_sls))
              1 HeapAlloc
      )%I with
        "[Htail_ext Hcred_new Hnew Hfree_new]"
        as "Htail_new".
      {
        (*
          h_tail ++ [v] 上の big_sepL を、

            h_tail 上の big_sepL
            ∗
            [v] 上の big_sepL

          に分解する。
        *)
        rewrite big_sepL_app.

        (*
          既存の h_tail 部分には、
          既に構築した Htail_ext をそのまま使用する。
        *)
        iSplitL "Htail_ext".
        {
          iExact "Htail_ext".
        }

        (*
          singleton list [v] 上の big_sepL を簡約する。
        *)
        simpl.

        (*
          singleton 部分に必要な資源だけを左側へ渡す。
        *)
        iSplitL "Hcred_new Hnew Hfree_new".
        {
          (*
            新規要素 v に対応する location は x'。
          *)
          iExists x'.

          (*
            まず lookup の事実を証明する。

            後半の Hcred_new、Hnew、Hfree_new は
            空間的資源なので右側へ残す。
          *)
          iSplitR "Hcred_new Hnew Hfree_new".
          {
            iPureIntro.

            (*
              singleton 側の index は 0 なので、
              big_sepL_app により全体での index は

                length h_tail + 0

              となる。
            *)
            rewrite Nat.add_0_r.

            (*
              length h_tail を length h0_tail に書き換える。
            *)
            rewrite -Hlen_tail.

            (*
              append された部分の lookup に切り替える。

              調べる index はちょうど length h0_tail なので、
              h0_tail ++ [x'] の追加部分に入る。
            *)
            rewrite lookup_app_r; last lia.

            (*
              追加部分での相対 index は

                length h0_tail - length h0_tail = 0

              なので、singleton [x'] の先頭 x' が得られる。
            *)
            rewrite Nat.sub_diag /=.
            done.
          }

          (*
            新規ノードの guarded true を構築する。

            guarded true P は概ね、

              have_creds ∗ ▷ P

            という形。

            Hcred_new と Hnew を使用して構築する。
          *)
          iSplitL "Hcred_new Hnew".
          {
            rewrite /guarded /=.
            iFrame.
          }

          (*
            新規ノードの freeable 資源を渡す。
          *)
          iExact "Hfree_new".
        }

        (*
          singleton big_sepL の末尾に生じた True を閉じる。
        *)
        done.
      }

      (*
        既存の先頭ノード invariant を分解する。

        Hfirst は概ね、

          ∃ l,
            old_l = l
            ∗ guarded true (Node ownership at l)
            ∗ freeable_nz l

        という形。
      *)
      iDestruct "Hfirst" as (l)
        "(%Heq_l & Hguard_first & Hfree_first)".

      (*
        Some old_l = Some l から old_l = l を得る。
      *)
      injection Heq_l as Heq_l.

      (*
        witness l を old_l に置換する。
      *)
      subst l.

      (*
        ここでは Hguard_first の guarded を展開しない。

        展開すると所有権が later の下に入り、

          ▷ old_l ◁ₗ[...]

        を直接取り出す必要が生じる。

        既存ノードは変更していないため、
        guarded true (...) を丸ごと新しい invariant に再利用する。

        iRevert は Iris の仮定を再びゴール側へ戻し、
        後続の Lithium の exhale に消費させるために使う。
      *)
      iRevert "Hguard_first Hfree_first Htail_new".

      (*
        ・既存先頭ノード
        ・更新後 tail
        を組み合わせて、新しい Heap invariant の構築を完了する。
      *)
      rep liRStep; liShow.
    }
    {
      (*
        iSplitL の右側。

        左側で構築した新しい Heap invariant を使い、
        Heap_ty 全体を再び fold する。

        trigger_tc、SimpLtype、typed_context_fold などの
        自動生成された型付け処理を Lithium に任せる。
      *)
      rep liRStep; liShow.
    }


  (*
    ここまでで関数本体に関する主要な typing goal を処理した。

    残っている可能性のあるゴールを表示する。
  *)
  all: print_remaining_goal.

  (*
    Lithium が証明中に shelve した補助条件を復帰させる。

    まず、単純な等式、範囲条件、型クラス条件などを
    sidecond_solver で処理する。
  *)
  Unshelve.
  all: sidecond_solver.

  (*
    sidecond_solver で解けなかった算術条件や
    より複雑な補助条件を sidecond_hammer で処理する。
  *)
  Unshelve.
  all: sidecond_hammer.

  (*
    さらに shelved goal が残っていないか確認し、
    残っていれば内容を表示する。

    この後 Qed. が成功すれば、すべてのゴールが解決済み。
  *)
  Unshelve.
  all: print_remaining_sidecond.
Qed.

End proof.