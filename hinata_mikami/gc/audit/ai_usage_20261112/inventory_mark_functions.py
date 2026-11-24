"""Inventory the current mark_from / mark / sweep specification and proof sources.

Reads source text only. Does not regenerate or compile proofs.
Dependency labels mean explicit source references, not kernel-term dependencies.
"""
from pathlib import Path
import collections
import csv
import html
import importlib.util
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
spec = importlib.util.spec_from_file_location('gc_inventory_util', OUT/'inventory.py')
util = importlib.util.module_from_spec(spec)
spec.loader.exec_module(util)

SUPPORT = sorted((ROOT/'hinata_mikami/extra_proofs/gc').glob('*.v'))
TARGETS = ['mark_from', 'mark', 'sweep']
PROOFS = {fn: ROOT/f'hinata_mikami/gc/output/gc/proofs/proof_Heap_{fn}.v' for fn in TARGETS}

DESCRIPTIONS = {
    'mark_from_rel': 'mark_fromの開始時・終了時マーク列を結ぶ帰納的な実行関係。',
    'reachable_from': '任意の開始添字から対象添字への到達可能性。',
    'reachable': '添字0をrootとする到達可能性。',
    'all_unmarked': 'マーク列の全要素がfalse。',
    'marks_closed_except': '指定した現在位置を例外として、マーク集合がnextに沿って閉じる。',
    'marks_closed': 'markedなノードの非NULLのnext先もmarked。',
    'keep_marked': '同じ添字の開始時マークがtrueの要素だけを残す関数。',
    'keep_marked_suffix': '未処理prefixをそのまま残し、処理済みsuffixだけをフィルタする関数。',
    'sweep_marks': '未処理prefixのマークを保持し、残る処理済みノードのマークをfalseにする関数。',
    'aligned_nodes': '値・位置・next・markの4列と、各ノードの資源Φの対応。',
    'sweep_nodes_inv': 'sweepの処理境界に応じた4列とノード資源の不変条件。',
    'reachable_loc': '添字を介して、アドレスについて述べた到達可能性。',
    'marking_exact': 'marked iff reachableが各添字で成立。',
    'keep_unmarked': '開始時にfalseの要素だけを残す関数。',
    'sweep_drop_targets': '開始時にfalseだったアドレスを後方走査順に並べた候補列。実行済みDropの記録ではない。',
    'sweep_kept_exact': '残存アドレス iff 開始時marked。',
    'sweep_reachable_exact': '残存アドレス iff 開始時reachable。',
    'sweep_reachability_preserved': '処理前後でアドレスによる到達可能性が一致。',
    'sweep_post': '保持対象の正確さと、条件付きの到達可能性一致・保存をまとめた事後条件。',
    'sweep_fields_preserved': 'フィルタ後の同じ位置のアドレス・値・nextが、元の同一ノードに由来する。',
    'simplify_goal_big_sepL_app_inst': 'big_sepL連結補題を自動化へ登録する定義。仕様用述語ではない。',
    'reachable_from_trans': '到達可能性の推移律。',
    'mark_from_rel_sound': '終了後trueなら、開始前からtrue、または開始位置からreachable。',
    'mark_from_rel_sound_unmarked': '全falseで開始した場合のsoundness。',
    'mark_from_rel_sound_root': 'root開始の場合のsoundness。',
    'mark_from_rel_preserves_true': 'すでにtrueだったマークを保持。',
    'mark_from_rel_marks_start': '実行開始位置は終了後true。',
    'nodup_locs_lookup_unique': 'NoDupの下で同じアドレスを指す添字が一意。',
    'all_unmarked_closed_except': '全falseなら例外付きマーク閉包が成立。',
    'mark_from_rel_final_closed': '例外付き閉包と遷移から、終了時の例外なし閉包を得る。',
    'mark_from_rel_final_closed_unmarked': '全false開始から終了時marks_closedを得る。',
    'mark_from_rel_complete': '全false開始・NoDupの下で、reachableな位置は終了後true。',
    'mark_from_rel_complete_root': 'root開始の場合のcompleteness。',
    'mark_from_rel_exact_root': 'root開始・全false・NoDupの下で、終了後marked iff reachable。',
    'keep_marked_suffix_0': '境界0ではリスト全体のフィルタ。',
    'keep_marked_suffix_length': '境界が元の長さならリストは未処理のまま。',
    'sweep_marks_length': '境界がマーク列の長さなら元のマーク列。',
    'sweep_marks_0': '境界0では残存ノード分のfalse列。',
    'keep_marked_suffix_step_true': 'trueの要素を処理しても保持リストは変わらない。',
    'sweep_marks_step_true': 'trueのノードを処理すると対応する実マークをfalseに更新。',
    'keep_marked_suffix_step_false': 'falseの要素を削除すると次の境界のリストになる。',
    'sweep_marks_step_false': 'falseのノード削除と次の境界のマーク列が対応。',
    'elem_of_keep_marked': 'フィルタ後の所属と、元の添字・trueマークの存在が同値。',
    'simplify_goal_big_sepL_app': '連結リストのbig_sepLを、前半・後半の資源へ分けて自動化に渡す。',
    'prove_with_subtype_big_sepL_acc': '1要素の資源と戻す継続から、リスト全体の部分型証明へ接続。',
    'NoDup_snoc_local': '未登録要素の末尾追加がNoDupを保つ。allocで使用。',
    'freeable_full_ne': '2つの完全な解放権限から、位置が異なることを導く。',
    'freeable_nz_full_ne': '正のサイズのfreeable_nz版。allocで使用。',
    'freeable_full_ne_gives': '解放権限から位置の相違を得る自動化インスタンス。',
    'keep_marked_length_same_mask': '同長の2列を同じマークでフィルタすると同長。',
    'keep_marked_NoDup': 'フィルタがNoDupを保存。',
    'keep_marked_Forall': 'フィルタが各要素の性質を保存。',
    'marks_closed_keep_marked_next_valid': '元のnext有効性・非NULL性・閉包から、フィルタ後のnext有効性を得る。',
    'aligned_nodes_cons': '整列したノード資源を先頭と残部に分解。',
    'sweep_nodes_inv_cons': '未処理先頭ノードの資源と残部のsweep不変条件に分解。',
    'sweep_nodes_inv_zero_cons': '境界0で、先頭の元マークに応じて生存・削除を区別。',
    'sweep_nodes_inv_init': '開始時の所有権からループ不変条件を構築。',
    'sweep_nodes_inv_step': '処理対象ノードと、処理後に不変条件を再構成する継続を取り出す。',
    'sweep_nodes_inv_done': '境界0の不変条件から、最終フィルタ結果の所有権を取り出す。',
    'elem_of_keep_unmarked': '未マーク側のフィルタ所属の特徴付け。',
    'sweep_kept_exact_filter': 'フィルタ結果について残存 iff 開始時markedを示す。',
    'sweep_reachable_exact_filter': 'marking_exactの下で残存 iff reachableを示す。',
    'sweep_partition': '元のノード集合を保持・除去候補へ完全に分割。',
    'sweep_partition_disjoint': '保持集合と除去候補集合が交わらない。',
    'sweep_drop_targets_exact': 'Drop候補 iff 元の対応マークがfalse。',
    'sweep_drop_targets_nodup': 'Drop候補に重複がない。',
    'sweep_drop_targets_unreachable': '正確なマークの下で、Drop候補 iff 元の非到達ノード。',
    'keep_marked_lookup_pair': '2列のフィルタ後の同じ位置を、元の共通添字へ戻す。',
    'keep_marked_lookup_pair_intro': '元の同じ位置の2要素が、フィルタ後にも同じ位置に現れる。',
    'sweep_unprocessed_marks_unchanged': '未処理prefixのマークが元のまま。',
    'sweep_reset_all_unmarked': '最終false列がall_unmarkedを満たす。',
    'keep_marked_lookup_origin': 'フィルタ後要素の元の添字とtrueマークを取り出す。',
    'keep_marked_root': 'rootがmarkedなら、フィルタ後もrootが先頭に残る。',
    'reachable_filter_forward': '元のグラフの経路をフィルタ後のグラフへ移す。',
    'reachable_filter_backward': 'フィルタ後のグラフの経路を元のグラフへ戻す。',
    'sweep_preserves_reachability': '条件を満たすフィルタで到達可能性を双方向に保存。',
    'sweep_post_filter': 'フィルタ結果がsweep_postの全成分を満たす。',
    'mark_sweep_exact': 'mark関係と初期全falseから、sweep後の残存 iff reachableを合成。',
    'mark_from_rel_length': 'mark遷移がマーク列の長さを保つ。',
    'mark_sweep_reachability_preserved': 'markの結果からsweepの到達可能性保存条件を満たすことを合成。',
    'sweep_fields_preserved_filter': '同じマスクによるフィルタがノードのフィールド対応を保つ。',
    'sweep_resets_mark_example': 'sweep_marks 0 [true] = [false]という具体例。',
    'resolve_ghost_Vec_concrete': '具体的なVec精緻化のゴースト解決を、証明済み一般規則で処理。',
    'resolve_ghost_Vec_concrete_inst': '局所resolverの自動化登録。仕様用述語ではない。',
    'prove_with_subtype_stratify_opened': '開いた場所の所有権を再整理して部分型証明へ接続。現行本証明に明示呼出しなし。',
    'keep_marked_suffix_pred_true': '境界cut−1でtrueを処理する、局所的な書換え用補題。',
    'keep_marked_suffix_pred_false': '境界cut−1でfalseを削除する、局所的な書換え用補題。',
    'Heap_mark_from_proof': 'Rust mark_fromの本体が生成された仕様を満たす。',
    'Heap_mark_proof': 'Rust markの本体が生成された仕様を満たす。',
    'Heap_sweep_proof': 'Rust sweepの本体が生成された仕様を満たす。',
}

END = re.compile(r'\b(?:(?:Time|Timeout\s+\d+)\s+)?(?P<ending>Qed|Defined|Admitted|Abort)\s*\.')
PROOF = re.compile(r'\bProof\s*\.')
rows=[]
blocks={}
for p in [*SUPPORT,*PROOFS.values()]:
    relative=str(p.relative_to(ROOT))
    text=p.read_text(); clean=util.mask_comments(text)
    matches=list(util.DECL.finditer(clean))
    for i,d in enumerate(matches):
        limit=matches[i+1].start() if i+1<len(matches) else len(clean)
        block=clean[d.start():limit]
        proof=PROOF.search(block);ending=END.search(block)
        before=block[:proof.start()] if proof else block
        proof_body=block[proof.end():ending.start()] if proof and ending else ''
        key=relative+'#'+d['name']
        row=dict(key=key,file=relative,line=clean.count('\n',0,d.start())+1,name=d['name'],kind=d['kind'],
                 description=DESCRIPTIONS.get(d['name'],''),scope='support' if p in SUPPORT else 'target_proof_file',
                 proof_nonblank_lines=sum(bool(x.strip()) for x in proof_body.splitlines()),
                 proof_start_line=clean.count('\n',0,d.start()+proof.start())+1 if proof else None,
                 proof_end_line=clean.count('\n',0,d.start()+ending.start())+1 if proof and ending else None,
                 has_proof=bool(proof),ending=ending['ending'] if proof and ending else '')
        assert row['description'],d['name']
        blocks[key]=dict(source=block,statement=before,proof=proof_body)
        rows.append(row)

by_key={r['key']:r for r in rows}
by_name=collections.defaultdict(list)
for r in rows:by_name[r['name']].append(r)
constructors={
    'mark_from_rel_marked':'mark_from_rel','mark_from_rel_null':'mark_from_rel','mark_from_rel_next':'mark_from_rel',
    'reachable_from_refl':'reachable_from','reachable_from_step':'reachable_from',
}
def refs(text,current_file=None):
    found=set()
    for name,variants in by_name.items():
        if not re.search(r'(?<![\w\'])'+re.escape(name)+r'(?![\w\'])',text):continue
        local=[r for r in variants if r['file']==current_file]
        chosen=local if local else [r for r in variants if r['scope']=='support']
        found.update(r['key'] for r in chosen)
    for name,parent in constructors.items():
        if re.search(r'\b'+name+r'\b',text):found.update(r['key'] for r in by_name[parent])
    return found

deps={}
for r in rows:
    deps[r['key']]=refs(blocks[r['key']]['source'],r['file'])-{r['key']}
def closure(initial):
    seen=set();todo=list(initial)
    while todo:
        k=todo.pop()
        if k in seen:continue
        seen.add(k);todo.extend(deps[k]-seen)
    return seen

def mask_rust_comments(text):
    out=list(text);i=0;depth=0;quoted=False
    while i<len(text):
        if depth:
            if text.startswith('/*',i):
                depth+=1;out[i:i+2]='  ';i+=2
            elif text.startswith('*/',i):
                depth-=1;out[i:i+2]='  ';i+=2
            else:
                if text[i]!='\n':out[i]=' '
                i+=1
        elif quoted:
            if text[i]=='\\':i+=2
            else:
                if text[i]=='"':quoted=False
                i+=1
        elif text.startswith('//',i):
            end=text.find('\n',i)
            if end<0:end=len(text)
            out[i:end]=' '*(end-i);i=end
        elif text.startswith('/*',i):
            depth=1;out[i:i+2]='  ';i+=2
        else:
            quoted=text[i]=='"';i+=1
    assert depth==0
    return ''.join(out)

rust=mask_rust_comments((ROOT/'hinata_mikami/gc/src/main.rs').read_text())
annotation_direct={};annotation_closure={};proof_closure={}
for fn in TARGETS:
    pos=rust.index('unsafe fn '+fn+'(')
    start=rust.rfind('    #[rr::params',0,pos)
    # Include loop annotations inside the function body as well as its contract.
    brace=rust.index('{',pos);end=brace;depth=0;quoted=False
    while end<len(rust):
        ch=rust[end]
        if quoted:
            if ch=='\\':end+=2;continue
            if ch=='"':quoted=False
        elif ch=='"':quoted=True
        elif ch=='{':depth+=1
        elif ch=='}':
            depth-=1
            if depth==0:
                end+=1;break
        end+=1
    assert depth==0
    annotation_direct[fn]=refs(rust[start:end])
    annotation_closure[fn]=closure(annotation_direct[fn])
    main=str(PROOFS[fn].relative_to(ROOT))+'#Heap_'+fn+'_proof'
    proof_closure[fn]=closure({main})
for r in rows:
    key=r['key']
    r['annotation_direct_for']=';'.join(fn for fn in TARGETS if key in annotation_direct[fn])
    r['annotation_indirect_for']=';'.join(fn for fn in TARGETS if key in annotation_closure[fn]-annotation_direct[fn])
    r['proof_source_reference_closure_for']=';'.join(fn for fn in TARGETS if key in proof_closure[fn])
    r['dependencies']=';'.join(sorted(deps[key]))

math_defs=[r for r in rows if r['scope']=='support' and r['kind'] in ['Inductive','Definition','Fixpoint'] and not r['name'].endswith('_inst')]
lemmas=[r for r in rows if r['scope']=='support' and r['kind'] in ['Lemma','Theorem','Corollary']]
extras=[r for r in rows if r['scope']=='support' and r['kind'] in ['Example','Instance']]
local_lemmas=[r for r in rows if r['scope']=='target_proof_file' and r['kind']=='Lemma' and not r['name'].endswith('_proof')]
assert len(math_defs)==20 and len(lemmas)==59 and len(extras)==2 and len(local_lemmas)==6
assert len(set().union(*annotation_direct.values()))==8, {fn:[by_key[k]['name'] for k in v] for fn,v in annotation_direct.items()}

file_rows=[]
all_files=[*SUPPORT,*sorted((ROOT/'hinata_mikami/gc/output/gc/proofs').glob('*.v')),*sorted((ROOT/'hinata_mikami/gc/output/gc/audit').glob('*.v'))]
for p in all_files:
    relative=str(p.relative_to(ROOT));text=p.read_text();clean=util.mask_comments(text)
    intervals=[]
    for match in PROOF.finditer(clean):
        end=END.search(clean,match.end());assert end,p
        intervals.append(clean[match.end():end.start()])
    main_name='Heap_'+p.stem.removeprefix('proof_Heap_')+'_proof' if p in PROOFS.values() else None
    main=next((r for r in rows if r['file']==relative and r['name']==main_name),None)
    group='shared_support' if p in SUPPORT else 'target_proof' if p in PROOFS.values() else 'drop_audit' if '/audit/' in relative else 'other_gc_proof'
    file_rows.append(dict(file=relative,group=group,total_lines=text.count('\n'),nonblank_noncomment_lines=sum(bool(x.strip()) for x in clean.splitlines()),
                          all_proof_bodies_nonblank_lines=sum(sum(bool(x.strip()) for x in s.splitlines()) for s in intervals),
                          main_proof_body_nonblank_lines=main['proof_nonblank_lines'] if main else '',proof_blocks=len(intervals)))

generated=[]
for fn in TARGETS:
    p=ROOT/f'hinata_mikami/gc/output/gc/generated/generated_template_Heap_{fn}.v'
    text=p.read_text();line=next(i for i,s in enumerate(text.splitlines(),1) if s.startswith('Definition Heap_'+fn+'_lemma'))
    generated.append(dict(function=fn,template_file=str(p.relative_to(ROOT)),template_total_lines=text.count('\n'),
                          obligation='Heap_'+fn+'_lemma',obligation_line=line,spec='type_of_Heap_'+fn,proof='Heap_'+fn+'_proof'))

def csv_write(name,data):
    with (OUT/name).open('w',encoding='utf-8-sig',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(data[0]));w.writeheader();w.writerows(data)
csv_write('mark_predicates.csv',math_defs)
csv_write('mark_lemmas.csv',lemmas+extras+local_lemmas)
csv_write('proof_file_lines.csv',file_rows)
(OUT/'mark_function_inventory.json').write_text(json.dumps(dict(definitions=math_defs,lemmas=lemmas,extras=extras,local_lemmas=local_lemmas,
    all_declarations=rows,files=file_rows,generated_obligations=generated,
    annotation_direct={fn:[by_key[k]['name'] for k in sorted(v)] for fn,v in annotation_direct.items()},
    scope_note='Explicit source references; automatic instance selection is not reconstructed from proof terms.'),ensure_ascii=False,indent=2)+'\n')

def esc(s):return html.escape(str(s))
def src(r):return '<a href="'+esc(str(ROOT/r['file'])+':'+str(r['line']))+'"><code>'+esc(r['name'])+'</code></a>'
def relation(r):
    labels=[]
    for key,label in [('annotation_direct_for','注釈に直接'),('annotation_indirect_for','注釈の内部定義'),('proof_source_reference_closure_for','本証明から参照')]:
        if r[key]:labels.append(label+': '+r[key].replace(';',', '))
    if not labels:labels.append('ライブラリに残存。対象3本からの明示参照なし。')
    return '<br>'.join(esc(s) for s in labels)
def decl_table(rs,proof=False):
    h='<table><tr><th>名前・ソース</th><th>役割</th><th>3関数との関係</th>'
    if proof:h+='<th>証明部分の実質行数</th>'
    h+='</tr>'
    for r in rs:
        h+='<tr><td>'+src(r)+'</td><td>'+esc(r['description'])+'</td><td>'+relation(r)+'</td>'
        if proof:h+='<td>'+str(r['proof_nonblank_lines'])+'</td>'
        h+='</tr>'
    return h+'</table>'

style='body{font:15px/1.8 system-ui,sans-serif;color:#182331;max-width:1250px;margin:36px auto;padding:0 24px}h1{font-size:27px}h2{font-size:21px;margin-top:38px;border-bottom:1px solid #ccd3dd}h3{font-size:17px}table{border-collapse:collapse;width:100%;font-size:13px;margin:16px 0 28px}th,td{border:1px solid #ccd3dd;padding:9px;vertical-align:top;text-align:left}th{background:#edf2f8}a{color:#185aa5}code{overflow-wrap:anywhere}.note{background:#f3f5f8;padding:14px}.flow{font-size:16px;background:#eef3f9;padding:16px} @media print{body{font-size:9pt;max-width:none}tr{break-inside:avoid}h2,h3{break-after:avoid}}'
parts=['<h1>mark_from・mark・sweep：仕様用定義・補題・証明ファイルの全体像</h1><p>2026年11月12日 JSTの作業ツリーを読み取り。研究用に追加されたRocq定義・補題を対象とし、stdpp/Iris/RefinedRust本体の一般補題は除く。</p>']
parts.append('<p class="note">共有ライブラリには、仕様・証明用の述語／数学的関数20件、補題・定理59件、Example 1件、Instance 1件、自動化登録用Definition 1件がある。対象3つのproofファイルには局所補題6件（同じresolverの3コピーを含む）と本証明3件がある。全てを以下に列挙する。現行で明示参照のない補助物も注記して残す。</p>')
parts.append('<h2>1. アノテーションが直接使う定義</h2><table><tr><th>関数</th><th>直接参照する独自の述語・関数</th></tr>')
for fn in TARGETS:
    names=sorted(by_key[k]['name'] for k in annotation_direct[fn])
    parts.append('<tr><td><code>'+fn+'</code></td><td>'+', '.join('<code>'+esc(n)+'</code>' for n in names)+'</td></tr>')
parts.append('</table><p>Heap不変条件の長さ一致・NoDup・非NULL性・nextの妥当性・ノード所有権は別途共通に使う。NoDup、Forall、guarded、freeable_nz等は既存ライブラリの定義。上記の独自定義数には含めない。mark_from_relの構成子はmarked/null/nextの3件、reachable_fromの構成子はrefl/stepの2件であり、独立した補題として二重計上しない。</p>')
parts.append('<p class="flow">Rust mark_from → mark_from_rel<br>mark_from_relのsoundness・completeness・閉包 → Rust markの到達可能性・閉包の事後条件<br>keep_marked_suffix・sweep_marks・sweep_nodes_inv → Rust sweepのループ証明 → sweep_postと実メモリの所有権</p>')
parts.append('<h2>2. 述語・数学的関数20件</h2>'+decl_table(math_defs)+'<p><code>marks_closed_except</code>はmarkの純粋証明用。<code>keep_unmarked</code>・<code>sweep_drop_targets</code>は除去候補の数学的検査用。<code>sweep_fields_preserved</code>は仕様整理後も補助定理として残る。全20件がアノテーションに直接現れるわけではない。</p>')
parts.append('<h2>3. 共有補題・定理59件</h2>')
for p in SUPPORT:
    selected=[r for r in lemmas if r['file']==str(p.relative_to(ROOT))]
    parts.append('<h3>'+esc(p.name)+'：'+str(len(selected))+'件</h3>'+decl_table(selected,True))
parts.append('<h3>別枠のInstance・Example</h3>'+decl_table(extras,True))
parts.append('<p><code>simplify_goal_big_sepL_app_inst</code>は自動化への登録用Definition。<code>NoDup_snoc_local</code>・<code>freeable_full_ne</code>・<code>freeable_nz_full_ne</code>は主にallocの新規ノード追加・所有権一意性を支える。登録済みインスタンスの実際の選択はこのソース参照調査だけでは断定しない。</p>')
parts.append('<h2>4. 対象proofファイル内の局所補題6件</h2>'+decl_table(local_lemmas,True)+'<p><code>resolve_ghost_Vec_concrete</code>は3ファイルに1コピーずつあり、それぞれ<code>resolve_ghost_Vec_concrete_inst</code>で登録される。<code>prove_with_subtype_stratify_opened</code>は現行sweep本証明から明示的には呼ばれない。<code>liRStepUntilBb2</code>はsweepファイルに定義されたLtacで、補題ではない。本証明中の<code>P</code>・<code>Pnew</code>（mark_from）と<code>Φ</code>（sweep）も局所的な資源述語の略記であり、独立したグローバル宣言として数えない。</p>')
parts.append('<h2>5. RefinedRustが生成する3つの証明義務</h2><table><tr><th>関数</th><th>生成仕様</th><th>生成される命題</th><th>永続ファイルの本証明</th><th>生成テンプレート総行数</th></tr>')
for g in generated:
    parts.append('<tr><td>'+esc(g['function'])+'</td><td><code>'+esc(g['spec'])+'</code></td><td><a href="'+esc(str(ROOT/g['template_file'])+':'+str(g['obligation_line']))+'"><code>'+esc(g['obligation'])+'</code></a></td><td><code>'+esc(g['proof'])+'</code></td><td>'+str(g['template_total_lines'])+'</td></tr>')
parts.append('</table><p>生成命題は<code>Definition ... : Prop</code>として出力され、Rust本体が対応する関数型を満たすことを要求する。呼び出し先契約・レイアウト・linking等の前提も含む。上の共有補題59件とは別物である。</p>')
parts.append('<h2>6. 各証明ファイルの行数</h2><p>総行数＝<code>wc -l</code>相当で空行・コメント・import・宣言を含む。ソース実質行数＝空行・コメントを除いたファイル全体。証明部分実質行数＝<code>Proof.</code>〜<code>Qed.</code>の内部だけで空行・コメントを除く。<code>Time Qed.</code>全体を終端として除外。1行に複数タクティクがあっても1行と数える。</p><table><tr><th>ファイル</th><th>範囲</th><th>総行数</th><th>ソース実質</th><th>証明部分実質（全ブロック）</th><th>対象関数の本証明のみ</th></tr>')
for f in file_rows:
    label={'shared_support':'共有補助','target_proof':'今回の3関数','other_gc_proof':'他のGC関数・ヘルパー','drop_audit':'独立のDrop検査'}[f['group']]
    parts.append('<tr><td><a href="'+esc(str(ROOT/f['file']))+'">'+esc(Path(f['file']).name)+'</a></td><td>'+label+'</td><td>'+str(f['total_lines'])+'</td><td>'+str(f['nonblank_noncomment_lines'])+'</td><td>'+str(f['all_proof_bodies_nonblank_lines'])+'</td><td>'+str(f['main_proof_body_nonblank_lines'])+'</td></tr>')
parts.append('</table>')
parts.append('<h2>7. 読み取り上の注意</h2><p>依存関係の表示は、注釈・定義・証明ソースに名前が明示されていることをたどったもの。自動タクティクや型クラス探索で最終的に採用された全補題を証明項から抽出した結果ではない。<code>try</code>内の補題もソース参照に含む。<code>mark_sweep_exact</code>等の合成定理、Drop候補の性質、フィールド保存・リセットの補助検査も列挙したが、全てが対象3つの本証明から直接呼ばれるわけではない。collectのRust本体検証はこの合成定理とは別。</p>')
parts.append('<p>CSV: <a href="mark_predicates.csv">全20定義</a> / <a href="mark_lemmas.csv">全59補題＋別枠2件＋局所6件</a> / <a href="proof_file_lines.csv">ファイル行数</a> / <a href="mark_function_inventory.json">依存関係・全宣言JSON</a>。再集計: <code>python3 inventory_mark_functions.py</code>。この作業では生成・コンパイルは実行していない。</p>')
(OUT/'mark_functions.html').write_text('<!doctype html><html lang="ja"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>mark_from・mark・sweep の定義・補題一覧</title><style>'+style+'</style><body>'+''.join(parts)+'</body></html>')

print('ANNOTATIONS',json.dumps({fn:sorted(by_key[k]['name'] for k in v) for fn,v in annotation_direct.items()},ensure_ascii=False))
print('COUNTS',dict(math_definitions=len(math_defs),support_lemmas=len(lemmas),instance_example=len(extras),local_lemmas=len(local_lemmas)))
for f in file_rows:print('LINES',json.dumps(f,ensure_ascii=False))
print('SHARED PROOF CLOSURE',json.dumps({fn:sorted(by_key[k]['name'] for k in proof_closure[fn] if by_key[k]['scope']=='support') for fn in TARGETS},ensure_ascii=False))
