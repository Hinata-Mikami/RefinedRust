from pathlib import Path
import collections, csv, hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent

def mask_comments(s):
    out = list(s)
    depth = 0
    quoted = False
    i = 0
    while i < len(s):
        if depth:
            if s.startswith('(*', i):
                depth += 1
                out[i:i+2] = '  '
                i += 2
            elif s.startswith('*)', i):
                depth -= 1
                out[i:i+2] = '  '
                i += 2
            else:
                if s[i] != '\n':
                    out[i] = ' '
                i += 1
        elif quoted:
            if s[i] == '"':
                if s.startswith('""', i):
                    i += 2
                else:
                    quoted = False
                    i += 1
            else:
                i += 1
        elif s.startswith('(*', i):
            depth = 1
            out[i:i+2] = '  '
            i += 2
        else:
            quoted = s[i] == '"'
            i += 1
    assert depth == 0
    return ''.join(out)

DECL = re.compile(r'(?m)^[ \t]*(?P<qual>(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*)(?P<kind>Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Class|Lemma|Theorem|Corollary|Proposition|Fact|Example|Instance|Axiom|Parameter)\s+(?P<name>[\w\']+)')

def inventory(text, path, group):
    s = mask_comments(text)
    ds = list(DECL.finditer(s))
    result = []
    for k, d in enumerate(ds):
        end = ds[k+1].start() if k+1 < len(ds) else len(s)
        body = s[d.start():end]
        orig = text[d.start():end]
        proof = re.search(r'\bProof\s*\.', body)
        terminal = re.search(r'\b(Qed|Defined|Admitted|Abort)\s*\.', body)
        proof_lines = 0
        if proof:
            p_end = terminal.start() if terminal else len(body)
            # Count physical, nonblank, noncomment lines between Proof. and end.
            proof_lines = sum(bool(x.strip()) for x in body[proof.end():p_end].splitlines())
        result.append(dict(group=group, file=path, name=d['name'], kind=d['kind'], qualifier=d['qual'].strip(), line=s.count('\n',0,d.start())+1, has_script=bool(proof), ending=terminal[1] if terminal else 'term', proof_nonblank_lines=proof_lines, statement_sha256=hashlib.sha256(body[:proof.start() if proof else len(body)].strip().encode()).hexdigest()))
    return result

def paths():
    for p in sorted((ROOT/'hinata_mikami/extra_proofs/gc').glob('*.v')):
        yield p, 'support'
    for p in sorted((ROOT/'hinata_mikami/gc/output/gc/proofs').glob('*.v')):
        yield p, 'typing'
    for p in sorted((ROOT/'hinata_mikami/gc/output/gc/audit').glob('*.v')):
        yield p, 'drop_audit'

def main():
    rows = []
    for p,g in paths():
        rel=str(p.relative_to(ROOT))
        these=inventory(p.read_text(),rel,g)
        rows.extend(these)
        counts=collections.Counter(r['kind'] for r in these)
        print(rel,dict(counts),'scripts',sum(r['has_script'] for r in these),'proof NLOC',sum(r['proof_nonblank_lines'] for r in these))
    for g in ['support','typing','drop_audit']:
        these=[r for r in rows if r['group']==g]
        print('GROUP',g,'declarations',len(these),'kinds',dict(collections.Counter(r['kind'] for r in these)),'scripts',sum(r['has_script'] for r in these),'proof NLOC',sum(r['proof_nonblank_lines'] for r in these))
    (OUT/'inventory.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
    with (OUT/'inventory.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    old=[]
    for p,g in paths():
        rel=str(p.relative_to(ROOT))
        res=subprocess.run(['git','show','644763f1:'+rel],cwd=ROOT,text=True,capture_output=True)
        if res.returncode==0:
            old.extend(inventory(res.stdout,rel,g))
    (OUT/'inventory_before_codex.json').write_text(json.dumps(old,ensure_ascii=False,indent=2))
    old_keys={(r['file'],r['name']) for r in old}
    new=[r for r in rows if (r['file'],r['name']) not in old_keys]
    print('ADDED SINCE 644763f1',len(new),dict(collections.Counter((r['group'],r['kind']) for r in new)))
    for r in new:print('NEW',r['group'],r['kind'],r['name'])

if __name__ == '__main__':
    main()
