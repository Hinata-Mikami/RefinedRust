"""Audit the native Dune artifacts after sourcing ../activate.sh and dune build.

Print Assumptions checks logical axioms. Callee contracts (including only_spec)
remain premises of the typing lemmas and are a separate trust boundary.
"""

import argparse
import hashlib
import pathlib
import re
import shlex
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=pathlib.Path)
    parser.add_argument("--raw-output", type=pathlib.Path)
    options = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parents[3]
    proofs = root / "hinata_mikami/gc/output/gc/proofs"
    build = root / "_build/default"
    project = build / proofs.relative_to(root) / "_RocqProject"
    args = []
    for line in project.read_text().splitlines():
        tokens = shlex.split(line, comments=True)
        if not tokens:
            continue
        if tokens[0] == "-arg":
            args.extend(tokens[1:])
        elif tokens[0] in ("-Q", "-R", "-I"):
            path = pathlib.Path(tokens[1])
            if not path.is_absolute():
                path = (proofs / path).resolve()
            args.extend([tokens[0], str(path), *tokens[2:]])
    args.extend([
        "-Q", str(build / "hinata_mikami/gc/output/gc/audit"), "hinata_mikami.gc.audit"
    ])

    queries = ["From Stdlib Require Import Strings.String."]
    names, sources = [], []
    for folder, prefix in [
        (root / "hinata_mikami/extra_proofs/gc", "hinata_mikami.extra_proofs.gc"),
        (proofs, "refinedrust.examples.gc.proofs"),
        (root / "hinata_mikami/gc/output/gc/audit", "hinata_mikami.gc.audit"),
    ]:
        for source in sorted(folder.glob("*.v")):
            built_source = build / source.relative_to(root)
            if not built_source.with_suffix(".vo").exists():
                raise RuntimeError(f"Native .vo missing: {source}; run dune build")
            if source.read_bytes() != built_source.read_bytes():
                raise RuntimeError(f"Stale Dune source: {source}; run dune build")
            sources.append(source)
            queries.append(f"From {prefix} Require Import {source.stem}.")
            for name in re.findall(
                r"^(?:Lemma|Theorem|Example)\s+([\w']+)",
                source.read_text(), flags=re.M,
            ):
                qualified = f"{prefix}.{source.stem}.{name}"
                names.append(qualified)
                queries.extend([
                    f'Eval compute in "RR-BEGIN|{qualified}"%string.',
                    f"Print Assumptions {qualified}.",
                    f'Eval compute in "RR-END|{qualified}"%string.',
                ])
    result = subprocess.run(
        ["rocq", "repl", "-quiet", *args], cwd=proofs,
        input="\n".join(queries + ["Quit."]) + "\n", text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if options.raw_output:
        options.raw_output.write_text(result.stdout)
    if result.returncode or "Error:" in result.stdout:
        raise RuntimeError("Rocq audit failed; inspect --raw-output")

    allowed = {
        "FunctionalExtensionality.functional_extensionality_dep",
        "ProofIrrelevance.proof_irrelevance",
    }
    lines = [
        "RefinedRust GC 証明依存関係監査（仕様強化後、2026-10-23）",
        f"対象: {len(names)} 件（補助補題・GC 型付け定理・Drop 検査）",
        "全対象の通常 .vo と Dune 内ソースの一致を確認。",
        "許可する基盤公理: functional_extensionality_dep, proof_irrelevance のみ。",
        "注意: only_spec 等の呼び出し先契約は型付け定理の前提であり、",
        "この公理監査はライブラリ実装や物理解放の証明を意味しない。",
        "Drop 検査は静的 CFG と単一遷移の観測器。sweep 全実行の履歴ではない。",
        "", "定理ごとの監査結果:",
    ]
    for name in names:
        match = re.search(
            r'=\s*"RR-BEGIN\|' + re.escape(name) + r'"(?:%string)?\s*:\s*string(.*?)'
            r'=\s*"RR-END\|' + re.escape(name) + r'"',
            result.stdout, flags=re.S,
        )
        if not match:
            raise RuntimeError(f"Missing audit result: {name}")
        block = match.group(1)
        if "Closed under the global context" in block:
            axioms = set()
        else:
            axiom_block = re.search(r"Axioms:\s*(.*?)(?:\nRocq <|\Z)", block, re.S)
            if not axiom_block:
                raise RuntimeError(f"Unknown assumptions output: {name}")
            axioms = set(re.findall(r"^([\w.']+)\s*:", axiom_block.group(1), re.M))
            if not axioms:
                raise RuntimeError(f"Unparsed axiom list: {name}")
        if axioms - allowed:
            raise RuntimeError(f"Unexpected axioms for {name}: {sorted(axioms - allowed)}")
        status = ", ".join(sorted(axioms)) or "Closed under the global context"
        lines.append(f"{name}: {status}")
    lines.extend(["", "対象手動ソースの SHA256:"])
    sources.extend([
        root / "hinata_mikami/gc/src/main.rs",
        root / "hinata_mikami/gc/RefinedRust.toml",
        root / "hinata_mikami/gc/output/gc/generated/generated_code_gc.v",
        root / "hinata_mikami/gc/output/gc/generated/generated_specs_gc.v",
    ])
    for source in sources:
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        lines.append(f"{digest}  {source.relative_to(root)}")
    report = "\n".join(lines) + "\n"
    if options.report:
        options.report.write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
