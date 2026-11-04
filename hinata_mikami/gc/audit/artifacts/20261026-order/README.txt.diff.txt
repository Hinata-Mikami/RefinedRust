--- before/hinata_mikami/gc/audit/README.txt
+++ after/hinata_mikami/gc/audit/README.txt
@@ -1,4 +1,4 @@
-GC の追加検査（2026-10-23）
+GC の追加検査（2026-10-26 更新）
 
 主要な事後条件は ../src/main.rs の sweep と、
 ../../extra_proofs/gc/sweep_contract.v にある。
@@ -33,7 +33,8 @@
   cargo refinedrust -- --locked --offline
   dune build
   python3 audit/check_assumptions.py \
-    --report verification_assumptions_20261023.txt \
+    --date 2026-10-26 \
+    --report verification_assumptions_20261026.txt \
     --raw-output /tmp/gc-assumptions.txt
 
 check_assumptions.py は、手動ソースが Dune 内のコピーと一致し、通常の
