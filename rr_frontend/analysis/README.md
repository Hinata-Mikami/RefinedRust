Analysis
========

Intra-procedural static analysis of MIR functions.

Each analysis compute a state for each program point:
* `DefinitelyAllocatedAnalysis` computes the places that are definitely allocated.
* `DefinitelyInitializedAnalysis` computes the places that are definitely initialized.
