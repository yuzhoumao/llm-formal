---- MODULE MCKVStoreSnapshotIsolation ----
EXTENDS KVStoreSnapshotIsolation, TLC
TxIdSymmetric == Permutations(TxId)
====

