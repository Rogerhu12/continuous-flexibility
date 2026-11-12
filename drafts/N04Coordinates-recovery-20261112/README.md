# Incremental recovery snapshot 6

This storage checkpoint contains the unchanged current line tree and newly saved candidate versions. Earlier sources and reviews are preserved in the previous backup commits. SOURCE-INDEX.json maps every current local candidate to its exact Git commit/path or this snapshot, with SHA256.

The prior snapshot is 20854f91f48a59f7ba5f6f0ab592a0543c442141. It remains the first parent; the current actual line commit is the second parent. This avoids copying already preserved uncompiled sources into every tree. All newly added Lean lines and current line additions are still counted against the latest complete green baseline. No file extension is changed to avoid that limit.

This branch is for recovery only. It is outside the active generated root, runs no line workflow and makes no compilation or theorem completion claim.
