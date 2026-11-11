# R05 and R06 radial contract migration

The coordinated revision of the actual mass and resistance intervals,
overlapping seam covers, and left outward labels passed the full build in
`checkpoint-2026-11-11-radial-contract-wave.json`. The exact patch and
review are preserved with that checkpoint. The actual infinite profile
and deep-tail inverse remain proof obligations.

In [§5](../paper/flexible-surface-rewrite/05-flat-end-chain.tex), lines 79–80,
107 and 187–195, write $L_n=r_n(X_c)$, $C_n=r_n(X_R)$, and
$U_n=r_n(X_R+c_RA_n^{-4})$. The mass interval is $[L_n,C_n]$. The
resistance interval starts at $C_n$, includes the long positive cap
$[C_n,U_n]$, and includes the short glue that follows in increasing $r$.
Lines 232–245 give the two densities $wr^6$ and $1/(wr^8)$ in $r$
coordinates, and bound the glue contribution separately.

[Radial.lean](../ContinuousFlexibility/Statements/Radial.lean), lines 637–664,
previously integrated the mass and its resistance over the entire retained
cell, then integrated the other mass and resistance over the glue alone.
The upper bound for the mass interval resistance is logarithmic in $A_n/B_n$.
The $A_n^{-4}/\lambda_n$ scale belongs to the long cap, which is included in
the wrong integral in the current specification.

The minimum proposed revision keeps the retained cell and glue coordinates.
Bind a mass endpoint to the right turning root
$X_R=-\log((1-\sqrt{1-4B_n/A_n})/2)$ in the same actual radial map, and
identify the four integrals on the real mass and resistance intervals. On the
right the resistance interval ends at $L_{n+1}$. On the left the original
increasing-$r$ interval ends at $L_{n-1}$ when that adjacent cell exists.
Treat the initial edge from the actual entrance explicitly, without reading
an unconstrained index below the construction threshold.

For R06, lines 273–278 of §5 orient the left coordinate by $-\log r$, so
the resistance following $I_n$ is the original $J_{n+1}$. The abstract
`DeepTailHypotheses` can retain its outward indexing. Check the physical
localizer labels in `TailPhysicalRelation`: the left interval between
successive nodes traverses the next cell's long cap. The current direct
consumers of `MorseMassResistanceBounds` are R05 and
`Statements.IsSelectedTail` in `RadialTargets.lean`; the latter feeds the
selection and inverse construction through R12. The final radial reference
need not expose these bookkeeping fields.
