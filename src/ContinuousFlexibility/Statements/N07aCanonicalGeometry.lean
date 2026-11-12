import ContinuousFlexibility.Statements.Nonlinear

/-!
# Primitive canonical geometry for the higher inverse estimates

The definitions now live in `Statements.Nonlinear`, before the coordinate
stage, and are carried by `NonlinearPropertiesThrough04` on the same chosen
reference, physical spaces, coordinates, and neighborhood. This compatibility
import preserves the public `Statements.CanonicalGeometry` names used by the
analytic modules. It adds no assumed inverse or regularity estimate.

See `docs/notes/N07a-interface-repair.md` for the exact construction-stage
obligations and the separate full-period weak-pairing repair.
-/
