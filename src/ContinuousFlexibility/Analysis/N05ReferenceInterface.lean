import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Intermediate specifications for the canonical reference inverse

The coordinate specification concerns the actual charts, heights, cells and
their first radial derivatives. It asserts no inverse estimate. The inverse
specification uses the frozen physical relation and the actual volume norms;
its converse is a separate uniqueness problem.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

/-- Quantitative reference coordinates sufficient for transporting the radial
inverse. The chosen construction must retain all of `Through04`. In particular,
this is an existence obligation, not an additional hypothesis of `N05`.

The association controls the difference of cubic endpoint exponents by a
coefficient exponent; no uniformly bounded difference of indices is required.
The number of pieces over an index may grow by a coefficient power, which
is absorbed by the fixed material loss. -/
def N05ControlledReferenceCoordinates (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) : Prop :=
  (∀ m p, p ∈ referencePhysicalPieceOpen S K m →
    K.chart (C.referenceState, 0) m p =
      ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
    K.height (C.referenceState, 0) m p = K.height (C.referenceState, 0) m (p.1, 0)) ∧
  ∃ B : ℝ, 0 < B ∧
    (∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      ∃ j, r ∈ D.cells j ∧
        |radialS (D.cellIndex j) - radialS (D.cellIndex (K.cell m))| ≤
          B * (radialQ (D.cellIndex (K.cell m)) + 1)) ∧
    (∀ n : ℕ, {m | D.cellIndex (K.cell m) = n}.Finite ∧
      ({m | D.cellIndex (K.cell m) = n}.ncard : ℝ) ≤ B * radialE n ^ B) ∧
    (∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      |K.height (C.referenceState, 0) m (r, 0)| +
      |(K.height (C.referenceState, 0) m (r, 0))⁻¹| +
      |deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r| +
      |deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r| +
      |(deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹| ≤
        B * radialE (D.cellIndex (K.cell m)) ^ B)

/-- One inverse on canonical sequences, with its continuous base restriction.
The base angular order is fixed at two, which is permitted by the frozen task. -/
structure N05ReferenceInverseData (S : PhysicalSpacesData) (K : CanonicalData S)
    (V : VolumeModelData S K) where
  weakExponent : ℝ
  sourceMaterial : ℝ
  outputMaterial : ℝ
  lossMaterial : ℝ
  physicalInverse : RadialSource → RadialUnknown
  baseInverse : V.level (3 / 4 : ℝ) 0 2 →L[ℝ] CanonicalUnknown S K
  globalInverse : CanonicalSequence S K → CanonicalUnknown S K

/-- The analytic stage proves existence in the literal physical relation,
the same inverse at all three endpoint exponents and every material/angular
order, and its actual weak first radial derivative. No graph identification
or uniqueness is included in this specification. -/
def N05ReferenceInverseBounds (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (V : VolumeModelData S K) (G : N05ReferenceInverseData S K V) : Prop :=
  0 < G.weakExponent ∧ G.weakExponent < (3 / 4 : ℝ) ∧ 0 ≤ G.lossMaterial ∧
  ReferenceInverseProperties D G.weakExponent G.sourceMaterial G.outputMaterial
    G.physicalInverse ∧
  (∀ F, G.baseInverse F = G.globalInverse (V.forget (3 / 4 : ℝ) 0 2 F)) ∧
  (∀ F, ReferenceCanonicalRelation D T S C K V G.weakExponent
    G.sourceMaterial G.outputMaterial G.lossMaterial (G.baseInverse F)
      (V.forget (3 / 4 : ℝ) 0 2 F)) ∧
  (∃ δ : ℝ, 0 < δ ∧ δ < (1 / 4 : ℝ) ∧ ∀ γ : ℝ,
    (γ = (3 / 4 : ℝ) - δ ∨ γ = (3 / 4 : ℝ) ∨ γ = (3 / 4 : ℝ) + δ) →
    ∀ t : ℝ, ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧ ∀ F : V.level γ t s,
      ∃ W : V.level γ (t - G.lossMaterial) s,
        V.forget γ (t - G.lossMaterial) s W =
          (fun m => (G.globalInverse (V.forget γ t s F)).1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K (G.globalInverse (V.forget γ t s F)) ≤
          C0 * ‖F‖) ∧
  (∀ t : ℝ, ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧
    ∀ F : V.level (3 / 4 : ℝ) t (s + 1),
      ∃ W : V.level (3 / 4 : ℝ) (t - G.lossMaterial) s,
        (∀ m φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) (t - G.lossMaterial) s W m p * φ p
            ∂canonicalMeasure S K m) =
          -(∫ p, (G.globalInverse (V.forget (3 / 4 : ℝ) t (s + 1) F)).1 m p *
            mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) ∧
        ‖W‖ ≤ C0 * ‖F‖)

end ContinuousFlexibility.Statements
