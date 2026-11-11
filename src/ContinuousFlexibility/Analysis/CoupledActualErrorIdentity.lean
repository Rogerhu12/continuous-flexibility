import ContinuousFlexibility.Analysis.CoupledRecoveredFirstJet
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Specializing the independent error to the actual residual

The independent formulas are specialized only here. Equality of the scalar
source on the open annulus identifies its actual Fréchet angular divergence;
the N08 circle identity identifies the return residual in the other row.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {V : CoupledInverseData S} {Q : QuadraticErrorData S}
  {base loss : ℕ} {ε : ℝ}

private theorem coupled_scalarCorrectionError_congr_annulus
    (F r r' η : PolarPoint → ℝ)
    (hr : ∀ p ∈ annularOpen D, r p = r' p)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    scalarCorrectionError F r η p = scalarCorrectionError F r' η p := by
  have hmem : annularOpen D ∈ 𝓝 p := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hflux : (fun y : PolarPoint => F y * r y * angularPartial η y) =ᶠ[𝓝 p]
      (fun y : PolarPoint => F y * r' y * angularPartial η y) := by
    filter_upwards [hmem] with y hy
    exact congrArg (fun a : ℝ => F y * a * angularPartial η y) (hr y hy)
  exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1))
    (hflux.fderiv_eq (𝕜 := ℝ))

theorem coupled_actualError_scalar_identity
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (y : ResidualSpace S)
    (hQ : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode (Q.Q z (jointResidual S P z) y).1.val p =
        z.2 * angularPartial (fun t => residualErrorCoefficient D S C z t *
          (S.height (3 / 4 : ℝ)).decode (P.scalar z).val t *
          angularPartial (heightPairField S (V.V z y).1) t) p +
        (S.height (3 / 4 : ℝ)).decode ((L.error z (P.circle z).val (V.V z y).1).val) p) :
    ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode (Q.Q z (jointResidual S P z) y).1.val p =
        z.2 * scalarCorrectionError (residualErrorCoefficient D S C z)
          (scalarResidualField D S C z) (heightPairField S (V.V z y).1) p +
        (S.height (3 / 4 : ℝ)).decode ((L.error z (R.residual z) (V.V z y).1).val) p := by
  intro p hp
  have herror := coupled_scalarCorrectionError_congr_annulus
    (residualErrorCoefficient D S C z)
    ((S.height (3 / 4 : ℝ)).decode (P.scalar z).val)
    (scalarResidualField D S C z) (heightPairField S (V.V z y).1)
    (h8.2.2.1 z hz hs) hp
  have hcircle := h8.2.2.2.1 z hz hs
  exact (hQ p hp).trans (congrArg₂ (· + ·) (congrArg (z.2 * ·) herror)
    (congrArg (fun r => (S.height (3 / 4 : ℝ)).decode
      ((L.error z r (V.V z y).1).val) p) hcircle))

theorem coupled_actualError_circle_identity
    (hS : IsPhysicalSpaces D T S)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (y : ResidualSpace S)
    (hQ : ∀ m θ,
      (S.circle (3 / 4 : ℝ)).decode (Q.Q z (jointResidual S P z) y).2.val m θ =
        circleChartError S C z (P.circle z).val
          (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
            B.circleColumn z (V.V z y).2.2.1)) m θ) :
    (Q.Q z (jointResidual S P z) y).2.val = R.error z (R.residual z)
      (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
        B.circleColumn z (V.V z y).2.2.1)) := by
  let ψ := R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
    B.circleColumn z (V.V z y).2.2.1)
  have he : (Q.Q z (jointResidual S P z) y).2.val = R.error z (P.circle z).val ψ := by
    apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
    funext m θ
    exact (hQ m θ).trans (h2.2.2.2.2.1 z hz hs (P.circle z).val ψ m θ).symm
  exact he.trans (congrArg (fun r => R.error z r ψ) (h8.2.2.2.1 z hz hs))

end ContinuousFlexibility.Statements
