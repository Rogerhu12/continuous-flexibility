import ContinuousFlexibility.Analysis.CoupledConstantFeedbackInverse
import ContinuousFlexibility.Analysis.CoupledInverseRecovery

/-!
# A regular formula for the same recovered coupled inverse

The constant-circle inverse recovers exactly the Banach control mean in
the frozen formula. Injectivity of that mean on constant circle elements
identifies the controls themselves. The regular expression below is thus
equal to the existing guarded recovery on its valid domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem coupled_recovery_map_sub_smul
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (x y : E) (q : ℝ) :
    L (x - q • y) = L x - q • L y := by
  rw [L.map_sub, L.map_smul]

variable {T : MaterialData} {S : PhysicalSpacesData}
variable (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
  (B : ControlColumnData S) (G : ScalarInverseData S)
  (z : AnnularState S × ℝ) (y : ResidualSpace S)

def coupledRecoveryConstantControl : CoupledConstantCircle hM :=
  coupledConstantFeedbackInverse hM B G z (coupledConstantCircleProjection hM
    (y.2.val - z.2 • B.heightRow z (G.G z y.1).1))

def coupledRecoveryHeightFormula : HeightPair S × ℝ :=
  G.G z y.1 - G.G z (B.heightColumn z
    (coupledConstantControlRestriction hM B (coupledRecoveryConstantControl hM B G z y)))

def coupledRecoveryRemainderFormula : CircleSpace S :=
  y.2.val - z.2 • B.heightRow z (coupledRecoveryHeightFormula hM B G z y).1 -
    B.circleColumn z (coupledRecoveryConstantControl hM B G z y).val

def coupledRecoveryRegularFormula (R : ReturnEquationData S) : AnnularState S :=
  ((coupledRecoveryHeightFormula hM B G z y).1,
    ((coupledRecoveryHeightFormula hM B G z y).2,
      ((coupledRecoveryConstantControl hM B G z y).val,
        R.chartIncrement z (R.inverse (coupledRecoveryRemainderFormula hM B G z y)))))

variable
  (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
    angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
  (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
  (hJ : ∀ u, B.JInverse z (B.J z u) = u ∧ B.J z (B.JInverse z u) = u)
  (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
  (hsmall : ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ))

include hrestriction in
theorem coupledConstantFeedbackControl_recoveryInput :
    coupledConstantFeedbackControl hM B G z (coupledConstantCircleProjection hM
      (y.2.val - z.2 • B.heightRow z (G.G z y.1).1)) =
      controlSolution S B G (coupledControlInverse S B G) z y := by
  have hp : coupledConstantControlRestriction hM B (coupledConstantCircleProjection hM
      (y.2.val - z.2 • B.heightRow z (G.G z y.1).1)) =
      B.restriction y.2.val - z.2 • controlMeanRow S B z (G.G z y.1).1 :=
    (coupledConstantControlRestriction_projection hM B hrestriction _).trans
      ((coupled_recovery_map_sub_smul B.restriction.toLinearMap y.2.val
        (B.heightRow z (G.G z y.1).1) z.2).trans
        (congrArg (fun v : ControlBanach => B.restriction y.2.val - z.2 • v)
          (controlMeanRow_apply B z (G.G z y.1).1).symm))
  exact congrArg (fun v : ControlBanach =>
    (coupledControlInverse S B G).inverse z (B.JInverse z v)) hp

include hrestriction hdiag hJ hlo hsmall in
theorem coupledRecoveryConstantControl_mean :
    coupledConstantControlRestriction hM B (coupledRecoveryConstantControl hM B G z y) =
      controlSolution S B G (coupledControlInverse S B G) z y := by
  exact (coupledConstantFeedbackInverse_restriction hM B G z hrestriction hdiag hJ hlo hsmall
    (coupledConstantCircleProjection hM (y.2.val - z.2 • B.heightRow z (G.G z y.1).1))).trans
      (coupledConstantFeedbackControl_recoveryInput hM B G z y hrestriction)

variable (hH : ∀ m, 0 < T.H (T.sample m))

include hrestriction hdiag hJ hlo hsmall hH in
theorem coupledRecoveryConstantControl_eq :
    (coupledRecoveryConstantControl hM B G z y).val =
      coupledRecoveredKappaLinear hM B G (coupledControlInverse S B G) z hlo y := by
  apply controlRestriction_injective_on_constants hM B hrestriction hH
    (coupledConstantCircle_constant hM _)
  · intro m θ φ
    exact coupledInverseControlLift_constant hM (B.diagonal z) hlo _ m θ φ
  · have hnew := coupledRecoveryConstantControl_mean hM B G z y hrestriction hdiag hJ hlo hsmall
    have hold := coupledRecoveredKappaLinear_restriction hM B G (coupledControlInverse S B G)
      z hlo hrestriction hdiag hJ (coupledControlInverse_right B G z hsmall) y
    exact (coupledConstantControlRestriction_apply hM B _).symm.trans (hnew.trans hold.symm)

include hrestriction hdiag hJ hlo hsmall hH in
theorem coupledRecoveryRegularFormula_eq (R : ReturnEquationData S) :
    coupledRecoveryRegularFormula hM B G z y R =
      coupledRecoveryLinear hM R B G (coupledControlInverse S B G) z hlo y := by
  have hmean := coupledRecoveryConstantControl_mean hM B G z y hrestriction hdiag hJ hlo hsmall
  have hκ := coupledRecoveryConstantControl_eq hM B G z y hrestriction hdiag hJ hlo hsmall hH
  have hheight : coupledRecoveryHeightFormula hM B G z y =
      coupledRecoveredHeightLinear B G (coupledControlInverse S B G) z y :=
    (congrArg (fun v : ControlBanach => G.G z y.1 - G.G z (B.heightColumn z v)) hmean).trans
      (coupledRecoveredHeightLinear_apply B G (coupledControlInverse S B G) z y).symm
  have hrem : coupledRecoveryRemainderFormula hM B G z y =
      coupledRecoveryRemainderLinear hM B G (coupledControlInverse S B G) z hlo y :=
    (congrArg₂ (fun (η : HeightPair S × ℝ) (κ : CircleSpace S) =>
      y.2.val - z.2 • B.heightRow z η.1 - B.circleColumn z κ) hheight hκ).trans
      (coupledRecoveryRemainderLinear_apply hM B G (coupledControlInverse S B G) z hlo y).symm
  exact (Prod.ext (congrArg Prod.fst hheight)
    (Prod.ext (congrArg Prod.snd hheight)
      (Prod.ext hκ (congrArg (fun u : CircleSpace S => R.chartIncrement z (R.inverse u)) hrem)))).trans
    (coupledRecoveryLinear_apply hM R B G (coupledControlInverse S B G) z hlo y).symm

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

theorem coupledRecoveryRegularFormula_eq_recoveredV
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : CoupledRecoveryValid S C B G base ε z)
    (y : ResidualSpace S) :
    coupledRecoveryRegularFormula (hS.2.1 (3 / 4 : ℝ)) B G z y R =
      coupledRecoveredV hS h8 z y := by
  have hrestriction : ∀ (u : CircleSpace S) (m : ℕ),
      B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        angularMean ((S.circle (3 / 4 : ℝ)).decode u m) :=
    h8.2.2.2.2.2.1
  have hdiag : ∀ (u : ControlBanach) (m : ℕ), B.J z u m = B.diagonal z m * u m :=
    h8.2.2.2.2.2.2.2.2.2.2.2.2.1 z hz.1 hz.2.1
  have hJ : ∀ u : ControlBanach, B.JInverse z (B.J z u) = u ∧
      B.J z (B.JInverse z u) = u :=
    h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 z hz.1 hz.2.1
  have hH (m : ℕ) : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT h1.1.1.choose_spec.2.1 m)).2.1
  have he := congrArg (fun A : ResidualSpace S →ₗ[ℝ] AnnularState S => A y)
    (coupledRecoveredV_eq hS h8 hz)
  exact (coupledRecoveryRegularFormula_eq (hS.2.1 (3 / 4 : ℝ)) B G z y
    hrestriction hdiag hJ
    (coupledRecovery_diagonal_lower h8 hz.1 hz.2.1) hz.2.2 hH R).trans he.symm

end ContinuousFlexibility.Statements
