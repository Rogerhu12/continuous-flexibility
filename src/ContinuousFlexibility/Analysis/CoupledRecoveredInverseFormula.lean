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

theorem coupledConstantFeedbackControl_recoveryInput :
    coupledConstantFeedbackControl hM B G z (coupledConstantCircleProjection hM
      (y.2.val - z.2 • B.heightRow z (G.G z y.1).1)) =
      controlSolution S B G (coupledControlInverse S B G) z y := by
  rw [coupledConstantFeedbackControl_apply hM B G z,
    coupledConstantControlRestriction_projection hM B hrestriction,
    map_sub, map_smul, controlSolution]
  exact congrArg
    (fun v : ControlBanach => (coupledControlInverse S B G).inverse z
      (B.JInverse z (B.restriction y.2.val - z.2 • v)))
    (controlMeanRow_apply B z (G.G z y.1).1).symm

theorem coupledRecoveryConstantControl_mean :
    coupledConstantControlRestriction hM B (coupledRecoveryConstantControl hM B G z y) =
      controlSolution S B G (coupledControlInverse S B G) z y := by
  exact (coupledConstantFeedbackInverse_restriction hM B G z hrestriction hdiag hJ hlo hsmall
    (coupledConstantCircleProjection hM (y.2.val - z.2 • B.heightRow z (G.G z y.1).1))).trans
      (coupledConstantFeedbackControl_recoveryInput hM B G z y hrestriction)

variable (hH : ∀ m, 0 < T.H (T.sample m))

theorem coupledRecoveryConstantControl_eq :
    (coupledRecoveryConstantControl hM B G z y).val =
      coupledRecoveredKappaLinear hM B G (coupledControlInverse S B G) z hlo y := by
  apply controlRestriction_injective_on_constants hM B hrestriction hH
    (coupledConstantCircle_constant hM _)
  · intro m θ φ
    rw [coupledRecoveredKappaLinear_apply hM B G (coupledControlInverse S B G) z hlo y]
    exact coupledInverseControlLift_constant hM (B.diagonal z) hlo _ m θ φ
  · have hnew := coupledRecoveryConstantControl_mean hM B G z y hrestriction hdiag hJ hlo hsmall
    have hold := coupledRecoveredKappaLinear_restriction hM B G (coupledControlInverse S B G)
      z hlo hrestriction hdiag hJ (coupledControlInverse_right B G z hsmall) y
    exact (coupledConstantControlRestriction_apply hM B _).symm.trans (hnew.trans hold.symm)

theorem coupledRecoveryRegularFormula_eq (R : ReturnEquationData S) :
    coupledRecoveryRegularFormula hM B G z y R =
      coupledRecoveryLinear hM R B G (coupledControlInverse S B G) z hlo y := by
  have hmean := coupledRecoveryConstantControl_mean hM B G z y hrestriction hdiag hJ hlo hsmall
  have hκ := coupledRecoveryConstantControl_eq hM B G z y hrestriction hdiag hJ hlo hsmall hH
  have hheight : coupledRecoveryHeightFormula hM B G z y =
      coupledRecoveredHeightLinear B G (coupledControlInverse S B G) z y := by
    rw [coupledRecoveryHeightFormula, hmean,
      coupledRecoveredHeightLinear_apply B G (coupledControlInverse S B G) z y]
  rw [coupledRecoveryRegularFormula,
    coupledRecoveryLinear_apply hM R B G (coupledControlInverse S B G) z hlo y]
  apply Prod.ext (congrArg Prod.fst hheight)
  apply Prod.ext (congrArg Prod.snd hheight)
  apply Prod.ext hκ
  apply congrArg (fun u : CircleSpace S => R.chartIncrement z (R.inverse u))
  rw [coupledRecoveryRemainderFormula, hheight, hκ,
    coupledRecoveryRemainderLinear_apply hM B G (coupledControlInverse S B G) z hlo y]

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
  have h8' := h8
  obtain ⟨_, _, _, _, _, hrestriction, _, _, _, _, _, _, hdiag, _, hJ, _⟩ := h8'
  have hH (m : ℕ) : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT h1.1.1.choose_spec.2.1 m)).2.1
  rw [coupledRecoveredV_eq hS h8 hz]
  exact coupledRecoveryRegularFormula_eq (hS.2.1 (3 / 4 : ℝ)) B G z y
    hrestriction (hdiag z hz.1 hz.2.1) (hJ z hz.1 hz.2.1)
    (coupledRecovery_diagonal_lower h8 hz.1 hz.2.1) hz.2.2 hH R

end ContinuousFlexibility.Statements
