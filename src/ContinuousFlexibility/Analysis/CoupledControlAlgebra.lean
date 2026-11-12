import ContinuousFlexibility.Analysis.NeumannPackage
import ContinuousFlexibility.Statements.Nonlinear

/-!
# The control Neumann inverse and the coupled mean equation

The inverse is formed on the existing control Banach space.  Its two-sided
identities are applications of the Neumann package.  The remaining lemmas
perform the elimination in the original coupled formulas: a recovered
control with the prescribed weighted mean leaves a zero-mean circle source.
No smallness or regularity of the parameter family is assumed here beyond
the explicit pointwise hypotheses of the individual algebraic lemmas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

section Neumann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A total choice of the inverse of `1 - A`, using the actual Neumann
inverse wherever its norm criterion holds. -/
def coupledNeumannInverse (A : E →L[ℝ] E) : E →L[ℝ] E :=
  if hA : ‖A‖ < 1 then
    neumannInverse (-A) (by simpa only [norm_neg] using hA)
  else 0

theorem coupledNeumannInverse_eq (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    coupledNeumannInverse A =
      neumannInverse (-A) (by simpa only [norm_neg] using hA) := by
  simp only [coupledNeumannInverse, dif_pos hA]

theorem coupledNeumannInverse_apply_sub (A : E →L[ℝ] E)
    (hA : ‖A‖ < 1) (u : E) :
    coupledNeumannInverse A (u - A u) = u := by
  rw [coupledNeumannInverse_eq A hA]
  simpa only [ContinuousLinearMap.neg_apply, sub_eq_add_neg] using
    neumannInverse_apply_add (-A) (by simpa only [norm_neg] using hA) u

theorem coupledNeumannInverse_sub_apply (A : E →L[ℝ] E)
    (hA : ‖A‖ < 1) (u : E) :
    coupledNeumannInverse A u - A (coupledNeumannInverse A u) = u := by
  rw [coupledNeumannInverse_eq A hA]
  simpa only [ContinuousLinearMap.neg_apply, sub_eq_add_neg] using
    neumannInverse_add_apply (-A) (by simpa only [norm_neg] using hA) u

theorem coupledNeumannInverse_norm_le_two (A : E →L[ℝ] E)
    (hA : ‖A‖ < (1 / 2 : ℝ)) : ‖coupledNeumannInverse A‖ ≤ 2 := by
  have hAone : ‖A‖ < 1 := hA.trans (by norm_num)
  rw [coupledNeumannInverse_eq A hAone]
  exact norm_neumannInverse_le_two (-A)
    (by simpa only [norm_neg] using hAone)
    (by simpa only [norm_neg] using hA.le)

end Neumann

section Elimination

variable {E F Y : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup Y] [Module ℝ Y]

/-- Apply the genuine diagonal operator to the feedback equation before
recovering the height increment. -/
theorem coupledControl_elimination
    (J I : E →ₗ[ℝ] E) (R : F →ₗ[ℝ] E) (U : E →ₗ[ℝ] F)
    (hJI : ∀ v, J (I v) = v) (q : ℝ) (ξ b : E) (h : F)
    (hξ : ξ - q • I (R (U ξ)) = I (b - q • R h)) :
    J ξ + q • R (h - U ξ) = b := by
  have hJ := congrArg J hξ
  simp only [map_sub, map_smul, hJI] at hJ
  calc
    J ξ + q • R (h - U ξ) = (J ξ - q • R (U ξ)) + q • R h := by
      rw [map_sub, smul_sub]
      abel
    _ = (b - q • R h) + q • R h := congrArg (fun v => v + q • R h) hJ
    _ = b := sub_add_cancel _ _

/-- The mean equation cancels the mean of the remaining circle source. -/
theorem coupledControl_remainder_zero
    (ρ : Y →ₗ[ℝ] E) (H : F →ₗ[ℝ] Y) (D : Y →ₗ[ℝ] Y) (J : E →ₗ[ℝ] E)
    (hD : ∀ κ, ρ (D κ) = J (ρ κ))
    (q : ℝ) (g κ : Y) (η : F) (ξ : E)
    (hκ : ρ κ = ξ) (hmean : J ξ + q • ρ (H η) = ρ g) :
    ρ (g - q • H η - D κ) = 0 := by
  rw [map_sub, map_sub, map_smul, hD, hκ, ← hmean]
  abel

end Elimination

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData}

theorem controlHeightResponse_apply (B : ControlColumnData S) (G : ScalarInverseData S)
    (z : AnnularState S × ℝ) (u : ControlBanach) :
    controlHeightResponse S B G z u = (G.G z (B.heightColumn z u)).1 := by
  simp only [controlHeightResponse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst']

theorem controlMeanRow_apply (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (η : HeightPair S) :
    controlMeanRow S B z η = B.restriction (B.heightRow z η) := by
  simp only [controlMeanRow, ContinuousLinearMap.comp_apply]

theorem controlFeedback_apply (B : ControlColumnData S) (G : ScalarInverseData S)
    (z : AnnularState S × ℝ) (u : ControlBanach) :
    controlFeedback S B G z u =
      B.JInverse z (controlMeanRow S B z (controlHeightResponse S B G z u)) := by
  simp only [controlFeedback, ContinuousLinearMap.comp_apply]

/-- The second inverse acts on the same control space as the feedback. -/
def coupledControlInverse (S : PhysicalSpacesData) (B : ControlColumnData S)
    (G : ScalarInverseData S) : ControlInverseData S where
  inverse z := coupledNeumannInverse (z.2 • controlFeedback S B G z)

theorem coupledControlInverse_left (B : ControlColumnData S) (G : ScalarInverseData S)
    (z : AnnularState S × ℝ)
    (hsmall : ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ)) (u : ControlBanach) :
    (coupledControlInverse S B G).inverse z
      (u - z.2 • controlFeedback S B G z u) = u := by
  simpa only [coupledControlInverse, ContinuousLinearMap.smul_apply] using
    coupledNeumannInverse_apply_sub (z.2 • controlFeedback S B G z)
      (hsmall.trans (by norm_num)) u

theorem coupledControlInverse_right (B : ControlColumnData S) (G : ScalarInverseData S)
    (z : AnnularState S × ℝ)
    (hsmall : ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ)) (u : ControlBanach) :
    (coupledControlInverse S B G).inverse z u - z.2 • controlFeedback S B G z
      ((coupledControlInverse S B G).inverse z u) = u := by
  simpa only [coupledControlInverse, ContinuousLinearMap.smul_apply] using
    coupledNeumannInverse_sub_apply (z.2 • controlFeedback S B G z)
      (hsmall.trans (by norm_num)) u

theorem coupledControlInverse_norm_le_two (B : ControlColumnData S) (G : ScalarInverseData S)
    (z : AnnularState S × ℝ)
    (hsmall : ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ)) :
    ‖(coupledControlInverse S B G).inverse z‖ ≤ 2 :=
  coupledNeumannInverse_norm_le_two (z.2 • controlFeedback S B G z) hsmall

theorem controlSolution_sub_feedback
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ)
    (hN : ∀ u, N.inverse z u - z.2 • controlFeedback S B G z (N.inverse z u) = u)
    (y : ResidualSpace S) :
    controlSolution S B G N z y - z.2 • controlFeedback S B G z
      (controlSolution S B G N z y) =
        B.JInverse z (B.restriction y.2.val -
          z.2 • controlMeanRow S B z (G.G z y.1).1) :=
  hN _

theorem controlSolution_fixedPoint
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ)
    (hN : ∀ u, N.inverse z u - z.2 • controlFeedback S B G z (N.inverse z u) = u)
    (y : ResidualSpace S) :
    controlSolution S B G N z y =
      B.JInverse z (B.restriction y.2.val -
        z.2 • controlMeanRow S B z (G.G z y.1).1) +
      z.2 • controlFeedback S B G z (controlSolution S B G N z y) :=
  (sub_eq_iff_eq_add).mp (controlSolution_sub_feedback B G N z hN y)

theorem controlSolution_mean_equation
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ)
    (hN : ∀ u, N.inverse z u - z.2 • controlFeedback S B G z (N.inverse z u) = u)
    (hJ : ∀ u, B.J z (B.JInverse z u) = u) (y : ResidualSpace S) :
    B.J z (controlSolution S B G N z y) + z.2 • controlMeanRow S B z
      ((G.G z y.1).1 - controlHeightResponse S B G z (controlSolution S B G N z y)) =
        B.restriction y.2.val := by
  have hξ := controlSolution_sub_feedback B G N z hN y
  have hξ' := (congrArg
    (fun v : ControlBanach => controlSolution S B G N z y - z.2 • v)
    (controlFeedback_apply B G z (controlSolution S B G N z y))).symm.trans hξ
  exact coupledControl_elimination (B.J z).toLinearMap (B.JInverse z).toLinearMap
    (controlMeanRow S B z).toLinearMap (controlHeightResponse S B G z).toLinearMap
    hJ z.2 (controlSolution S B G N z y) (B.restriction y.2.val) (G.G z y.1).1 hξ'

theorem controlSolution_restriction_remainder
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ)
    (hN : ∀ u, N.inverse z u - z.2 • controlFeedback S B G z (N.inverse z u) = u)
    (hJ : ∀ u, B.J z (B.JInverse z u) = u)
    (hcolumn : ∀ κ, B.restriction (B.circleColumn z κ) = B.J z (B.restriction κ))
    (y : ResidualSpace S) (η : HeightPair S) (κ : CircleSpace S)
    (hη : η = (G.G z y.1).1 -
      controlHeightResponse S B G z (controlSolution S B G N z y))
    (hκ : B.restriction κ = controlSolution S B G N z y) :
    B.restriction (y.2.val - z.2 • B.heightRow z η - B.circleColumn z κ) = 0 := by
  have hmean : B.J z (controlSolution S B G N z y) +
      z.2 • controlMeanRow S B z η = B.restriction y.2.val :=
    (congrArg (fun h => B.J z (controlSolution S B G N z y) +
      z.2 • controlMeanRow S B z h) hη).trans
        (controlSolution_mean_equation B G N z hN hJ y)
  have hmean' := (congrArg
    (fun v : ControlBanach => B.J z (controlSolution S B G N z y) + z.2 • v)
    (controlMeanRow_apply B z η)).symm.trans hmean
  exact coupledControl_remainder_zero B.restriction.toLinearMap
    (B.heightRow z).toLinearMap (B.circleColumn z).toLinearMap (B.J z).toLinearMap
    hcolumn z.2 y.2.val κ η (controlSolution S B G N z y) hκ hmean'

/-- The stored inverse has the reciprocal coordinates of the stored
diagonal operator; this follows from the actual right inverse identity. -/
theorem controlJInverse_apply_of_diagonal
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.J z (B.JInverse z u) = u)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
    (u : ControlBanach) (m : ℕ) :
    B.JInverse z u m = (B.diagonal z m)⁻¹ * u m := by
  have hne : B.diagonal z m ≠ 0 :=
    abs_pos.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hlo m))
  have hp : B.diagonal z m * B.JInverse z u m = u m :=
    (hdiag (B.JInverse z u) m).symm.trans
      (congrArg (fun v : ControlBanach => v m) (hJ u))
  calc
    B.JInverse z u m = (B.diagonal z m)⁻¹ *
        (B.diagonal z m * B.JInverse z u m) := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = (B.diagonal z m)⁻¹ * u m := congrArg (fun a : ℝ => (B.diagonal z m)⁻¹ * a) hp

theorem controlRestriction_mean_zero
    {T : MaterialData} (B : ControlColumnData S)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hH : ∀ m, 0 < T.H (T.sample m)) {u : CircleSpace S}
    (hu : B.restriction u = 0) (m : ℕ) :
    angularMean ((S.circle (3 / 4 : ℝ)).decode u m) = 0 := by
  have hz : B.restriction u m = 0 := by
    simpa only [lp.coeFn_zero, Pi.zero_apply] using
      congrArg (fun v : ControlBanach => v m) hu
  have hp := (hrestriction u m).symm.trans hz
  exact (mul_eq_zero.mp hp).resolve_left (Real.rpow_pos_of_pos (hH m) _).ne'

end ContinuousFlexibility.Statements
