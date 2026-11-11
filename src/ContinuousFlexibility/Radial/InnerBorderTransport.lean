import ContinuousFlexibility.Radial.InnerDisjointPieces
import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Transport from the inner Hilbert source to the stated mode pair

`InnerBorderL2 μ` is the Hilbert source used for adjoints and orthogonal
assembly. The statement-layer product uses its usual maximum norm. The
existing `WithLp` equivalence identifies their vectors and scalar border
exactly, with norm comparison constants `1` and `sqrt 2`.

Conjugating an operator by this fixed equivalence preserves its equations
and its Green pairing. No differential graph or final reference column is
introduced here, so the same transport applies to the temporary inner
border as well as to the final mode-pair representation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α]

/-- The existing `WithLp` equivalence, specialized to the actual bordered
source. It changes the norm and preserves both coordinates. -/
def innerBorderMaxEquiv (μ : Measure α) :
    InnerBorderL2 μ ≃L[ℝ] (Lp ℝ 2 μ × ℝ) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 μ) ℝ

theorem innerBorderMaxEquiv_apply (μ : Measure α) (u : InnerBorderL2 μ) :
    innerBorderMaxEquiv μ u = WithLp.ofLp u := by
  simp only [innerBorderMaxEquiv, WithLp.prodContinuousLinearEquiv_apply]

theorem innerBorderMaxEquiv_symm_apply (μ : Measure α) (u : Lp ℝ 2 μ × ℝ) :
    (innerBorderMaxEquiv μ).symm u = WithLp.toLp 2 u := by
  simp only [innerBorderMaxEquiv, WithLp.prodContinuousLinearEquiv_symm_apply]

/-- The ordinary product norm is bounded by the Hilbert norm. -/
theorem innerBorder_ofLp_norm_le {μ : Measure α} (u : InnerBorderL2 μ) :
    ‖WithLp.ofLp u‖ ≤ ‖u‖ := by
  rw [Prod.norm_def, WithLp.ofLp_fst, WithLp.ofLp_snd]
  exact max_le (WithLp.norm_fst_le u) (WithLp.norm_snd_le u)

/-- Passing to the Hilbert product costs at most `sqrt 2`, independently
of the physical measure or the number of inner pieces. -/
theorem innerBorder_norm_le_sqrt_two_mul {μ : Measure α} (u : InnerBorderL2 μ) :
    ‖u‖ ≤ Real.sqrt 2 * ‖WithLp.ofLp u‖ := by
  have hf : ‖u.fst‖ ≤ ‖WithLp.ofLp u‖ := by
    rw [Prod.norm_def, WithLp.ofLp_fst, WithLp.ofLp_snd]
    exact le_max_left _ _
  have hs : ‖u.snd‖ ≤ ‖WithLp.ofLp u‖ := by
    rw [Prod.norm_def, WithLp.ofLp_fst, WithLp.ofLp_snd]
    exact le_max_right _ _
  apply (sq_le_sq₀ (norm_nonneg u)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    ‖u.fst‖ ^ 2 + ‖u.snd‖ ^ 2 ≤
        ‖WithLp.ofLp u‖ ^ 2 + ‖WithLp.ofLp u‖ ^ 2 :=
      add_le_add ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hf)
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hs)
    _ = 2 * ‖WithLp.ofLp u‖ ^ 2 := by ring

theorem norm_innerBorderMaxEquiv_le_one (μ : Measure α) :
    ‖(innerBorderMaxEquiv μ : InnerBorderL2 μ →L[ℝ] (Lp ℝ 2 μ × ℝ))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [ContinuousLinearEquiv.coe_coe, innerBorderMaxEquiv_apply, one_mul] using
    innerBorder_ofLp_norm_le u

theorem norm_innerBorderMaxEquiv_symm_le_sqrt_two (μ : Measure α) :
    ‖((innerBorderMaxEquiv μ).symm : (Lp ℝ 2 μ × ℝ) →L[ℝ] InnerBorderL2 μ)‖ ≤
      Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2)
  intro u
  simpa only [ContinuousLinearEquiv.coe_coe, innerBorderMaxEquiv_symm_apply,
    WithLp.ofLp_toLp] using innerBorder_norm_le_sqrt_two_mul (WithLp.toLp 2 u)

/-- One Hilbert-space operator expressed in the ordinary mode-pair norm. -/
def innerBorderToMaxOperator (μ : Measure α)
    (G : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) :
    (Lp ℝ 2 μ × ℝ) →L[ℝ] (Lp ℝ 2 μ × ℝ) :=
  (innerBorderMaxEquiv μ : InnerBorderL2 μ →L[ℝ] (Lp ℝ 2 μ × ℝ)) ∘L G ∘L
    ((innerBorderMaxEquiv μ).symm : (Lp ℝ 2 μ × ℝ) →L[ℝ] InnerBorderL2 μ)

theorem innerBorderToMaxOperator_apply (μ : Measure α)
    (G : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) (F : Lp ℝ 2 μ × ℝ) :
    innerBorderToMaxOperator μ G F = WithLp.ofLp (G (WithLp.toLp 2 F)) := by
  simp only [innerBorderToMaxOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, innerBorderMaxEquiv_apply,
    innerBorderMaxEquiv_symm_apply]

theorem innerBorderToMaxOperator_toLp (μ : Measure α)
    (G : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) (F : Lp ℝ 2 μ × ℝ) :
    WithLp.toLp 2 (innerBorderToMaxOperator μ G F) = G (WithLp.toLp 2 F) := by
  rw [innerBorderToMaxOperator_apply, WithLp.toLp_ofLp]

/-- The equation defining the inverse graph is unchanged under transport. -/
theorem innerBorderToMaxOperator_eq_iff (μ : Measure α)
    (G : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) (F U : Lp ℝ 2 μ × ℝ) :
    innerBorderToMaxOperator μ G F = U ↔ G (WithLp.toLp 2 F) = WithLp.toLp 2 U := by
  rw [innerBorderToMaxOperator_apply]
  constructor
  · intro h
    simpa only [WithLp.toLp_ofLp] using congrArg (WithLp.toLp 2) h
  · intro h
    simpa only [WithLp.ofLp_toLp] using congrArg WithLp.ofLp h

/-- Composition, hence either inverse identity and either weight
conjugation, transports exactly. -/
theorem innerBorderToMaxOperator_comp (μ : Measure α)
    (A B : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) :
    innerBorderToMaxOperator μ (A ∘L B) =
      innerBorderToMaxOperator μ A ∘L innerBorderToMaxOperator μ B := by
  ext F
  simp only [innerBorderToMaxOperator_apply, ContinuousLinearMap.comp_apply,
    WithLp.toLp_ofLp]

theorem innerBorderToMaxOperator_id (μ : Measure α) :
    innerBorderToMaxOperator μ (ContinuousLinearMap.id ℝ (InnerBorderL2 μ)) =
      ContinuousLinearMap.id ℝ (Lp ℝ 2 μ × ℝ) := by
  ext F
  simp only [innerBorderToMaxOperator_apply, ContinuousLinearMap.id_apply, WithLp.ofLp_toLp]

/-- A fixed norm-equivalence constant is the only cost of expressing a
Hilbert operator in the mode-pair norm. -/
theorem norm_innerBorderToMaxOperator_le (μ : Measure α)
    (G : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) :
    ‖innerBorderToMaxOperator μ G‖ ≤ Real.sqrt 2 * ‖G‖ := by
  unfold innerBorderToMaxOperator
  calc
    _ ≤ ‖(innerBorderMaxEquiv μ : InnerBorderL2 μ →L[ℝ] (Lp ℝ 2 μ × ℝ))‖ *
        (‖G‖ * ‖((innerBorderMaxEquiv μ).symm :
          (Lp ℝ 2 μ × ℝ) →L[ℝ] InnerBorderL2 μ)‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖G‖ * Real.sqrt 2) :=
      mul_le_mul (norm_innerBorderMaxEquiv_le_one μ)
        (mul_le_mul_of_nonneg_left (norm_innerBorderMaxEquiv_symm_le_sqrt_two μ) (norm_nonneg G))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = Real.sqrt 2 * ‖G‖ := by ring

/-- The actual pairwise bilinear form is the Hilbert inner product, even
though the ordinary product carries a different norm. -/
theorem innerBorder_toLp_inner (μ : Measure α) (U F : Lp ℝ 2 μ × ℝ) :
    ⟪(WithLp.toLp 2 U : InnerBorderL2 μ), WithLp.toLp 2 F⟫_ℝ =
      ⟪U.1, F.1⟫_ℝ + U.2 * F.2 := by
  rcases U with ⟨u, c⟩
  rcases F with ⟨f, d⟩
  exact innerBorderL2_inner u f c d

theorem innerBorderToMaxOperator_green (μ : Measure α)
    (G : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) (hG : IsSelfAdjoint G)
    (U F : Lp ℝ 2 μ × ℝ) :
    ⟪(innerBorderToMaxOperator μ G U).1, F.1⟫_ℝ +
        (innerBorderToMaxOperator μ G U).2 * F.2 =
      ⟪U.1, (innerBorderToMaxOperator μ G F).1⟫_ℝ +
        U.2 * (innerBorderToMaxOperator μ G F).2 := by
  have h : ⟪G (WithLp.toLp 2 U), WithLp.toLp 2 F⟫_ℝ =
      ⟪WithLp.toLp 2 U, G (WithLp.toLp 2 F)⟫_ℝ := hG.isSymmetric _ _
  rw [← innerBorderToMaxOperator_toLp μ G U,
    ← innerBorderToMaxOperator_toLp μ G F] at h
  simpa only [innerBorder_toLp_inner] using h

/-- In particular this is exactly the existing statement-layer pairing,
without any change to the source measure or the scalar coordinate. -/
theorem innerBorderL2_modePairing (D : Statements.ReferenceData)
    (U F : Statements.RadialModePair D) :
    ⟪(WithLp.toLp 2 U : InnerBorderL2 (Statements.radialHilbertMeasure D)),
      WithLp.toLp 2 F⟫_ℝ = Statements.modePairing D U F := by
  simpa only [Statements.modePairing] using
    innerBorder_toLp_inner (Statements.radialHilbertMeasure D) U F

end ContinuousFlexibility.Radial
