import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A coercive closed-energy inverse from Lax-Milgram

An energy space E maps to the physical function space H through U, and
to its energy coordinates through G. Lax-Milgram constructs the inverse
from the bounded form inner(Gv,Gz). A coercive bound in the physical
function norm gives the sharp resolvent bound in H.

The construction assumes neither an inverse nor solvability of the form
equation. A closed physical form supplies E and the norm/coercivity
identities used below.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace

variable {E H Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

def innerGradientForm (G : E →L[ℝ] Z) : E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ E Z ℝ).flip G ∘L
    (innerSL ℝ : Z →L[ℝ] Z →L[ℝ] ℝ) ∘L G

theorem innerGradientForm_apply (G : E →L[ℝ] Z) (v z : E) :
    innerGradientForm G v z = ⟪G v, G z⟫_ℝ := by
  simp only [innerGradientForm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  exact innerSL_apply_apply ℝ (G v) (G z)

/-- Physical coercivity also controls the entire closed energy norm. -/
theorem innerGradientForm_isCoercive (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    {δ : ℝ} (hδ : 0 < δ)
    (hnorm : ∀ v, ‖v‖ ^ 2 = ‖U v‖ ^ 2 + ‖G v‖ ^ 2)
    (hcoerce : ∀ v, δ * ‖U v‖ ^ 2 ≤ ‖G v‖ ^ 2) :
    IsCoercive (innerGradientForm G) := by
  have hden : 0 < 1 + δ := by linarith
  refine ⟨δ / (1 + δ), div_pos hδ hden, ?_⟩
  intro v
  rw [innerGradientForm_apply, real_inner_self_eq_norm_sq,
    mul_assoc, ← pow_two, hnorm, div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hcoerce v]

/-- The solution in the complete energy space, constructed by Riesz and
the coercive bilinear-form equivalence. -/
def innerCoerciveGradientLift (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) : H →L[ℝ] E :=
  (h.continuousLinearEquivOfBilin.symm : E →L[ℝ] E) ∘L U.adjoint

def innerCoerciveGradientInverse (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) : H →L[ℝ] H :=
  U ∘L innerCoerciveGradientLift U G h

theorem innerCoerciveGradientInverse_apply (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) (f : H) :
    innerCoerciveGradientInverse U G h f = U (innerCoerciveGradientLift U G h f) := by
  simp only [innerCoerciveGradientInverse, ContinuousLinearMap.comp_apply]

theorem innerCoerciveGradientLift_equation (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) (f : H) (z : E) :
    ⟪f, U z⟫_ℝ =
      ⟪G (innerCoerciveGradientLift U G h f), G z⟫_ℝ := by
  have he : h.continuousLinearEquivOfBilin (innerCoerciveGradientLift U G h f) =
      U.adjoint f := by
    simp only [innerCoerciveGradientLift, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  have hh := h.continuousLinearEquivOfBilin_apply
    (innerCoerciveGradientLift U G h f) z
  rw [he, ContinuousLinearMap.adjoint_inner_left, innerGradientForm_apply] at hh
  exact hh

/-- The actual form graph associated to a function embedding and its
energy coordinates. -/
def InnerGradientGraph (U : E →L[ℝ] H) (G : E →L[ℝ] Z) (u f : H) : Prop :=
  ∃ v : E, U v = u ∧ ∀ z : E, ⟪f, U z⟫_ℝ = ⟪G v, G z⟫_ℝ

theorem innerCoerciveGradientInverse_graph (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) (f : H) :
    InnerGradientGraph U G (innerCoerciveGradientInverse U G h f) f :=
  ⟨innerCoerciveGradientLift U G h f,
    (innerCoerciveGradientInverse_apply U G h f).symm,
    innerCoerciveGradientLift_equation U G h f⟩

/-- Both directions of the inverse relation include the closed form
domain, not just an interior differential expression. -/
theorem innerGradientGraph_iff_inverse (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) (u f : H) :
    InnerGradientGraph U G u f ↔ innerCoerciveGradientInverse U G h f = u := by
  constructor
  · rintro ⟨v, hv, hform⟩
    have he : U.adjoint f = h.continuousLinearEquivOfBilin v := by
      apply h.unique_continuousLinearEquivOfBilin
      intro z
      rw [ContinuousLinearMap.adjoint_inner_left, innerGradientForm_apply]
      exact hform z
    rw [innerCoerciveGradientInverse_apply]
    have hv' : innerCoerciveGradientLift U G h f = v := by
      simp only [innerCoerciveGradientLift, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, he, ContinuousLinearEquiv.symm_apply_apply]
    rw [hv', hv]
  · intro he
    rw [← he]
    exact innerCoerciveGradientInverse_graph U G h f

theorem innerCoerciveGradientInverse_energy (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) (f : H) :
    ⟪f, innerCoerciveGradientInverse U G h f⟫_ℝ =
      ‖G (innerCoerciveGradientLift U G h f)‖ ^ 2 := by
  rw [innerCoerciveGradientInverse_apply,
    innerCoerciveGradientLift_equation U G h f, real_inner_self_eq_norm_sq]

theorem innerCoerciveGradientInverse_isSymmetric (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) :
    (innerCoerciveGradientInverse U G h).IsSymmetric := by
  intro f g
  simp only [ContinuousLinearMap.coe_coe]
  rw [innerCoerciveGradientInverse_apply, innerCoerciveGradientInverse_apply]
  calc
    _ = ⟪g, U (innerCoerciveGradientLift U G h f)⟫_ℝ := real_inner_comm _ _
    _ = ⟪G (innerCoerciveGradientLift U G h g),
        G (innerCoerciveGradientLift U G h f)⟫_ℝ :=
      innerCoerciveGradientLift_equation U G h g _
    _ = ⟪G (innerCoerciveGradientLift U G h f),
        G (innerCoerciveGradientLift U G h g)⟫_ℝ := real_inner_comm _ _
    _ = _ := (innerCoerciveGradientLift_equation U G h f _).symm

/-- Physical coercivity gives the sharp inverse frequency scale. -/
theorem innerCoerciveGradientInverse_norm_le (U : E →L[ℝ] H) (G : E →L[ℝ] Z)
    (h : IsCoercive (innerGradientForm G)) {δ : ℝ} (hδ : 0 < δ)
    (hcoerce : ∀ v, δ * ‖U v‖ ^ 2 ≤ ‖G v‖ ^ 2) :
    ‖innerCoerciveGradientInverse U G h‖ ≤ δ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hδ.le)
  intro f
  have he := innerCoerciveGradientInverse_energy U G h f
  have hc := hcoerce (innerCoerciveGradientLift U G h f)
  rw [← innerCoerciveGradientInverse_apply] at hc
  rw [← he] at hc
  have hb := hc.trans (real_inner_le_norm f (innerCoerciveGradientInverse U G h f))
  by_cases hz : ‖innerCoerciveGradientInverse U G h f‖ = 0
  · rw [hz]
    exact mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg _)
  have hp : 0 < ‖innerCoerciveGradientInverse U G h f‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hcancel : δ * ‖innerCoerciveGradientInverse U G h f‖ ≤ ‖f‖ :=
    (mul_le_mul_iff_right₀ hp).mp (by nlinarith only [hb])
  calc
    _ ≤ ‖f‖ / δ := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hcancel)
    _ = δ⁻¹ * ‖f‖ := by ring

end ContinuousFlexibility.Radial
