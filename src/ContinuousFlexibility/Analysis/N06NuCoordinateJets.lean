module

public import ContinuousFlexibility.Analysis.N06NuFiniteSmooth
public import ContinuousFlexibility.Analysis.N06StateHeightJetBounds
public import ContinuousFlexibility.Analysis.SpacesTorusWaves

/-!
# Actual angular jets of the finite nu coordinates

The five height entries are the original polar derivatives. Their angular
jets are expressed in ordinary mixed derivatives of the same stateU, so
the fixed original seminorm estimates apply without a smooth-source or
independent-jet replacement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff

private theorem n06_partial_radial_smooth {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (radialPartial u) :=
  hu.fderiv_right (by simp) |>.clm_apply contDiff_const

private theorem n06_partial_angular_smooth {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (angularPartial u) :=
  hu.fderiv_right (by simp) |>.clm_apply contDiff_const

private theorem n06_slice_smooth {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (r : ℝ) : ContDiff ℝ ∞ (fun θ => u (r, θ)) :=
  hu.comp (contDiff_const.prodMk contDiff_id)

theorem n06_radial_heightAngular_formula {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) {p : PolarPoint} (hr : p.1 ≠ 0) :
    radialPartial (heightAngular u) p =
      (1 / p.1) * angularPartial (radialPartial u) p -
        (1 / p.1 ^ 2) * angularPartial u p := by
  have h := height_compatibility (hu.contDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) hr
  change p.1 * radialPartial (heightAngular u) p =
    angularPartial (radialPartial u) p - angularPartial u p / p.1 at h
  field_simp [hr] at h ⊢
  nlinarith only [h]

/-- Every angular jet uses only physical mixed derivatives of order at
most j+2, with the fixed coefficients 1/r and 1/r². -/
theorem n06_nuHeight_angularJet_formulas {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) {r : ℝ} (hr : r ≠ 0) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun t => radialPartial u (r, t)) θ =
        mixedDerivative 1 j u (r, θ) ∧
    iteratedDeriv j (fun t => radialPartial (radialPartial u) (r, t)) θ =
        mixedDerivative 2 j u (r, θ) ∧
    iteratedDeriv j (fun t => heightAngular u (r, t)) θ =
        (1 / r) * mixedDerivative 0 (j + 1) u (r, θ) ∧
    iteratedDeriv j (fun t => radialPartial (heightAngular u) (r, t)) θ =
        (1 / r) * mixedDerivative 1 (j + 1) u (r, θ) -
          (1 / r ^ 2) * mixedDerivative 0 (j + 1) u (r, θ) ∧
    iteratedDeriv j (fun t => angularPartial (heightAngular u) (r, t)) θ =
        (1 / r) * mixedDerivative 0 (j + 2) u (r, θ) := by
  have hur := n06_partial_radial_smooth hu
  have hut := n06_partial_angular_smooth hu
  have hurt := n06_partial_angular_smooth hur
  have hutt := n06_partial_angular_smooth hut
  have hrad : iteratedDeriv j (fun t => radialPartial u (r, t)) θ =
      mixedDerivative 1 j u (r, θ) := by
    change mixedDerivative 0 j (radialPartial u) (r, θ) = _
    exact mixedDerivative_radialPartial isOpen_univ hu.contDiffOn 0 j (mem_univ (r, θ))
  have hrad₂ : iteratedDeriv j (fun t => radialPartial (radialPartial u) (r, t)) θ =
      mixedDerivative 2 j u (r, θ) := by
    change mixedDerivative 0 j (radialPartial (radialPartial u)) (r, θ) = _
    rw [mixedDerivative_radialPartial isOpen_univ hur.contDiffOn 0 j (mem_univ _),
      mixedDerivative_radialPartial isOpen_univ hu.contDiffOn 1 j (mem_univ _)]
  have hθ : iteratedDeriv j (fun t => angularPartial u (r, t)) θ =
      mixedDerivative 0 (j + 1) u (r, θ) := by
    change mixedDerivative 0 j (angularPartial u) (r, θ) = _
    exact mixedDerivative_angularPartial isOpen_univ hu.contDiffOn 0 j (mem_univ (r, θ))
  have hrθ : iteratedDeriv j (fun t => angularPartial (radialPartial u) (r, t)) θ =
      mixedDerivative 1 (j + 1) u (r, θ) := by
    change mixedDerivative 0 j (angularPartial (radialPartial u)) (r, θ) = _
    rw [mixedDerivative_angularPartial isOpen_univ hur.contDiffOn 0 j (mem_univ _),
      mixedDerivative_radialPartial isOpen_univ hu.contDiffOn 0 (j + 1) (mem_univ _)]
  have hθθ : iteratedDeriv j (fun t => angularPartial (angularPartial u) (r, t)) θ =
      mixedDerivative 0 (j + 2) u (r, θ) := by
    change mixedDerivative 0 j (angularPartial (angularPartial u)) (r, θ) = _
    rw [mixedDerivative_angularPartial isOpen_univ hut.contDiffOn 0 j (mem_univ _),
      mixedDerivative_angularPartial isOpen_univ hu.contDiffOn 0 (j + 1) (mem_univ _)]
  refine ⟨hrad, hrad₂, ?_, ?_, ?_⟩
  · have he : (fun t => heightAngular u (r, t)) =
        (fun t => (1 / r) * angularPartial u (r, t)) := by
      funext t
      simp only [heightAngular, div_eq_mul_inv, one_mul, mul_one, mul_comm]
    rw [he, iteratedDeriv_const_mul_field, hθ]
  · have he : (fun t => radialPartial (heightAngular u) (r, t)) =
        (fun t => (1 / r) * angularPartial (radialPartial u) (r, t) -
          (1 / r ^ 2) * angularPartial u (r, t)) :=
      funext fun t => n06_radial_heightAngular_formula hu hr
    rw [he, iteratedDeriv_fun_sub
      ((contDiff_const.mul (n06_slice_smooth hurt r)).contDiffAt.of_le (by simp))
      ((contDiff_const.mul (n06_slice_smooth hut r)).contDiffAt.of_le (by simp)),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, hrθ, hθ]
  · have he : (fun t => angularPartial (heightAngular u) (r, t)) =
        (fun t => (1 / r) * angularPartial (angularPartial u) (r, t)) := by
      funext t
      rw [angularPartial_heightAngular_eq hu hr]
      ring
    rw [he, iteratedDeriv_const_mul_field, hθθ]

theorem n06_actualNuJetCoordinates_angular_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiff ℝ ∞ (fun θ => n06ActualNuJetCoordinates D S z (r, θ)) := by
  have hu := neighborhood_stateU_contDiff hT hS z.1
  have hur := n06_partial_radial_smooth hu
  have hut := n06_partial_angular_smooth hu
  have hrr := n06_slice_smooth (n06_partial_radial_smooth hur) r
  have hrθ := n06_slice_smooth (n06_partial_angular_smooth hur) r
  have hθθ := n06_slice_smooth (n06_partial_angular_smooth hut) r
  have ha : ContDiff ℝ ∞ (fun θ => heightAngular (stateU S z.1) (r, θ)) := by
    exact (n06_slice_smooth hut r).div_const r
  have hd : ContDiff ℝ ∞ (fun θ => radialPartial (heightAngular (stateU S z.1)) (r, θ)) := by
    have he : (fun θ => radialPartial (heightAngular (stateU S z.1)) (r, θ)) =
        (fun θ => (1 / r) * angularPartial (radialPartial (stateU S z.1)) (r, θ) -
          (1 / r ^ 2) * angularPartial (stateU S z.1) (r, θ)) :=
      funext fun θ => n06_radial_heightAngular_formula hu hr
    rw [he]
    exact (contDiff_const.mul hrθ).sub (contDiff_const.mul (n06_slice_smooth hut r))
  have he : ContDiff ℝ ∞ (fun θ => angularPartial (heightAngular (stateU S z.1)) (r, θ)) := by
    have heq : (fun θ => angularPartial (heightAngular (stateU S z.1)) (r, θ)) =
        (fun θ => angularPartial (angularPartial (stateU S z.1)) (r, θ) / r) :=
      funext fun θ => angularPartial_heightAngular_eq hu hr
    rw [heq]
    exact hθθ.div_const r
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    simp only [n06ActualNuJetCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    first | exact contDiff_const | exact n06_slice_smooth hur r | exact hrr |
      exact ha | exact hd | exact he

theorem n06_actualNuJetCoordinates_angularJet_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) {r : ℝ} (hr : r ≠ 0) (j : ℕ) (θ : ℝ)
    (i : Fin 12) :
    (iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ) i =
      iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t) i) θ := by
  exact (spaces_iteratedDeriv_clm (ContinuousLinearMap.proj i)
    (n06_actualNuJetCoordinates_angular_contDiff hT hS z hr) j θ).symm

end ContinuousFlexibility.Statements
