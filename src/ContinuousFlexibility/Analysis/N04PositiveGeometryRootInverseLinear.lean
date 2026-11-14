module

public import ContinuousFlexibility.Analysis.NonlinearInverseJetTriangle
public import ContinuousFlexibility.Analysis.N04RealizationPlaneJetDirections
public import ContinuousFlexibility.Analysis.TameProductDirections

/-!
# The oriented triangular inverse differential

The radial orientation occurs in the first diagonal entry. The two
orientation factors cancel in the lower off-diagonal entry. Genuine
scalar coefficient towers therefore construct the full operator tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped ContDiff Topology

def n04PositiveGeometry_rootInverseLinear (σ a e b : ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  ((σ * a) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (b • ContinuousLinearMap.snd ℝ ℝ ℝ -
      (b * e * a) • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem n04PositiveGeometry_rootInverseLinear_apply (σ a e b : ℝ) (v : PolarPoint) :
    n04PositiveGeometry_rootInverseLinear σ a e b v =
      (σ * a * v.1, b * v.2 - b * e * a * v.1) := by
  simp only [n04PositiveGeometry_rootInverseLinear, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]

/-- The inverse is checked against the actual two columns. -/
theorem n04PositiveGeometry_rootInverseLinear_left
    (D : PolarPoint →L[ℝ] PolarPoint) {σ A a e β b : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (ha : a * A = 1) (hb : b * β = 1)
    (hr : D (1, 0) = (σ * A, σ * e)) (hθ : D (0, 1) = (0, β)) :
    (n04PositiveGeometry_rootInverseLinear σ a e b).comp D =
      ContinuousLinearMap.id ℝ PolarPoint := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hD (v : PolarPoint) : D v = (σ * A * v.1, σ * e * v.1 + β * v.2) := by
    have hv : v.1 • ((1, 0) : PolarPoint) + v.2 • ((0, 1) : PolarPoint) = v := by
      ext <;> simp
    rw [← hv, map_add, map_smul, map_smul, hr, hθ]
    ext <;> simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, add_zero] <;> ring
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    hD, n04PositiveGeometry_rootInverseLinear_apply]
  apply Prod.ext
  · change σ * a * (σ * A * v.1) = v.1
    calc
      _ = (σ * σ) * (a * A) * v.1 := by ring
      _ = _ := by rw [hσσ, ha, one_mul, one_mul]
  · change b * (σ * e * v.1 + β * v.2) - b * e * a * (σ * A * v.1) = v.2
    calc
      _ = (b * β) * v.2 + b * σ * e * v.1 * (1 - a * A) := by ring
      _ = _ := by rw [hb, ha, sub_self, mul_zero, add_zero, one_mul]

theorem n04PositiveGeometry_rootInverse_fderiv_eq
    {f g : PolarPoint → PolarPoint} {q : PolarPoint} {σ A a e β b : ℝ}
    (hf : ContDiffAt ℝ ∞ f (g q)) (hg : ContDiffAt ℝ ∞ g q)
    (hfg : f ∘ g =ᶠ[𝓝 q] (id : PolarPoint → PolarPoint))
    (hσ : σ = 1 ∨ σ = -1) (ha : a * A = 1) (hb : b * β = 1)
    (hr : fderiv ℝ f (g q) (1, 0) = (σ * A, σ * e))
    (hθ : fderiv ℝ f (g q) (0, 1) = (0, β)) :
    fderiv ℝ g q = n04PositiveGeometry_rootInverseLinear σ a e b :=
  nonlinearInverse_fderiv_eq hf hg hfg _
    (n04PositiveGeometry_rootInverseLinear_left _ hσ ha hb hr hθ)

theorem n04PositiveGeometry_rootInverseLinear_norm (σ a e b : ℝ) :
    ‖n04PositiveGeometry_rootInverseLinear σ a e b‖ ≤
      |σ * a| + |b| + |b * e * a| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [n04PositiveGeometry_rootInverseLinear_apply, Prod.norm_def]
  have h₁ : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have h₂ : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  apply max_le
  · rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |σ * a| * ‖v‖ := mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_right (abs_nonneg b)).trans
          (le_add_of_nonneg_right (abs_nonneg (b * e * a)))) (norm_nonneg _)
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ |b * v.2| + |b * e * a * v.1| := abs_sub _ _
      _ = |b| * |v.2| + |b * e * a| * |v.1| := by rw [abs_mul, abs_mul]
      _ ≤ |b| * ‖v‖ + |b * e * a| * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _))
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg (σ * a)) (norm_nonneg v)]

/-- No parameter differentiability of an inverse map is assumed here:
the displayed scalar coefficients build its genuine operator tower. -/
def n04PositiveGeometry_rootInverseLinear_directions
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {a e b : X → ℝ} (σ : ℝ)
    (Ja : SmoothDirections U a) (Je : SmoothDirections U e) (Jb : SmoothDirections U b) :
    SmoothDirections U (fun x => n04PositiveGeometry_rootInverseLinear σ (a x) (e x) (b x)) := by
  let Jcross := smoothDirections_realMul (smoothDirections_realMul Jb Je) Ja
  let Jr := smoothDirectionsProd (smoothDirections_realConstMul σ Ja)
    (smoothDirections_realConstMul (-1 : ℝ) Jcross)
  let Jθ := smoothDirectionsProd (smoothDirections_constant Ja.open_domain (0 : ℝ)) Jb
  apply n04Realization_planeLinear_directions
    (fun x => n04PositiveGeometry_rootInverseLinear σ (a x) (e x) (b x))
  · apply Jr.congr
    intro x _
    simp only [n04PositiveGeometry_rootInverseLinear_apply, mul_one, mul_zero,
      zero_sub, neg_one_mul]
  · apply Jθ.congr
    intro x _
    simp only [n04PositiveGeometry_rootInverseLinear_apply, mul_one, mul_zero, sub_zero]

end ContinuousFlexibility.Analysis
