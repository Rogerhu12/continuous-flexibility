import ContinuousFlexibility.Analysis.N07bFiniteRadialGreen
import ContinuousFlexibility.Radial.ReferenceColumnSmooth
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual reference forcing from finite physical jets

The three reference coefficients are uniformly bounded on the closed
core. The first and second coordinate derivatives are evaluations of
the actual Fréchet jets, so the genuine radial PDE inherits their bound.
A positive gap between two height exponents absorbs every fixed material
envelope power. No decay assumption on the forcing is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n07b_first_direction_abs_le (f : PolarPoint → ℝ)
    (x v : PolarPoint) :
    |fderiv ℝ f x v| ≤ ‖iteratedFDeriv ℝ 1 f x‖ * ‖v‖ := by
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_one] using
    (fderiv ℝ f x).le_opNorm v

private theorem n07b_second_direction_abs_le {u : PolarPoint → ℝ} {x : PolarPoint}
    (hu : ContDiffAt ℝ 2 u x) (v w : PolarPoint) :
    |fderiv ℝ (fun y => fderiv ℝ u y v) x w| ≤
      (‖v‖ * ‖iteratedFDeriv ℝ 2 u x‖) * ‖w‖ := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  have hj := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ u) (c := v) (n := 1) hd (by norm_num)
  rw [norm_iteratedFDeriv_fderiv] at hj
  exact (n07b_first_direction_abs_le (fun y => fderiv ℝ u y v) x w).trans
    (mul_le_mul_of_nonneg_right hj (norm_nonneg w))

/-- The actual reference expression uses only the first two physical jets. -/
theorem n07b_referencePDE_abs_le_frechet_jets
    {w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hu : ContDiffAt ℝ 2 u x) :
    |radialPDE w (fun r θ => u (r, θ)) x.1 x.2| ≤
      |deriv w x.1| * ‖iteratedFDeriv ℝ 1 u x‖ +
        (|w x.1| + |deriv w x.1 / x.1|) * ‖iteratedFDeriv ℝ 2 u x‖ := by
  have hv₁ : ‖((1, 0) : PolarPoint)‖ = 1 := by norm_num [Prod.norm_mk]
  have hv₂ : ‖((0, 1) : PolarPoint)‖ = 1 := by norm_num [Prod.norm_mk]
  have hr : |radialPartial u x| ≤ ‖iteratedFDeriv ℝ 1 u x‖ := by
    simpa only [radialPartial, hv₁, mul_one] using
      n07b_first_direction_abs_le u x (1, 0)
  have hrr : |radialPartial (radialPartial u) x| ≤ ‖iteratedFDeriv ℝ 2 u x‖ := by
    change |fderiv ℝ (fun y => fderiv ℝ u y (1, 0)) x (1, 0)| ≤ _
    simpa only [hv₁, one_mul, mul_one] using
      n07b_second_direction_abs_le hu (1, 0) (1, 0)
  have hθθ : |angularPartial (angularPartial u) x| ≤ ‖iteratedFDeriv ℝ 2 u x‖ := by
    change |fderiv ℝ (fun y => fderiv ℝ u y (0, 1)) x (0, 1)| ≤ _
    simpa only [hv₂, one_mul, mul_one] using
      n07b_second_direction_abs_le hu (0, 1) (0, 1)
  rw [n07b_c2_radialPDE_eq_polar_jets hw hu]
  calc
    _ ≤ |deriv w x.1 * radialPartial u x| +
        |w x.1 * radialPartial (radialPartial u) x| +
        |deriv w x.1 / x.1 * angularPartial (angularPartial u) x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |deriv w x.1| * |radialPartial u x| +
        |w x.1| * |radialPartial (radialPartial u) x| +
        |deriv w x.1 / x.1| * |angularPartial (angularPartial u) x| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |deriv w x.1| * ‖iteratedFDeriv ℝ 1 u x‖ +
        |w x.1| * ‖iteratedFDeriv ℝ 2 u x‖ +
        |deriv w x.1 / x.1| * ‖iteratedFDeriv ℝ 2 u x‖ :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hrr (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hθθ (abs_nonneg _))
    _ = _ := by ring

/-- The reference coefficients have one bound independent of the height. -/
theorem n07b_reference_coefficients_bounded {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc D.a D.b,
      |deriv D.w r| + |D.w r| + |deriv D.w r / r| ≤ B := by
  have hdw : Continuous (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2.continuous
  have hq : Continuous (fun r => deriv D.w r / r) :=
    (reference_contDiff_flat_deriv_div hgeom.1 hgeom.2.2.1).continuous
  have hc : Continuous (fun r => |deriv D.w r| + |D.w r| + |deriv D.w r / r|) :=
    (hdw.abs.add hgeom.2.2.1.1.continuous.abs).add hq.abs
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun r hr => ?_⟩
  have hb : |(|deriv D.w r| + |D.w r| + |deriv D.w r / r|)| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB r hr
  exact (le_abs_self _).trans (hb.trans (le_max_left _ _))

/-- A positive exponent gap absorbs every fixed real power of the actual
material envelope. The exponents themselves may be any real numbers. -/
theorem n07b_material_height_gap_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {δ γ : ℝ} (hγδ : γ < δ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ radialCore D,
      T.H r ^ δ * T.M r ^ A ≤ C * T.H r ^ γ := by
  obtain ⟨C, hC, hbound, _, _⟩ :=
    hT.2.2.2.2.2.2.2.2.2.2.2.2.1 A (δ - γ) (sub_pos.mpr hγδ)
  refine ⟨C, hC, fun r hr => ?_⟩
  have hH := (hT.2.1 r hr).2.1
  have hsplit : T.H r ^ δ = T.H r ^ γ * T.H r ^ (δ - γ) := by
    rw [← Real.rpow_add hH]
    congr 1
    ring
  calc
    _ = T.H r ^ γ * (T.H r ^ (δ - γ) * T.M r ^ A) := by rw [hsplit]; ring
    _ ≤ T.H r ^ γ * C :=
      mul_le_mul_of_nonneg_left (hbound r hr) (Real.rpow_pos_of_pos hH γ).le
    _ = _ := mul_comm _ _

/-- A genuine C² height with material bounds on jets zero through two has
reference forcing with every strictly smaller height exponent. -/
theorem n07b_referencePDE_decay_of_frechet_jets
    {D : ReferenceData} {T : MaterialData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    {δ γ A K : ℝ} (hγδ : γ < δ) (hK : 0 ≤ K)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ 2 u)
    (hjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n u x‖ ≤ K * T.H x.1 ^ δ * T.M x.1 ^ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ annularOpen D,
      |radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2| ≤ C * T.H x.1 ^ γ := by
  obtain ⟨B, hB, hcoeff⟩ := n07b_reference_coefficients_bounded hgeom
  obtain ⟨L, hL, hweight⟩ := n07b_material_height_gap_bound hT hγδ A
  refine ⟨B * K * L, mul_nonneg (mul_nonneg hB hK) hL.le, fun x hx => ?_⟩
  have hpos := hT.2.1 x.1 hx.1
  have hW : 0 ≤ K * T.H x.1 ^ δ * T.M x.1 ^ A :=
    mul_nonneg (mul_nonneg hK (Real.rpow_pos_of_pos hpos.2.1 δ).le)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hpos.2.2.2) A).le
  have h₁ := hjet x hx 1 (by norm_num)
  have h₂ := hjet x hx 2 le_rfl
  calc
    _ ≤ |deriv D.w x.1| * ‖iteratedFDeriv ℝ 1 u x‖ +
        (|D.w x.1| + |deriv D.w x.1 / x.1|) * ‖iteratedFDeriv ℝ 2 u x‖ :=
      n07b_referencePDE_abs_le_frechet_jets
        (hgeom.2.2.1.1.differentiable (by simp) x.1) hu.contDiffAt
    _ ≤ |deriv D.w x.1| * (K * T.H x.1 ^ δ * T.M x.1 ^ A) +
        (|D.w x.1| + |deriv D.w x.1 / x.1|) * (K * T.H x.1 ^ δ * T.M x.1 ^ A) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h₂ (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = (|deriv D.w x.1| + |D.w x.1| + |deriv D.w x.1 / x.1|) *
        (K * T.H x.1 ^ δ * T.M x.1 ^ A) := by ring
    _ ≤ B * (K * T.H x.1 ^ δ * T.M x.1 ^ A) :=
      mul_le_mul_of_nonneg_right (hcoeff x.1 ⟨hx.1.1.le, hx.1.2.le⟩) hW
    _ = (B * K) * (T.H x.1 ^ δ * T.M x.1 ^ A) := by ring
    _ ≤ (B * K) * (L * T.H x.1 ^ γ) :=
      mul_le_mul_of_nonneg_left (hweight x.1 hx.1) (mul_nonneg hB hK)
    _ = _ := by ring

/-- Additivity is proved for the actual differential expression at C²
regularity, for later addition of the prescribed left cutoff. -/
theorem n07b_c2_radialPDE_add {w : ℝ → ℝ} {u v : PolarPoint → ℝ}
    (hw : Differentiable ℝ w) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x : PolarPoint) :
    radialPDE w (fun r θ => u (r, θ) + v (r, θ)) x.1 x.2 =
      radialPDE w (fun r θ => u (r, θ)) x.1 x.2 +
        radialPDE w (fun r θ => v (r, θ)) x.1 x.2 := by
  have hud (y : PolarPoint) := hu.differentiable (by norm_num) y
  have hvd (y : PolarPoint) := hv.differentiable (by norm_num) y
  have hrad : radialPartial (fun y => u y + v y) =
      fun y => radialPartial u y + radialPartial v y :=
    funext fun y => radialPartial_add (hud y) (hvd y)
  have hang : angularPartial (fun y => u y + v y) =
      fun y => angularPartial u y + angularPartial v y :=
    funext fun y => angularPartial_add (hud y) (hvd y)
  have hrr : radialPartial (radialPartial (fun y => u y + v y)) x =
      radialPartial (radialPartial u) x + radialPartial (radialPartial v) x := by
    rw [hrad]
    exact radialPartial_add
      ((contDiffAt_radialPartial hu.contDiffAt (m := 1) (by norm_num)).differentiableAt one_ne_zero)
      ((contDiffAt_radialPartial hv.contDiffAt (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  have hθθ : angularPartial (angularPartial (fun y => u y + v y)) x =
      angularPartial (angularPartial u) x + angularPartial (angularPartial v) x := by
    rw [hang]
    exact angularPartial_add
      ((contDiffAt_angularPartial hu.contDiffAt (m := 1) (by norm_num)).differentiableAt one_ne_zero)
      ((contDiffAt_angularPartial hv.contDiffAt (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  rw [n07b_c2_radialPDE_eq_polar_jets (hw x.1) (hu.add hv).contDiffAt,
    n07b_c2_radialPDE_eq_polar_jets (hw x.1) hu.contDiffAt,
    n07b_c2_radialPDE_eq_polar_jets (hw x.1) hv.contDiffAt, hrr, hθθ, hrad]
  ring

end ContinuousFlexibility.Analysis
