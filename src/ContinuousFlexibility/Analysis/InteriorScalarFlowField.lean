import ContinuousFlexibility.Analysis.AffineWeightedCompositionJets
import ContinuousFlexibility.Analysis.RootFieldLocalization
import ContinuousFlexibility.Analysis.N04FlowJetsTarget

/-!
# An actual scalar flow with variable terminal radius

The first external parameter selects a radius in a fixed closed interval.
Time follows the straight radial segment from its left endpoint. Only the
original field's spatial jets on that interval enter the estimates; the
second external parameter is unused. The angular Gronwall bound depends
on the first angular derivative alone.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def interiorFlowRadius (a b t : ℝ) (v : ℝ × ℝ) : ℝ :=
  a + t * ((b - a) / 2 * (1 + v.1))

def interiorScalarFlowField (f : PolarPoint → ℝ) (a b : ℝ) :
    ℝ × N04FlowPoint → ℝ :=
  fun q => ((b - a) / 2 * (1 + q.2.1.1)) *
    f (interiorFlowRadius a b q.1 q.2.1, q.2.2)

theorem interiorFlowRadius_mem {a b t : ℝ} (hab : a ≤ b)
    (ht : t ∈ Icc (0 : ℝ) 1) {v : ℝ × ℝ}
    (hv : v ∈ n04FlowParameterBox) : interiorFlowRadius a b t v ∈ Icc a b := by
  have hd : 0 ≤ (b - a) / 2 := by linarith
  have hw : 0 ≤ (b - a) / 2 * (1 + v.1) := mul_nonneg hd (by linarith [hv.1.1])
  have hw' : (b - a) / 2 * (1 + v.1) ≤ b - a := by nlinarith [hv.1.2]
  have htw := mul_nonneg ht.1 hw
  have htw' := (mul_le_mul_of_nonneg_right ht.2 hw).trans
    (by simpa only [one_mul] using hw')
  dsimp only [interiorFlowRadius]
  exact ⟨by linarith, by linarith⟩

theorem contDiff_interiorScalarFlowField {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ ∞ (interiorScalarFlowField f a b) := by
  have hw : ContDiff ℝ ∞ (fun q : ℝ × N04FlowPoint =>
      (b - a) / 2 * (1 + q.2.1.1)) :=
    contDiff_const.mul (contDiff_const.add contDiff_snd.fst.fst)
  exact hw.mul (hf.comp ((contDiff_const.add (contDiff_fst.mul hw)).prodMk contDiff_snd.snd))

theorem interiorScalarFlowField_periodic {f : PolarPoint → ℝ} {P : ℝ}
    (hperiod : ∀ r, Function.Periodic (fun θ => f (r, θ)) P)
    (a b t : ℝ) (v : ℝ × ℝ) :
    Function.Periodic (fun θ => interiorScalarFlowField f a b (t, (v, θ))) P := by
  intro θ
  change ((b - a) / 2 * (1 + v.1)) * f (interiorFlowRadius a b t v, θ + P) =
    ((b - a) / 2 * (1 + v.1)) * f (interiorFlowRadius a b t v, θ)
  have hp : f (interiorFlowRadius a b t v, θ + P) =
      f (interiorFlowRadius a b t v, θ) := hperiod (interiorFlowRadius a b t v) θ
  rw [hp]

private def interiorFlowParameterProjection : N04FlowPoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

private theorem interiorFlowParameterProjection_apply (q : N04FlowPoint) :
    interiorFlowParameterProjection q = q.1.1 := by
  simp only [interiorFlowParameterProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst']

private theorem interiorFlowParameterProjection_norm :
    ‖interiorFlowParameterProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [interiorFlowParameterProjection_apply, one_mul]
  exact (norm_fst_le q.1).trans (norm_fst_le q)

private def interiorFlowArgument (c : ℝ) : N04FlowPoint →L[ℝ] PolarPoint :=
  (c • interiorFlowParameterProjection).prod (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)

private theorem interiorFlowArgument_apply (c : ℝ) (q : N04FlowPoint) :
    interiorFlowArgument c q = (c * q.1.1, q.2) := by
  simp only [interiorFlowArgument, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, interiorFlowParameterProjection_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul]

private theorem interiorFlowArgument_norm {t d : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖interiorFlowArgument (t * d)‖ ≤ 1 + |d| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  rw [interiorFlowArgument_apply, Prod.norm_def, max_le_iff]
  have htd : |t * d| ≤ |d| := by
    rw [abs_mul, abs_of_nonneg ht.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (abs_nonneg d)
  have hfirst : |q.1.1| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le q.1).trans (norm_fst_le q)
  constructor
  · rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul htd hfirst (abs_nonneg _) (abs_nonneg d)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg q))
  · have hone : (1 : ℝ) ≤ 1 + |d| := le_add_of_nonneg_right (abs_nonneg d)
    exact (norm_snd_le q).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (norm_nonneg q))

/-- Same-order field jets for the actual straight radial flow. -/
theorem interiorScalarFlowField_jet_le
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℝ)
    {M : ℝ} (hM : 0 ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : N04FlowPoint} (hq : q.1 ∈ n04FlowParameterBox)
    (n : ℕ) (hbound : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k f (interiorFlowRadius a b t q.1, q.2)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => interiorScalarFlowField f a b (t, y)) q‖ ≤
      (affineWeightedCompositionJetConstant (1 + |(b - a) / 2|) n *
        (2 * |(b - a) / 2|)) * M := by
  let d : ℝ := (b - a) / 2
  let A := interiorFlowArgument (t * d)
  let c : PolarPoint := (a + t * d, 0)
  let l := d • interiorFlowParameterProjection
  have hA : ‖A‖ ≤ 1 + |d| := interiorFlowArgument_norm ht
  have hl : ‖l‖ ≤ 2 * |d| := by
    have hh : ‖l‖ ≤ |d| := by
      dsimp only [l]
      rw [norm_smul, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        interiorFlowParameterProjection_norm (abs_nonneg d)
    exact hh.trans (by nlinarith only [abs_nonneg d])
  have hlq : ‖d + l q‖ ≤ 2 * |d| := by
    have hh : |l q| ≤ |d| := by
      simp only [l, ContinuousLinearMap.smul_apply, smul_eq_mul,
        interiorFlowParameterProjection_apply, abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (abs_le.mpr hq.1) (abs_nonneg d)
    rw [Real.norm_eq_abs]
    exact (abs_add_le d (l q)).trans (by linarith)
  have heval : c + A q = (interiorFlowRadius a b t q.1, q.2) := by
    simp only [c, A, interiorFlowArgument_apply, Prod.mk_add_mk, zero_add, interiorFlowRadius]
    congr 1
    dsimp only [d]
    ring
  have hh := norm_iteratedFDeriv_affineWeightedComposition_le hf A c l d q
    (le_add_of_nonneg_right (abs_nonneg d)) (by positivity : 0 ≤ 2 * |d|) hM
    hA hl hlq n (fun k hk => by rw [heval]; exact hbound k hk)
  have he : (fun y : N04FlowPoint => interiorScalarFlowField f a b (t, y)) =
      fun y => (d + l y) * f (c + A y) := by
    funext y
    have harg : c + A y = (interiorFlowRadius a b t y.1, y.2) := by
      simp only [c, A, interiorFlowArgument_apply, Prod.mk_add_mk, zero_add, interiorFlowRadius]
      congr 1
      dsimp only [d]
      ring
    rw [harg]
    simp only [interiorScalarFlowField, l, ContinuousLinearMap.smul_apply,
      interiorFlowParameterProjection_apply, smul_eq_mul]
    dsimp only [d]
    ring
  rw [he]
  exact hh

theorem interiorScalarFlowField_angularControl
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hbound : ∀ r ∈ Icc a b, ∀ θ,
      |deriv (fun η => f (r, η)) θ| ≤ M) :
    N04FlowAngularControl (interiorScalarFlowField f a b) (2 * |(b - a) / 2| * M) := by
  refine ⟨fun _ => 2 * |(b - a) / 2| * M, continuousOn_const,
    fun _ _ => by positivity, ?_, ?_⟩
  · intro t ht v hv θ
    have hdiff : DifferentiableAt ℝ (fun η => f (interiorFlowRadius a b t v, η)) θ :=
      (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) θ
    have he : deriv (fun η => interiorScalarFlowField f a b (t, (v, η))) θ =
        ((b - a) / 2 * (1 + v.1)) *
          deriv (fun η => f (interiorFlowRadius a b t v, η)) θ :=
      (hdiff.hasDerivAt.const_mul ((b - a) / 2 * (1 + v.1))).deriv
    have hw : |(b - a) / 2 * (1 + v.1)| ≤ 2 * |(b - a) / 2| := by
      rw [abs_mul]
      have hv₁ : |v.1| ≤ 1 := abs_le.mpr hv.1
      have hv' : |1 + v.1| ≤ 2 := (abs_add_le 1 v.1).trans
        (by rw [abs_one]; linarith only [hv₁])
      nlinarith only [mul_le_mul_of_nonneg_left hv' (abs_nonneg ((b - a) / 2))]
    rw [he, abs_mul]
    exact mul_le_mul hw (hbound _ (interiorFlowRadius_mem hab ht hv) θ)
      (abs_nonneg _) (by positivity)
  · simp only [intervalIntegral.integral_const, sub_zero, one_smul, le_refl]

end ContinuousFlexibility.Analysis
