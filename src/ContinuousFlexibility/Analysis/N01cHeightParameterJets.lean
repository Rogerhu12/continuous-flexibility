import ContinuousFlexibility.Analysis.N01cHeightSeminorms
import ContinuousFlexibility.Analysis.N01cLinearContinuity
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Actual continuous-linear height-jet evaluations

The finite material jets used by the nonlinear coefficients are genuine
continuous-linear functionals on the realized height space. Linearity is
proved for the actual iterated spatial derivatives of the decoded smooth
height. Continuity follows from the quantitative two-derivative estimate,
with no assumed continuity of derivative evaluation. Finite tuples and
their directional towers retain these exact evaluation formulas.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Mixed spatial derivatives add on actual smooth cylinder functions. -/
theorem mixedDerivative_add_of_contDiff {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q + g q) p =
      mixedDerivative a b f p + mixedDerivative a b g p := by
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, p.2)) :=
    contDiff_id.prodMk contDiff_const
  have hfr : ContDiff ℝ ∞ (fun r : ℝ =>
      iteratedDeriv b (fun θ : ℝ => f (r, θ)) p.2) := by
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using
      (contDiff_mixedDerivative hf 0 b).comp hline
  have hgr : ContDiff ℝ ∞ (fun r : ℝ =>
      iteratedDeriv b (fun θ : ℝ => g (r, θ)) p.2) := by
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using
      (contDiff_mixedDerivative hg 0 b).comp hline
  have hinner :
      (fun r : ℝ => iteratedDeriv b (fun θ : ℝ => f (r, θ) + g (r, θ)) p.2) =
        (fun r : ℝ => iteratedDeriv b (fun θ : ℝ => f (r, θ)) p.2 +
          iteratedDeriv b (fun θ : ℝ => g (r, θ)) p.2) := by
    funext r
    have hθ : ContDiff ℝ ∞ (fun θ : ℝ => (r, θ)) :=
      contDiff_const.prodMk contDiff_id
    exact iteratedDeriv_fun_add
      ((hf.comp hθ).contDiffAt.of_le (by simp))
      ((hg.comp hθ).contDiffAt.of_le (by simp))
  unfold mixedDerivative
  rw [hinner]
  exact iteratedDeriv_fun_add (hfr.contDiffAt.of_le (by simp))
    (hgr.contDiffAt.of_le (by simp))

/-- Scalar multiplication commutes with the actual mixed derivatives. -/
theorem mixedDerivative_const_mul (c : ℝ) (f : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => c * f q) p = c * mixedDerivative a b f p := by
  simp only [mixedDerivative, iteratedDeriv_const_mul_field]

theorem materialPullback_decode_add (T : MaterialData) (γ : ℝ)
    (M : SobolevModelData) (u v : M.Space) :
    materialPullback T γ (M.decode (u + v)) =
      (fun p => materialPullback T γ (M.decode u) p +
        materialPullback T γ (M.decode v) p) := by
  funext p
  simp only [map_add, materialPullback, Pi.add_apply, mul_add]

theorem materialPullback_decode_smul (T : MaterialData) (γ : ℝ)
    (M : SobolevModelData) (c : ℝ) (u : M.Space) :
    materialPullback T γ (M.decode (c • u)) =
      (fun p => c * materialPullback T γ (M.decode u) p) := by
  funext p
  simp only [map_smul, materialPullback, Pi.smul_apply, smul_eq_mul]
  ring

/-- Evaluation of a material mixed jet as an actual linear functional. -/
def heightMaterialJetLinear {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {M : SobolevModelData} (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) : M.Space →ₗ[ℝ] ℝ where
  toFun u := mixedDerivative a b (materialPullback T γ (M.decode u)) p
  map_add' u v := by
    rw [materialPullback_decode_add]
    exact mixedDerivative_add_of_contDiff
      (contDiff_materialPullback hT (hM.2.2.2.1 u).1)
      (contDiff_materialPullback hT (hM.2.2.2.1 v).1) a b p
  map_smul' c u := by
    rw [materialPullback_decode_smul]
    simpa only [RingHom.id_apply, smul_eq_mul] using mixedDerivative_const_mul c _ a b p

theorem heightMaterialJetLinear_apply {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {M : SobolevModelData} (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) (u : M.Space) :
    heightMaterialJetLinear hT hM a b p u =
      mixedDerivative a b (materialPullback T γ (M.decode u)) p := rfl

theorem continuous_heightMaterialJetLinear
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) : Continuous (heightMaterialJetLinear hT hM a b p) := by
  apply continuous_linear_of_seminorm_bound (heightMaterialJetLinear hT hM a b p)
    (M.grading (a + b + 2)) (continuous_gradedSeminorm _ _ _) (4 * Real.sqrt Real.pi)
  intro u
  simpa only [heightMaterialJetLinear_apply, Real.norm_eq_abs] using
    sobolevModel_materialPullback_mixedDerivative_le_grading hT hM u le_rfl p

/-- The coefficient formula's material jet inputs, with continuity derived
from the actual physical norm rather than supplied as a hypothesis. -/
def heightMaterialJetCLM {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {M : SobolevModelData} (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) : M.Space →L[ℝ] ℝ where
  toLinearMap := heightMaterialJetLinear hT hM a b p
  cont := continuous_heightMaterialJetLinear hT hM a b p

theorem heightMaterialJetCLM_apply {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {M : SobolevModelData} (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) (u : M.Space) :
    heightMaterialJetCLM hT hM a b p u =
      mixedDerivative a b (materialPullback T γ (M.decode u)) p := rfl

theorem heightMaterialJetCLM_bound {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {M : SobolevModelData} (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) (u : M.Space) {s : ℕ} (hab : a + b + 2 ≤ s) :
    |heightMaterialJetCLM hT hM a b p u| ≤
      (4 * Real.sqrt Real.pi) * M.grading s u :=
  sobolevModel_materialPullback_mixedDerivative_le_grading hT hM u hab p

/-- A finite jet vector keeps the exact ordered list of evaluation data. -/
def heightMaterialJetTupleCLM {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {M : SobolevModelData} (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    {n : ℕ} (a b : Fin n → ℕ) (p : Fin n → PolarPoint) : M.Space →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => heightMaterialJetCLM hT hM (a i) (b i) (p i)

theorem heightMaterialJetTupleCLM_apply
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    {n : ℕ} (a b : Fin n → ℕ) (p : Fin n → PolarPoint) (u : M.Space) (i : Fin n) :
    heightMaterialJetTupleCLM hT hM a b p u i =
      mixedDerivative (a i) (b i) (materialPullback T γ (M.decode u)) (p i) := by
  simp only [heightMaterialJetTupleCLM, ContinuousLinearMap.pi_apply,
    heightMaterialJetCLM_apply]

/-- The parameter tower of a material-jet evaluation is the ordinary tower
of its genuine continuous-linear functional. -/
def heightMaterialJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) :
    SmoothDirections univ
      (fun u : M.Space => mixedDerivative a b (materialPullback T γ (M.decode u)) p) :=
  smoothDirectionsLinear (heightMaterialJetCLM hT hM a b p)

def heightMaterialJetTupleSmoothDirections
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    {n : ℕ} (a b : Fin n → ℕ) (p : Fin n → PolarPoint) :
    SmoothDirections univ (fun u : M.Space => fun i : Fin n =>
      mixedDerivative (a i) (b i) (materialPullback T γ (M.decode u)) (p i)) :=
  smoothDirectionsLinear (heightMaterialJetTupleCLM hT hM a b p)

end ContinuousFlexibility.Statements
