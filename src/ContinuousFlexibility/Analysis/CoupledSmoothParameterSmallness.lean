import ContinuousFlexibility.Analysis.CoupledControlSmallness
import ContinuousFlexibility.Analysis.TameInverseExpressions

/-!
# Uniform smallness from an actual smooth linear family

The ordered forward-jet construction makes the parameter derivative a
continuous linear map in its independent input. Its joint continuity is
part of the genuine smooth tower. The real mean-value argument therefore
applies without any operator-norm continuity assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {U : Set (X × ℝ)} {A : X × ℝ → E →L[ℝ] F}

/-- The input stays in the final jet slot, so its linearity is already
bundled rather than recovered from pointwise derivatives. -/
def coupledParameterDerivative
    (J : SmoothDirections (U ×ˢ univ) (fun z : (X × ℝ) × E => A z.1 z.2))
    (z : X × ℝ) : E →L[ℝ] F :=
  inverseForwardJetLinear J 1 z (Fin.cons (0, 1) Fin.elim0)

theorem coupledParameterDerivative_hasDerivAt
    (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) (fun z : (X × ℝ) × E => A z.1 z.2))
    {z : X × ℝ} (hz : z ∈ U) (u : E) :
    HasDerivAt (fun q : ℝ => A (z.1, q) u) (coupledParameterDerivative J z u) z.2 := by
  rcases z with ⟨x, q⟩
  have hd := hasProjectiveLineDerivAt_inverseForwardJet J hz 0 Fin.elim0 u ((0 : X), 1)
  have hgerm : (fun x => A x u) =ᶠ[𝓝 (x, q)]
      (fun x => inverseForwardJet J 0 x Fin.elim0 u) := by
    filter_upwards [hU.mem_nhds hz] with x hx
    exact (inverseForwardJet_zero J hx u).symm
  have hline := hd.congr_germ hgerm
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    coupledParameterDerivative, inverseForwardJetLinear_apply,
    Prod.mk_add_mk, Prod.smul_mk,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, smul_eq_mul, mul_one, zero_smul, zero_add, add_zero, Prod.eta] using hline

theorem continuousOn_coupledParameterDerivative
    (J : SmoothDirections (U ×ˢ univ) (fun z : (X × ℝ) × E => A z.1 z.2)) :
    ContinuousOn (fun z : (X × ℝ) × E => coupledParameterDerivative J z.1 z.2)
      (U ×ˢ univ) := by
  let v : Fin 1 → X × ℝ := Fin.cons ((0 : X), 1) Fin.elim0
  have hm : Continuous
      (fun z : (X × ℝ) × E => (z.1, (v, z.2))) :=
    continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  have hmOn : ContinuousOn
      (fun z : (X × ℝ) × E => (z.1, (v, z.2))) (U ×ˢ univ) :=
    hm.continuousOn
  have hc := (continuousOn_inverseForwardJet J 1).comp hmOn
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  apply hc.congr
  intro z hz
  exact inverseForwardJetLinear_apply J 1 z.1 v z.2

/-- A genuinely smooth linear family which vanishes at zero parameter has
uniformly small fiber norm on one parameter strip near any base point. -/
theorem coupled_exists_small_smooth_parameter_family
    (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) (fun z : (X × ℝ) × E => A z.1 z.2))
    {x0 : X} (hx0 : (x0, 0) ∈ U)
    (hzero : ∀ x, (x, 0) ∈ U → ∀ u, A (x, 0) u = 0) :
    ∃ W : Set X, W ∈ 𝓝 x0 ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ W, ∀ q : ℝ, |q| < δ → (x, q) ∈ U ∧ ‖A (x, q)‖ < (1 / 4 : ℝ) := by
  have hc := (continuousOn_coupledParameterDerivative J) ((x0, 0), 0) ⟨hx0, mem_univ _⟩
  exact coupled_exists_small_parameter_family A (coupledParameterDerivative J) hU hx0 hzero
    (fun z hz u => coupledParameterDerivative_hasDerivAt hU J hz u)
    (hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hx0, mem_univ _⟩))

end ContinuousFlexibility.Analysis
