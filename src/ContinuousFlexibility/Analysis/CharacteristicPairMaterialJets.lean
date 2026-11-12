import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The true half-sum and half-difference of characteristic labels

Subtracting the linear angle from both labels makes their half-sum and
half-difference bounded objects. Two fixed contractions give their
ordinary jets without introducing any new state order or loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private def characteristicHalfLinear (difference : Bool) : PolarPoint →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ +
    (if difference then (-1 : ℝ) else 1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem characteristicHalfLinear_apply (difference : Bool) (x : PolarPoint) :
    characteristicHalfLinear difference x =
      (x.1 + (if difference then (-1 : ℝ) else 1) * x.2) / 2 := by
  simp only [characteristicHalfLinear, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

private theorem characteristicHalfLinear_norm (difference : Bool) :
    ‖characteristicHalfLinear difference‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [characteristicHalfLinear_apply, Real.norm_eq_abs, abs_div]
  have he : |(if difference then (-1 : ℝ) else 1) * x.2| = |x.2| := by
    cases difference <;> simp
  have h1 : |x.1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le x
  have h2 : |x.2| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le x
  have hh := abs_add_le x.1 ((if difference then (-1 : ℝ) else 1) * x.2)
  rw [he] at hh
  norm_num only [abs_ofNat, one_mul]
  nlinarith only [hh, h1, h2]

theorem characteristicPair_material_jets
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    {U V : PolarPoint → ℝ} {q : PolarPoint}
    (hU : ContDiffAt ℝ ∞ U q) (hV : ContDiffAt ℝ ∞ V q)
    (hu : PointwiseMaterialJetBound p loss A z (fun y => U y - y.2) q)
    (hv : PointwiseMaterialJetBound p loss A z (fun y => V y - y.2) q) :
    PointwiseMaterialJetBound p loss A z (fun y => (U y - V y) / 2) q ∧
      PointwiseMaterialJetBound p loss A z (fun y => (U y + V y) / 2 - y.2) q := by
  let f : PolarPoint → PolarPoint := fun y => (U y - y.2, V y - y.2)
  have hf : ContDiffAt ℝ ∞ f q :=
    (hU.sub contDiffAt_snd).prodMk (hV.sub contDiffAt_snd)
  have hb : PointwiseMaterialJetBound p loss A z f q := by
    simpa only [max_self] using PointwiseMaterialJetBound.prodMk
      (hU.sub contDiffAt_snd) (hV.sub contDiffAt_snd) hu hv
  have hbound (difference : Bool) :=
    PointwiseMaterialJetBound.contractive_clm_comp hf hb
      (characteristicHalfLinear difference) (characteristicHalfLinear_norm difference)
  have hdiff : characteristicHalfLinear true ∘ f = (fun y => (U y - V y) / 2) := by
    funext y
    rw [Function.comp_apply, characteristicHalfLinear_apply]
    simp only [f, ite_true]
    ring
  have hsum : characteristicHalfLinear false ∘ f =
      (fun y => (U y + V y) / 2 - y.2) := by
    funext y
    rw [Function.comp_apply, characteristicHalfLinear_apply]
    simp only [f, Bool.false_eq_true, ite_false]
    ring
  exact ⟨hdiff ▸ hbound true, hsum ▸ hbound false⟩

end ContinuousFlexibility.Analysis
