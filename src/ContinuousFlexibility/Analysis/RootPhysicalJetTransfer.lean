import ContinuousFlexibility.Analysis.RootModelAllAngleJets
import ContinuousFlexibility.Analysis.RootAffineOrdinaryJets

/-!
# Actual physical fields from the scaled ordinary root jets

The true ordinary jet identities transfer the controlled model to the
stored chart and height. The fixed invertible radial normalization is
then removed. Its inverse norm and determinant affect only component
constants, and the inverse-height tower is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem rootPhysicalFields_of_scaled_jet_model
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {B : ℕ → ℝ} {z : E}
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0) (hB : ∀ n, 0 ≤ B n)
    {F M : PolarPoint → PolarPoint} {H h : PolarPoint → ℝ} {q : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F (rootProfileShift r ℓ q))
    (hH : ContDiffAt ℝ ∞ H (rootProfileShift r ℓ q))
    (hHpos : 0 < H (rootProfileShift r ℓ q))
    (hmodel : RootPhysicalFieldJetBound p loss B z M h q)
    (hFjet : ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun y => F (rootProfileShift r ℓ y)) q =
        iteratedFDeriv ℝ n M q)
    (hHjet : ∀ a : ℝ, ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun y => H (rootProfileShift r ℓ y) ^ a) q =
        iteratedFDeriv ℝ n (fun y => h y ^ a) q)
    {J₀ : ℝ} (hJ : J₀ ≤ planeJacobian M q) :
    RootPhysicalFieldJetBound p loss (rootAffineJetEnvelope ℓ B) z
      F H (rootProfileShift r ℓ q) ∧
      J₀ / |ℓ| ≤ |planeJacobian F (rootProfileShift r ℓ q)| := by
  have hs : ContDiff ℝ ∞ (rootProfileShift r ℓ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hFnorm : ContDiffAt ℝ ∞ (fun y => F (rootProfileShift r ℓ y)) q := by
    have hh := hF.comp q hs.contDiffAt
    have he : F ∘ rootProfileShift r ℓ = (fun y => F (rootProfileShift r ℓ y)) := by
      funext y
      exact Function.comp_apply
    rw [he] at hh
    exact hh
  have hHnorm : ContDiffAt ℝ ∞ (fun y => H (rootProfileShift r ℓ y)) q := by
    have hh := hH.comp q hs.contDiffAt
    have he : H ∘ rootProfileShift r ℓ = (fun y => H (rootProfileShift r ℓ y)) := by
      funext y
      exact Function.comp_apply
    rw [he] at hh
    exact hh
  have hFbound : ∀ n : ℕ, 1 ≤ n →
      ‖iteratedFDeriv ℝ n (fun y => F (rootProfileShift r ℓ y)) q‖ ≤
        B n * (1 + p (n + loss) z) := by
    intro n hn
    rw [hFjet n]
    exact hmodel.2.2.2.1 n hn
  have hHnormJet : PointwiseMaterialJetBound p loss B z
      (fun y => H (rootProfileShift r ℓ y)) q := by
    apply pointwiseMaterialJetBound_of_iteratedFDeriv_eq _ hmodel.2.2.2.2.1
    intro n
    simpa only [Real.rpow_one] using hHjet 1 n
  have hInormJet : PointwiseMaterialJetBound p loss B z
      (fun y => (H (rootProfileShift r ℓ y))⁻¹) q := by
    apply pointwiseMaterialJetBound_of_iteratedFDeriv_eq _ hmodel.2.2.2.2.2
    intro n
    simpa only [Real.rpow_neg_one] using hHjet (-1) n
  have hHbound := PointwiseMaterialJetBound.unscale_rootProfile
    r ℓ hℓ hB hHnorm hHnormJet
  have hIbound := PointwiseMaterialJetBound.unscale_rootProfile
    r ℓ hℓ hB (hHnorm.fun_inv hHpos.ne') hInormJet
  have hD := root_fderiv_eq_of_firstJet_eq hFnorm hmodel.1 (hFjet 1)
  have hJnorm : planeJacobian (fun y => F (rootProfileShift r ℓ y)) q =
      planeJacobian M q := by
    unfold planeJacobian
    rw [hD]
  exact ⟨⟨hF, hH, hHpos,
      rootProfile_unscale_positiveJets r ℓ hℓ hB hFnorm hFbound,
      hHbound, hIbound⟩,
    planeJacobian_unscale_rootProfile_lower r ℓ hℓ
      (hF.differentiableAt (by simp)) (hJ.trans_eq hJnorm.symm)⟩

end ContinuousFlexibility.Analysis
