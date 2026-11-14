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

private theorem rootPhysical_contDiffAt_scaled
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r ℓ : ℝ) {f : PolarPoint → Y} {q : PolarPoint}
    (hf : ContDiffAt ℝ ∞ f (rootProfileShift r ℓ q)) :
    ContDiffAt ℝ ∞ (fun y => f (rootProfileShift r ℓ y)) q := by
  have hs : ContDiff ℝ ∞ (rootProfileShift r ℓ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hc : ContDiffAt ℝ ∞ (f ∘ rootProfileShift r ℓ) q :=
    hf.comp q hs.contDiffAt
  simpa only [Function.comp_def] using hc

private theorem rootPhysical_heightJets_transfer
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {B : ℕ → ℝ} {z : E}
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0) (hB : ∀ n, 0 ≤ B n)
    {H h : PolarPoint → ℝ} {q : PolarPoint}
    (hHnorm : ContDiffAt ℝ ∞ (fun y => H (rootProfileShift r ℓ y)) q)
    (hHpos : 0 < H (rootProfileShift r ℓ q))
    (hHmodel : PointwiseMaterialJetBound p loss B z h q)
    (hImodel : PointwiseMaterialJetBound p loss B z (fun y => (h y)⁻¹) q)
    (hHjet : ∀ a : ℝ, ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun y => H (rootProfileShift r ℓ y) ^ a) q =
        iteratedFDeriv ℝ n (fun y => h y ^ a) q) :
    PointwiseMaterialJetBound p loss (rootAffineJetEnvelope ℓ B) z
        H (rootProfileShift r ℓ q) ∧
      PointwiseMaterialJetBound p loss (rootAffineJetEnvelope ℓ B) z
        (fun y => (H y)⁻¹) (rootProfileShift r ℓ q) := by
  have hHnormJet : PointwiseMaterialJetBound p loss B z
      (fun y => H (rootProfileShift r ℓ y)) q := by
    apply pointwiseMaterialJetBound_of_iteratedFDeriv_eq
      (E := E) (X := PolarPoint) (Y := ℝ) (p := p) (loss := loss) (A := B) (z := z)
      (f := fun y => H (rootProfileShift r ℓ y)) (g := h) (x := q) _ hHmodel
    intro n
    simpa only [Real.rpow_one] using hHjet 1 n
  have hInormJet : PointwiseMaterialJetBound p loss B z
      (fun y => (H (rootProfileShift r ℓ y))⁻¹) q := by
    apply pointwiseMaterialJetBound_of_iteratedFDeriv_eq
      (E := E) (X := PolarPoint) (Y := ℝ) (p := p) (loss := loss) (A := B) (z := z)
      (f := fun y => (H (rootProfileShift r ℓ y))⁻¹)
      (g := fun y => (h y)⁻¹) (x := q) _ hImodel
    intro n
    simpa only [Real.rpow_neg_one] using hHjet (-1) n
  have hInorm : ContDiffAt ℝ ∞ (fun y => (H (rootProfileShift r ℓ y))⁻¹) q :=
    hHnorm.fun_inv hHpos.ne'
  exact ⟨PointwiseMaterialJetBound.unscale_rootProfile
      (E := E) (Y := ℝ) (p := p) (loss := loss) (A := B) (z := z)
      (f := H) (q := q) r ℓ hℓ hB hHnorm hHnormJet,
    PointwiseMaterialJetBound.unscale_rootProfile
      (E := E) (Y := ℝ) (p := p) (loss := loss) (A := B) (z := z)
      (f := fun y => (H y)⁻¹) (q := q) r ℓ hℓ hB hInorm hInormJet⟩

private theorem rootPhysical_jacobian_transfer
    (r ℓ : ℝ) (hℓ : ℓ ≠ 0)
    {F M : PolarPoint → PolarPoint} {q : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F (rootProfileShift r ℓ q))
    (hM : ContDiffAt ℝ ∞ M q)
    (hjet : iteratedFDeriv ℝ 1 (fun y => F (rootProfileShift r ℓ y)) q =
      iteratedFDeriv ℝ 1 M q)
    {J₀ : ℝ} (hJ : J₀ ≤ planeJacobian M q) :
    J₀ / |ℓ| ≤ |planeJacobian F (rootProfileShift r ℓ q)| := by
  have hFnorm : ContDiffAt ℝ ∞ (fun y => F (rootProfileShift r ℓ y)) q :=
    rootPhysical_contDiffAt_scaled (Y := PolarPoint) r ℓ (f := F) (q := q) hF
  have hD : fderiv ℝ (fun y => F (rootProfileShift r ℓ y)) q = fderiv ℝ M q :=
    root_fderiv_eq_of_firstJet_eq
      (X := PolarPoint) (Y := PolarPoint)
      (f := fun y => F (rootProfileShift r ℓ y)) (g := M) (x := q)
      hFnorm hM hjet
  have hJnorm : planeJacobian (fun y => F (rootProfileShift r ℓ y)) q =
      planeJacobian M q := by
    unfold planeJacobian
    rw [hD]
  exact planeJacobian_unscale_rootProfile_lower
    r ℓ hℓ (F := F) (q := q) (J₀ := J₀)
    (hF.differentiableAt (by simp)) (hJ.trans_eq hJnorm.symm)

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
  have hFnorm : ContDiffAt ℝ ∞ (fun y => F (rootProfileShift r ℓ y)) q :=
    rootPhysical_contDiffAt_scaled (Y := PolarPoint) r ℓ (f := F) (q := q) hF
  have hHnorm : ContDiffAt ℝ ∞ (fun y => H (rootProfileShift r ℓ y)) q :=
    rootPhysical_contDiffAt_scaled (Y := ℝ) r ℓ (f := H) (q := q) hH
  have hFbound : ∀ n : ℕ, 1 ≤ n →
      ‖iteratedFDeriv ℝ n (fun y => F (rootProfileShift r ℓ y)) q‖ ≤
        B n * (1 + p (n + loss) z) := by
    intro n hn
    rw [hFjet n]
    exact hmodel.2.2.2.1 n hn
  have hheight :
      PointwiseMaterialJetBound p loss (rootAffineJetEnvelope ℓ B) z
          H (rootProfileShift r ℓ q) ∧
        PointwiseMaterialJetBound p loss (rootAffineJetEnvelope ℓ B) z
          (fun y => (H y)⁻¹) (rootProfileShift r ℓ q) :=
    rootPhysical_heightJets_transfer
      (E := E) (p := p) (loss := loss) (B := B) (z := z)
      r ℓ hℓ hB (H := H) (h := h) (q := q)
      hHnorm hHpos hmodel.2.2.2.2.1 hmodel.2.2.2.2.2 hHjet
  exact ⟨⟨hF, hH, hHpos,
      rootProfile_unscale_positiveJets
        (E := E) (Y := PolarPoint) (p := p) (loss := loss) (A := B) (z := z)
        (f := F) (q := q) r ℓ hℓ hB hFnorm hFbound,
      hheight.1, hheight.2⟩,
    rootPhysical_jacobian_transfer r ℓ hℓ (F := F) (M := M) (q := q)
      hF hmodel.1 (hFjet 1) hJ⟩

end ContinuousFlexibility.Analysis
