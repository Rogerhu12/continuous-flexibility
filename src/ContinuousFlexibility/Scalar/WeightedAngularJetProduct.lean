import ContinuousFlexibility.Scalar.WeightedAngularDifferentiation
import ContinuousFlexibility.Scalar.WeightedDecodedProductMap
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# Products of two actual odd angular jets

The second angular derivative product rule realizes the product of two odd
first derivatives as an even weighted height. The construction uses only the
actual even multiplication and angular-second-derivative maps.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

theorem angularPartial_product_twice
    {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : PolarPoint) :
    angularPartial (angularPartial (fun q => f q * g q)) p =
      angularPartial (angularPartial f) p * g p +
        2 * angularPartial f p * angularPartial g p +
          f p * angularPartial (angularPartial g) p := by
  have hf' : ContDiff ℝ ∞ (angularPartial f) :=
    contDiff_iff_contDiffAt.mpr fun q => contDiffAt_angularPartial hf.contDiffAt (by simp)
  have hg' : ContDiff ℝ ∞ (angularPartial g) :=
    contDiff_iff_contDiffAt.mpr fun q => contDiffAt_angularPartial hg.contDiffAt (by simp)
  have he : angularPartial (fun q => f q * g q) =
      fun q => angularPartial f q * g q + f q * angularPartial g q := by
    funext q
    exact angularPartial_mul (hf.differentiable (by simp) q) (hg.differentiable (by simp) q)
  rw [he, angularPartial_add
    ((hf'.mul hg).differentiable (by simp) p) ((hf.mul hg').differentiable (by simp) p),
    angularPartial_mul (hf'.differentiable (by simp) p) (hg.differentiable (by simp) p),
    angularPartial_mul (hf.differentiable (by simp) p) (hg'.differentiable (by simp) p)]
  ring

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- A genuine continuous bilinear map whose decoder is the product of the
two first angular derivatives. -/
def angularJetProductMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => A.Space) A.Space :=
  let L := angularSecondCLM hT hA
  let M := decodedProductMap hT hA hinterp hγ 1
  (1 / 2 : ℝ) •
    (L.compContinuousMultilinearMap M -
      M.compContinuousLinearMap ![L, ContinuousLinearMap.id ℝ A.Space] -
      M.compContinuousLinearMap ![ContinuousLinearMap.id ℝ A.Space, L])

theorem angularJetProductMap_apply
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (u : Fin 2 → A.Space) :
    angularJetProductMap hT hA hinterp hγ u =
      (1 / 2 : ℝ) •
        (angularSecondCLM hT hA (decodedProductMap hT hA hinterp hγ 1 u) -
          decodedProductMap hT hA hinterp hγ 1 ![angularSecondCLM hT hA (u 0), u 1] -
          decodedProductMap hT hA hinterp hγ 1 ![u 0, angularSecondCLM hT hA (u 1)]) := by
  let L := angularSecondCLM hT hA
  have hs₁ : (fun i : Fin 2 => (![L, ContinuousLinearMap.id ℝ A.Space] i) (u i)) =
      ![L (u 0), u 1] := by
    funext i
    fin_cases i <;> simp
  have hs₂ : (fun i : Fin 2 => (![ContinuousLinearMap.id ℝ A.Space, L] i) (u i)) =
      ![u 0, L (u 1)] := by
    funext i
    fin_cases i <;> simp
  simp only [angularJetProductMap, smul_apply, sub_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hs₁, hs₂]

theorem decode_angularJetProductMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) (u : Fin 2 → A.Space) :
    A.decode (angularJetProductMap hT hA hinterp hγ.le u) =
      fun p => angularPartial (A.decode (u 0)) p * angularPartial (A.decode (u 1)) p := by
  have hu₀ := (heightMember_contDiff_and_flatJets hT hγ (hA.2.2.2.1 (u 0))).1
  have hu₁ := (heightMember_contDiff_and_flatJets hT hγ (hA.2.2.2.1 (u 1))).1
  rw [angularJetProductMap_apply]
  simp only [map_smul, map_sub]
  funext p
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [decode_angularSecondCLM, decode_decodedProductMap,
    decode_decodedProductMap, decode_decodedProductMap]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    decode_angularSecondCLM]
  rw [angularPartial_product_twice hu₀ hu₁]
  ring

end SobolevModelData

end ContinuousFlexibility.Statements
