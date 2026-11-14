module

public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
public import ContinuousFlexibility.Analysis.MixedDerivativeLocality
public import ContinuousFlexibility.Analysis.N01cHeightParameterJets

/-!
# Linearity of the actual material jets on the supplied height space

The smoothness of the material pullback justifies additivity of every
mixed derivative. The resulting maps evaluate the actual weighted jets,
so linear difference quotients can be estimated without replacing those
jets by formal derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem n02n03_mixedDerivative_add_of_contDiff {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q + g q) p =
      mixedDerivative a b f p + mixedDerivative a b g p := by
  have h := mixedDerivative_sub_of_contDiffOn isOpen_univ hf.contDiffOn
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : PolarPoint => (-1 : ℝ))).mul hg).contDiffOn
      a b (mem_univ p)
  have heq : (fun q : PolarPoint => f q - (-1) * g q) = fun q => f q + g q := by
    funext q
    ring
  rw [heq, mixedDerivative_const_mul] at h
  simpa only [neg_one_mul, sub_neg_eq_add] using h

theorem weightedPhysicalJet_add {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f g : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hg : ContDiffOn ℝ ∞ g (annularOpen D)) (a b c : ℕ) (p : PolarPoint) :
    weightedPhysicalJet T γ a b c (fun q => f q + g q) p =
      weightedPhysicalJet T γ a b c f p + weightedPhysicalJet T γ a b c g p := by
  have heq : materialPullback T γ (fun q => f q + g q) =
      fun q => materialPullback T γ f q + materialPullback T γ g q := by
    funext q
    simp only [materialPullback, mul_add]
  unfold weightedPhysicalJet
  rw [heq, n02n03_mixedDerivative_add_of_contDiff (contDiff_materialPullback hT hf)
    (contDiff_materialPullback hT hg), mul_add]

theorem weightedPhysicalJet_const_mul {T : MaterialData} {γ : ℝ}
    (d : ℝ) (f : PolarPoint → ℝ) (a b c : ℕ) (p : PolarPoint) :
    weightedPhysicalJet T γ a b c (fun q => d * f q) p =
      d * weightedPhysicalJet T γ a b c f p := by
  have heq : materialPullback T γ (fun q => d * f q) =
      fun q => d * materialPullback T γ f q := by
    funext q
    dsimp only [materialPullback]
    ring
  unfold weightedPhysicalJet
  rw [heq, mixedDerivative_const_mul]
  ring

def heightWeightedJetLinear {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {H : SobolevModelData} (hH : IsSobolevModel D T γ H) (hT : IsMaterialData D T)
    (a b c : ℕ) : H.Space →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun u := weightedPhysicalJet T γ a b c (H.decode u)
  map_add' u v := by
    funext p
    simp only [map_add, Pi.add_apply]
    exact weightedPhysicalJet_add hT (hH.2.2.2.1 u).1 (hH.2.2.2.1 v).1 a b c p
  map_smul' d u := by
    funext p
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact weightedPhysicalJet_const_mul d (H.decode u) a b c p

theorem heightWeightedJetLinear_apply {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {H : SobolevModelData} (hH : IsSobolevModel D T γ H) (hT : IsMaterialData D T)
    (a b c : ℕ) (u : H.Space) (p : PolarPoint) :
    heightWeightedJetLinear hH hT a b c u p =
      weightedPhysicalJet T γ a b c (H.decode u) p := rfl

end ContinuousFlexibility.Statements
