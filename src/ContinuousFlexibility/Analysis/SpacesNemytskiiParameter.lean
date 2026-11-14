module

public import ContinuousFlexibility.Analysis.SpacesNemytskiiKernels
public import ContinuousFlexibility.Analysis.SpacesParameterJets

/-!
# Parameter derivatives of the actual composition kernels

On every affine base curve the next normalized kernel is the actual
derivative. Parameter differentiation commutes with all spatial jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

theorem spacesNemytskiiMaterial_affine_contDiff (γ : ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (k : ℕ) (u w : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) :
    ContDiff ℝ ∞ (fun z : ℝ × PolarPoint =>
      spacesNemytskiiMaterial hT γ F k (u + z.1 • w) v z.2) := by
  have hH (α : ℝ) : ContDiff ℝ ∞ (fun z : ℝ × PolarPoint => T.H (T.radius z.2.1) ^ α) :=
    (spacesRadialMultiplier_materialH hT α).contDiff.comp (contDiff_fst.comp contDiff_snd)
  have hU : ContDiff ℝ ∞ (fun z : ℝ × PolarPoint =>
      spacesPhysicalRepresentative hT u z.2 + z.1 * spacesPhysicalRepresentative hT w z.2) :=
    ((spacesPhysicalRepresentative_contDiff hT u).comp contDiff_snd).add
      (contDiff_fst.mul ((spacesPhysicalRepresentative_contDiff hT w).comp contDiff_snd))
  have hV : ContDiff ℝ ∞ (fun z : ℝ × PolarPoint =>
      ∏ i, spacesPhysicalRepresentative hT (v i) z.2) :=
    contDiff_prod (fun i _ => (spacesPhysicalRepresentative_contDiff hT (v i)).comp contDiff_snd)
  simpa only [spacesNemytskiiMaterial_apply, spacesPhysicalRepresentative_add,
    spacesPhysicalRepresentative_smul, Function.comp_apply] using
    ((hH (((k : ℝ) - 1) * γ)).mul
      ((spaces_scalar_contDiff_iteratedDeriv hF k).comp ((hH γ).mul hU))).mul hV

theorem spacesNemytskiiMaterial_affine_hasDerivAt (γ : ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (k : ℕ) (u w : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) (t : ℝ) (p : PolarPoint) :
    HasDerivAt (fun r => spacesNemytskiiMaterial hT γ F k (u + r • w) v p)
      (spacesNemytskiiMaterial hT γ F (k + 1) (u + t • w) (Fin.cons w v) p) t := by
  let H := T.H (T.radius p.1)
  let U := spacesPhysicalRepresentative hT u p
  let W := spacesPhysicalRepresentative hT w p
  let V := ∏ i, spacesPhysicalRepresentative hT (v i) p
  have hH : 0 < H := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.1
  have harg : HasDerivAt (fun r : ℝ => H ^ γ * (U + r * W)) (H ^ γ * W) t := by
    convert ((hasDerivAt_const t U).add ((hasDerivAt_id' t).mul_const W)).const_mul (H ^ γ) using 1
    ring
  have hscalar : HasDerivAt (iteratedDeriv k F)
      (iteratedDeriv (k + 1) F (H ^ γ * (U + t * W))) (H ^ γ * (U + t * W)) := by
    rw [iteratedDeriv_succ]
    exact ((spaces_scalar_contDiff_iteratedDeriv hF k).differentiable (by simp) _).hasDerivAt
  have hd := ((hscalar.comp t harg).const_mul (H ^ (((k : ℝ) - 1) * γ))).mul_const V
  have hpow : H ^ (((k : ℝ) - 1) * γ) * H ^ γ =
      H ^ ((((k + 1 : ℕ) : ℝ) - 1) * γ) := by
    rw [← Real.rpow_add hH]
    congr 1
    push_cast
    ring
  have he : (fun r => spacesNemytskiiMaterial hT γ F k (u + r • w) v p) =
      fun r => H ^ (((k : ℝ) - 1) * γ) * iteratedDeriv k F (H ^ γ * (U + r * W)) * V := by
    funext r
    simp only [spacesNemytskiiMaterial_apply, spacesPhysicalRepresentative_add,
      spacesPhysicalRepresentative_smul, H, U, W, V]
  rw [he]
  convert hd using 1
  · rfl
  · simp only [spacesNemytskiiMaterial_apply, spacesPhysicalRepresentative_add,
      spacesPhysicalRepresentative_smul, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change H ^ ((((k + 1 : ℕ) : ℝ) - 1) * γ) *
      iteratedDeriv (k + 1) F (H ^ γ * (U + t * W)) * (W * V) = _
    rw [← hpow]
    ring

theorem spacesNemytskiiMaterial_weightedJet_affine_hasDerivAt (γ : ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (k a b c : ℕ) (u w : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) (t : ℝ) (p : PolarPoint) :
    HasDerivAt (fun r => T.M (T.radius p.1) ^ c * mixedDerivative a b
      (spacesNemytskiiMaterial hT γ F k (u + r • w) v) p)
      (T.M (T.radius p.1) ^ c * mixedDerivative a b
        (spacesNemytskiiMaterial hT γ F (k + 1) (u + t • w) (Fin.cons w v)) p) t := by
  have hd := spaces_hasDerivAt_parameter_mixedDerivative
    (spacesNemytskiiMaterial_affine_contDiff hT γ hF k u w v) a b t p
  have he : (fun q => deriv (fun r => spacesNemytskiiMaterial hT γ F k (u + r • w) v q) t) =
      spacesNemytskiiMaterial hT γ F (k + 1) (u + t • w) (Fin.cons w v) := by
    funext q
    exact (spacesNemytskiiMaterial_affine_hasDerivAt hT γ hF k u w v t q).deriv
  rw [he] at hd
  exact hd.const_mul (T.M (T.radius p.1) ^ c)

end ContinuousFlexibility.Statements
