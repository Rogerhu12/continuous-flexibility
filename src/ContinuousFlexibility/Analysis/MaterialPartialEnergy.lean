import ContinuousFlexibility.Analysis.MaterialInverseEllJets
import ContinuousFlexibility.Analysis.MaterialMixedMultiplier
import ContinuousFlexibility.Analysis.PhysicalJetLinearity

/-!
# Ordinary physical partial derivatives preserve the weighted energy class

The actual radial derivative in material coordinates is the inverse
material length times a first derivative plus a bounded logarithmic
weight term. Every derivative of the inverse length costs the same
single power of M. Angular differentiation simply shifts the angular
jet index. These identities concern the actual total partial derivatives.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem materialPullback_radialPartial
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (p : PolarPoint) :
    materialPullback T γ (radialPartial f) p =
      (T.ell (T.radius p.1))⁻¹ *
        (radialPartial (materialPullback T γ f) p +
          γ * deriv (fun t => Real.log (T.H (T.radius t))) p.1 *
            materialPullback T γ f p) := by
  let L : ℝ → ℝ := fun t => Real.log (T.H (T.radius t))
  let w : ℝ → ℝ := fun t => T.H (T.radius t) ^ (-γ)
  let G : PolarPoint → ℝ := materialPullback T γ f
  have hrange (t : ℝ) : T.radius t ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 t).1
  have hH (t : ℝ) : 0 < T.H (T.radius t) := (hT.2.1 _ (hrange t)).2.1
  have hell : T.ell (T.radius p.1) ≠ 0 := (hT.2.1 _ (hrange p.1)).1.ne'
  have hL : ContDiff ℝ ∞ L := materialRadius_comp_contDiff hT
    ((hT.1 T.H (by simp)).log (fun r hr => (hT.2.1 r hr).2.1.ne'))
  have hweq : w = (fun t => Real.exp ((-γ) * L t)) := by
    funext t
    dsimp only [w, L]
    rw [Real.rpow_def_of_pos (hH t)]
    congr 1
    ring
  have hw : HasDerivAt w (w p.1 * ((-γ) * deriv L p.1)) p.1 := by
    rw [hweq]
    exact (((hL.differentiable (by simp) p.1).hasDerivAt).const_mul (-γ)).exp
  have hp : (T.radius p.1, p.2) ∈ annularOpen D := ⟨hrange p.1, mem_univ _⟩
  have hfp : DifferentiableAt ℝ f (T.radius p.1, p.2) :=
    (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hcurve₀ : HasDerivAt (fun t => f (T.radius t, p.2))
      (fderiv ℝ f (T.radius p.1, p.2) (T.ell (T.radius p.1), 0)) p.1 := by
    simpa only [Function.comp_def] using hfp.hasFDerivAt.comp_hasDerivAt p.1
      ((hT.2.2.2.2.2.2.2.2.2.1 p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hcurve : HasDerivAt (fun t => f (T.radius t, p.2))
      (T.ell (T.radius p.1) * radialPartial f (T.radius p.1, p.2)) p.1 := by
    apply hcurve₀.congr_deriv
    have hvec : (T.ell (T.radius p.1), (0 : ℝ)) =
        T.ell (T.radius p.1) • ((1 : ℝ), (0 : ℝ)) := by
      ext <;> simp
    rw [hvec]
    simp only [radialPartial, map_smul, smul_eq_mul]
  have hprod : HasDerivAt (fun t => G (t, p.2))
      (w p.1 * ((-γ) * deriv L p.1) * f (T.radius p.1, p.2) +
        w p.1 * (T.ell (T.radius p.1) * radialPartial f (T.radius p.1, p.2))) p.1 := by
    simpa only [G, w, materialPullback] using hw.mul hcurve
  have hG : ContDiff ℝ ∞ G := contDiff_materialPullback hT hf
  have hGder : HasDerivAt (fun t => G (t, p.2)) (radialPartial G p) p.1 := by
    simpa only [Function.comp_def, radialPartial] using
      (hG.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1
        ((hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hid := hGder.unique hprod
  change w p.1 * radialPartial f (T.radius p.1, p.2) =
    (T.ell (T.radius p.1))⁻¹ *
      (radialPartial G p + γ * deriv L p.1 * (w p.1 * f (T.radius p.1, p.2)))
  rw [hid]
  field_simp [hell]
  <;> ring

theorem materialPullback_angularPartial
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (p : PolarPoint) :
    materialPullback T γ (angularPartial f) p =
      angularPartial (materialPullback T γ f) p := by
  have hp : (T.radius p.1, p.2) ∈ annularOpen D :=
    ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩
  have hfp : DifferentiableAt ℝ f (T.radius p.1, p.2) :=
    (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun t => f (T.radius p.1, t))
      (angularPartial f (T.radius p.1, p.2)) p.2 := by
    simpa only [Function.comp_def, angularPartial] using hfp.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 (T.radius p.1)).prodMk (hasDerivAt_id' p.2))
  have hprod : HasDerivAt (fun t => materialPullback T γ f (p.1, t))
      (materialPullback T γ (angularPartial f) p) p.2 := by
    simpa only [materialPullback] using hcurve.const_mul (T.H (T.radius p.1) ^ (-γ))
  have hG := contDiff_materialPullback hT hf
  have hGder : HasDerivAt (fun t => materialPullback T γ f (p.1, t))
      (angularPartial (materialPullback T γ f) p) p.2 := by
    simpa only [Function.comp_def, angularPartial] using
      (hG.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2))
  exact hprod.unique hGder

theorem memLp_weighted_mixed_radialPartial
    {W G : PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (hLp : ∀ a b c, MemLp (fun p => W p ^ c * mixedDerivative a b G p)
      2 materialCylinderMeasure) (a b c : ℕ) :
    MemLp (fun p => W p ^ c * mixedDerivative a b (radialPartial G) p)
      2 materialCylinderMeasure := by
  apply (hLp (a + 1) b c).ae_eq
  exact Eventually.of_forall fun p => by
    rw [mixedDerivative_radialPartial isOpen_univ hG.contDiffOn a b (mem_univ p)]

theorem memLp_weighted_mixed_angularPartial
    {W G : PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (hLp : ∀ a b c, MemLp (fun p => W p ^ c * mixedDerivative a b G p)
      2 materialCylinderMeasure) (a b c : ℕ) :
    MemLp (fun p => W p ^ c * mixedDerivative a b (angularPartial G) p)
      2 materialCylinderMeasure := by
  apply (hLp a (b + 1) c).ae_eq
  exact Eventually.of_forall fun p => by
    rw [mixedDerivative_angularPartial isOpen_univ hG.contDiffOn a b (mem_univ p)]

theorem memLp_weightedPhysicalJet_angularPartial
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure)
    (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c (angularPartial f)) 2 materialCylinderMeasure := by
  have heq : materialPullback T γ (angularPartial f) =
      angularPartial (materialPullback T γ f) := funext (materialPullback_angularPartial hT hf)
  simpa only [weightedPhysicalJet, heq] using
    memLp_weighted_mixed_angularPartial (contDiff_materialPullback hT hf) hLp a b c

theorem materialLogH_radius_deriv_mixed_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (γ : ℝ) (a b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative a b
        (fun q => γ * deriv (fun t => Real.log (T.H (T.radius t))) q.1) p| ≤ K := by
  cases b with
  | zero =>
    obtain ⟨K, hK, hb⟩ := materialLogH_radius_deriv_iteratedDeriv_bounded hT a
    refine ⟨|γ| * K, mul_nonneg (abs_nonneg _) hK, fun p => ?_⟩
    simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_const_mul_field, abs_mul]
    exact mul_le_mul_of_nonneg_left (hb p.1) (abs_nonneg γ)
  | succ b =>
    refine ⟨0, le_rfl, fun p => ?_⟩
    simp [mixedDerivative, iteratedDeriv_const]

theorem memLp_weightedPhysicalJet_radialPartial
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure)
    (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c (radialPartial f)) 2 materialCylinderMeasure := by
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let G : PolarPoint → ℝ := materialPullback T γ f
  let L (p : PolarPoint) : ℝ :=
    γ * deriv (fun t => Real.log (T.H (T.radius t))) p.1
  let A (p : PolarPoint) : ℝ := (T.ell (T.radius p.1))⁻¹
  let V (p : PolarPoint) : ℝ := radialPartial G p + L p * G p
  have hrange (t : ℝ) : T.radius t ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 t).1
  have hW : Continuous W :=
    ((materialRadius_comp_contDiff hT (hT.1 T.M (by simp))).comp contDiff_fst).continuous
  have hWpos (p : PolarPoint) : 0 ≤ W p := zero_le_one.trans (hT.2.1 _ (hrange p.1)).2.2.2
  have hG : ContDiff ℝ ∞ G := contDiff_materialPullback hT hf
  have hR : ContDiff ℝ ∞ (radialPartial G) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact contDiffAt_radialPartial hG.contDiffAt (m := ∞) (by simp)
  have hlog : ContDiff ℝ ∞ (fun t => Real.log (T.H (T.radius t))) :=
    materialRadius_comp_contDiff hT
      ((hT.1 T.H (by simp)).log (fun r hr => (hT.2.1 r hr).2.1.ne'))
  have hL : ContDiff ℝ ∞ L :=
    contDiff_const.mul ((contDiff_infty_iff_deriv.mp hlog).2.comp contDiff_fst)
  have hA : ContDiff ℝ ∞ A := (materialInvEll_radius_contDiff hT).comp contDiff_fst
  have hLb (i j : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p,
      |mixedDerivative i j L p| ≤ K * W p ^ 0 := by
    obtain ⟨K, hK, hb⟩ := materialLogH_radius_deriv_mixed_bounded hT γ i j
    exact ⟨K, hK, fun p => by simpa only [pow_zero, mul_one] using hb p⟩
  have hAb (i j : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p,
      |mixedDerivative i j A p| ≤ K * W p ^ 1 := by
    obtain ⟨K, hK, hb⟩ := materialInvEll_mixedDerivative_bound hT i j
    exact ⟨K, hK, fun p => by simpa only [pow_one] using hb p⟩
  have hLG (i j k : ℕ) :
      MemLp (fun p => W p ^ k * mixedDerivative i j (fun q => L q * G q) p)
        2 materialCylinderMeasure :=
    memLp_weighted_mixed_product hW hWpos hL hG 0 hLb hLp i j k
  have hVLp (i j k : ℕ) :
      MemLp (fun p => W p ^ k * mixedDerivative i j V p) 2 materialCylinderMeasure := by
    have hfirst := memLp_weighted_mixed_radialPartial hG hLp i j k
    have hsecond := hLG i j k
    apply (hfirst.add hsecond).ae_eq
    exact Eventually.of_forall fun p => by
      simp only [Pi.add_apply, V, mixedDerivative_add_of_contDiff hR (hL.mul hG), mul_add]
  have hV : ContDiff ℝ ∞ V := hR.add (hL.mul hG)
  have hproduct := memLp_weighted_mixed_product hW hWpos hA hV 1 hAb hVLp a b c
  have heq : materialPullback T γ (radialPartial f) = (fun p => A p * V p) :=
    funext (materialPullback_radialPartial hT hf)
  simpa only [weightedPhysicalJet, heq] using hproduct

end ContinuousFlexibility.Statements
