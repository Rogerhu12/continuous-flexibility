import ContinuousFlexibility.Analysis.N06StripPerturbation
import ContinuousFlexibility.Analysis.CanonicalSourceMeasure
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smooth inverse of the actual clamped strip perturbation

The derivative bound on the closed strip supplies the global Lipschitz
bound. Its smallness also makes every interior differential invertible.
The inverse constructed in the preceding module therefore is smooth
throughout the open strip. All domain and inverse identities refer to
that same function.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped NNReal ContDiff Topology

theorem n06_stripCorrection_lipschitz_of_derivative {g : PolarPoint → PolarPoint}
    (hg : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ), DifferentiableAt ℝ g p)
    (hbound : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ), ‖fderiv ℝ g p‖ ≤ (1 / 2 : ℝ)) :
    LipschitzOnWith (1 / 2 : ℝ≥0) g (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le hg
    (fun p hp => by exact_mod_cast hbound p hp)
  exact (convex_Icc (0 : ℝ) 1).prod convex_univ

private theorem n06_id_add_derivative_equiv {g : PolarPoint → PolarPoint} {p : PolarPoint}
    (hg : DifferentiableAt ℝ g p) (hbound : ‖fderiv ℝ g p‖ ≤ (1 / 2 : ℝ)) :
    ∃ e : PolarPoint ≃L[ℝ] PolarPoint,
      HasFDerivAt (fun x => x + g x) (e : PolarPoint →L[ℝ] PolarPoint) p := by
  have hL : LipschitzWith (1 / 2 : ℝ≥0) (fderiv ℝ g p) :=
    (fderiv ℝ g p).lipschitzWith.weaken (by exact_mod_cast hbound)
  let A : PolarPoint →L[ℝ] PolarPoint := ContinuousLinearMap.id ℝ PolarPoint + fderiv ℝ g p
  have hA : Function.Bijective A := n06_halfLipschitz_id_add_bijective hL
  let e : PolarPoint ≃L[ℝ] PolarPoint := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.injective) (LinearMap.range_eq_top.mpr hA.surjective)
  have he : (e : PolarPoint →L[ℝ] PolarPoint) = A :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  refine ⟨e, ?_⟩
  rw [he]
  exact (hasFDerivAt_id p).add hg.hasFDerivAt

/-- The original smooth map has a nonzero Jacobian even at the strip
endpoints. This uses its genuine derivative, without differentiating
the clamped extension there. -/
theorem n06_smallStripCorrection_jacobian_ne_zero
    {g : PolarPoint → PolarPoint} {p : PolarPoint}
    (hg : DifferentiableAt ℝ g p) (hbound : ‖fderiv ℝ g p‖ ≤ (1 / 2 : ℝ)) :
    planeJacobian (fun x => x + g x) p ≠ 0 := by
  obtain ⟨e, he⟩ := n06_id_add_derivative_equiv hg hbound
  rw [planeJacobian_eq_fderiv_det, he.fderiv]
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- On the interior the clamped extension has the exact original germ. -/
theorem n06UnitStripPerturbation_germ {g : PolarPoint → PolarPoint} {p : PolarPoint}
    (hp : p.1 ∈ Ioo (0 : ℝ) 1) :
    n06UnitStripPerturbation g =ᶠ[𝓝 p] (fun x => x + g x) := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp, mem_univ p.2⟩]
    with x hx
  exact n06UnitStripPerturbation_on_closed (mem_Icc_of_Ioo hx.1)

private theorem n06_invFun_contDiffAt_of_invertible
    {f : PolarPoint → PolarPoint} {p : PolarPoint} {e : PolarPoint ≃L[ℝ] PolarPoint}
    (hf : ContDiffAt ℝ ∞ f p) (hd : HasFDerivAt f (e : PolarPoint →L[ℝ] PolarPoint) p)
    (hinj : Function.Injective f) :
    ContDiffAt ℝ ∞ (Function.invFun f) (f p) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hstrict := hf.hasStrictFDerivAt' hd hn
  have heq := hstrict.localInverse_unique
    (Filter.Eventually.of_forall (Function.leftInverse_invFun hinj))
  exact (hf.to_localInverse hd hn).congr_of_eventuallyEq heq

/-- The global inverse is smooth at the image of every interior point.
No differentiability of the radial clamp at its two endpoints is used. -/
theorem n06UnitStripPerturbation_inverse_contDiffAt
    {g : PolarPoint → PolarPoint}
    (hlip : LipschitzOnWith (1 / 2 : ℝ≥0) g (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))
    {p : PolarPoint} (hp : p.1 ∈ Ioo (0 : ℝ) 1) (hg : ContDiffAt ℝ ∞ g p) :
    ContDiffAt ℝ ∞ (Function.invFun (n06UnitStripPerturbation g))
      (n06UnitStripPerturbation g p) := by
  have hnhds : Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
    Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp, mem_univ p.2⟩)
      (fun x hx => ⟨mem_Icc_of_Ioo hx.1, hx.2⟩)
  have hb : ‖fderiv ℝ g p‖ ≤ (1 / 2 : ℝ) := by
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      norm_fderiv_le_of_lipschitzOn ℝ hnhds hlip
  obtain ⟨e, he⟩ := n06_id_add_derivative_equiv (hg.differentiableAt (by simp)) hb
  have hnear := n06UnitStripPerturbation_germ (g := g) hp
  exact n06_invFun_contDiffAt_of_invertible
    ((contDiffAt_id.add hg).congr_of_eventuallyEq hnear)
    (he.congr_of_eventuallyEq hnear)
    (n06UnitStripPerturbation_bijective hlip).1.injective

/-- One explicit inverse has the correct domain, both inverse
identities and smoothness on the whole open strip. -/
theorem n06_smallStripPerturbation_smooth_inverse {g : PolarPoint → PolarPoint}
    (hg : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ), ContDiffAt ℝ ∞ g p)
    (hbound : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ), ‖fderiv ℝ g p‖ ≤ (1 / 2 : ℝ))
    (hzero : ∀ θ, (g (0, θ)).1 = 0 ∧ (g (1, θ)).1 = 0) :
    let G := Function.invFun (n06UnitStripPerturbation g)
    MapsTo (fun p => p + g p) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
    MapsTo G (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
    (∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), G (p + g p) = p) ∧
    (∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), G p + g (G p) = p) ∧
    ContDiffOn ℝ ∞ G (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  dsimp only
  have hlip := n06_stripCorrection_lipschitz_of_derivative
    (fun p hp => (hg p hp).differentiableAt (by simp)) hbound
  have hb := (n06UnitStripPerturbation_bijective hlip).1
  have hl := Function.leftInverse_invFun hb.injective
  have hr := Function.rightInverse_invFun hb.surjective
  have hm : MapsTo (Function.invFun (n06UnitStripPerturbation g))
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    intro p hp
    refine ⟨(n06UnitStripPerturbation_mem_open_iff hlip hzero _).mp ?_, mem_univ _⟩
    rw [hr p]
    exact hp.1
  refine ⟨(n06_smallStripPerturbation_bijOn hlip hzero).mapsTo, hm, ?_, ?_, ?_⟩
  · intro p hp
    rw [← n06UnitStripPerturbation_on_closed (g := g) (mem_Icc_of_Ioo hp.1)]
    exact hl p
  · intro p hp
    have he := n06UnitStripPerturbation_on_closed (g := g) (mem_Icc_of_Ioo (hm hp).1)
    exact he.symm.trans (hr p)
  · intro p hp
    have hq := hm hp
    have hc := n06UnitStripPerturbation_inverse_contDiffAt hlip hq.1
      (hg _ ⟨mem_Icc_of_Ioo hq.1, mem_univ _⟩)
    rw [hr p] at hc
    exact hc.contDiffWithinAt

end ContinuousFlexibility.Analysis
