import ContinuousFlexibility.Analysis.MaterialHeightCutoff
import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# Compact radial tests in the actual height model

An annular smooth, periodic function supported in a compact radial subset
of the open annulus belongs to every prescribed physical height space.
The proof checks every actual weighted mixed jet after material pullback.
In particular a smooth radial primitive can be localized while keeping
its values on an entire closed characteristic component.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Compact physical radial support becomes a bounded material radial
support. The bound uses the actual coordinate on that compact set. -/
theorem materialPullback_bounded_radial_support
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hsupp : HasCompactRadialSupport D f) :
    ∃ R : ℝ, 0 < R ∧ ∀ p : PolarPoint, R ≤ |p.1| →
      materialPullback T γ f p = 0 := by
  obtain ⟨K, hK, hKcore, hzero⟩ := hsupp
  have hρ : ContinuousOn T.rho K :=
    (hT.1 T.rho (by simp)).continuousOn.mono hKcore
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hρ
  obtain ⟨_, _, _, _, _, _, _, hInv, _⟩ := hT
  refine ⟨max A 0 + 1, by positivity, ?_⟩
  intro p hp
  have hnot : T.radius p.1 ∉ K := by
    intro hk
    have hb : |p.1| ≤ A := by
      simpa only [Real.norm_eq_abs, (hInv p.1).2] using hA (T.radius p.1) hk
    have hlt : A < max A 0 + 1 := (le_max_left A 0).trans_lt (lt_add_one _)
    exact (not_lt_of_ge (hp.trans hb)) hlt
  simp only [materialPullback, hzero (T.radius p.1) hnot p.2, mul_zero]

/-- Every weighted mixed jet of a compact radial annular smooth field is
an actual cylinder test. -/
theorem weightedPhysicalJet_isCylinderTest_of_compactRadialSupport
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hsupp : HasCompactRadialSupport D f) (a b c : ℕ) :
    IsCylinderTest (weightedPhysicalJet T γ a b c f) := by
  have hF := contDiff_materialPullback (γ := γ) hT hf
  obtain ⟨R, hR, hzero⟩ :=
    materialPullback_bounded_radial_support (γ := γ) hT hsupp
  have hM : ContDiffOn ℝ ∞ T.M (Ioo D.a D.b) := hT.1 T.M (by simp)
  obtain ⟨_, _, _, _, _, _, hradius, hInv, _⟩ := hT
  have hcoord : ContDiff ℝ ∞ (fun p : PolarPoint => T.radius p.1) :=
    hradius.comp contDiff_fst
  have hweight : ContDiff ℝ ∞ (fun p : PolarPoint => T.M (T.radius p.1) ^ c) :=
    (hM.comp_contDiff hcoord (fun p => (hInv p.1).1)).pow c
  refine ⟨hweight.mul (contDiff_mixedDerivative hF a b), ?_, R, hR, ?_⟩
  · rintro ⟨x, θ⟩
    change T.M (T.radius (x + 0)) ^ c *
        mixedDerivative a b (materialPullback T γ f) (x + 0, θ + Real.pi) =
      T.M (T.radius x) ^ c * mixedDerivative a b (materialPullback T γ f) (x, θ)
    rw [add_zero]
    have hh : mixedDerivative a b (materialPullback T γ f) (x, θ + Real.pi) =
        mixedDerivative a b (materialPullback T γ f) (x, θ) :=
      mixedDerivative_angular_periodic
        (materialPullback_angular_periodic (T := T) (γ := γ) hperiod) a b x θ
    exact congrArg (fun v : ℝ => T.M (T.radius x) ^ c * v) hh
  · intro p hp
    simp only [weightedPhysicalJet,
      mixedDerivative_zero_of_radial_support hF hzero a b p hp, mul_zero]

theorem heightMember_of_compactRadialSupport
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0)
    (hsupp : HasCompactRadialSupport D f) :
    HeightMember D T γ f :=
  ⟨hf, heven, hperiod, hzero, fun a b c =>
    (weightedPhysicalJet_isCylinderTest_of_compactRadialSupport
      hT hf hperiod hsupp a b c).memLp⟩

/-- No integrability assumption on the uncut field is needed: the radial
cutoff creates a compactly supported member of the actual height space. -/
theorem materialCutoff_annularSmooth_member
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {χ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hχ : ContDiff ℝ ∞ χ) (hsupp : HasCompactSupport χ) :
    HeightMember D T γ
      (materialCutoffHeight T χ ((annularOpen D).indicator f)) := by
  classical
  let f₀ : PolarPoint → ℝ := (annularOpen D).indicator f
  have hf₀ : ContDiffOn ℝ ∞ f₀ (annularOpen D) :=
    hf.congr (fun p hp => indicator_of_mem hp f)
  have hz₀ : ∀ p, p ∉ annularOpen D → f₀ p = 0 := fun p hp =>
    indicator_of_notMem hp f
  have he₀ (r θ : ℝ) : f₀ (r, -θ) = f₀ (r, θ) := by
    by_cases hr : r ∈ Ioo D.a D.b
    · have hm : (r, -θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
      have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
      simpa only [f₀, indicator_of_mem hm, indicator_of_mem hp] using heven r θ
    · have hm : (r, -θ) ∉ annularOpen D := fun hp => hr hp.1
      have hp : (r, θ) ∉ annularOpen D := fun hp => hr hp.1
      rw [hz₀ (r, -θ) hm, hz₀ (r, θ) hp]
  have hp₀ : Function.Periodic f₀ (0, Real.pi) := by
    intro p
    have hmem : p + (0, Real.pi) ∈ annularOpen D ↔ p ∈ annularOpen D := by
      simp only [annularOpen, mem_prod, Prod.fst_add, Prod.snd_add, add_zero,
        mem_univ, and_true]
    by_cases hp : p ∈ annularOpen D
    · simpa only [f₀, indicator_of_mem hp, indicator_of_mem (hmem.mpr hp)] using hperiod p
    · rw [hz₀ _ (fun h => hp (hmem.mp h)), hz₀ _ hp]
  have hρ : ContDiffOn ℝ ∞ (fun p : PolarPoint => T.rho p.1) (annularOpen D) :=
    (hT.1 T.rho (by simp)).comp contDiffOn_fst (fun p hp => hp.1)
  apply heightMember_of_compactRadialSupport hT
    ((hχ.comp_contDiffOn hρ).mul hf₀)
  · intro r θ
    simp only [materialCutoffHeight, Function.comp_def, he₀ r θ]
  · intro p
    simpa only [materialCutoffHeight, Function.comp_def, Prod.fst_add, add_zero] using
      congrArg (fun t => χ (T.rho p.1) * t) (hp₀ p)
  · intro p hp
    simp only [materialCutoffHeight, hz₀ p hp, mul_zero]
  · exact materialCutoffHeight_compactRadialSupport hT hsupp hz₀

/-- The supplied Sobolev model realizes a radial smooth test which agrees
with a chosen function on the complete closed interval. -/
theorem exists_physical_radial_test
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hT : IsMaterialData D T) (hH : IsSobolevModel D T γ H)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {l r : ℝ} (hl : D.a < l) (hlr : l ≤ r) (hr : r < D.b) :
    ∃ u : H.Space, HasCompactRadialSupport D (H.decode u) ∧
      ∀ t ∈ Icc l r, ∀ θ, H.decode u (t, θ) = h t := by
  obtain ⟨χ, hχ, hsupp, hone⟩ := exists_materialCutoff_one_on_Icc hT hl hlr hr
  let f : PolarPoint → ℝ := fun p => h p.1
  have hf : ContDiffOn ℝ ∞ f (annularOpen D) := (hh.comp contDiff_fst).contDiffOn
  have heven : ∀ t θ, f (t, -θ) = f (t, θ) := fun _ _ => rfl
  have hperiod : Function.Periodic f (0, Real.pi) := by
    intro p
    simp only [f, Prod.fst_add, add_zero]
  have hmember := materialCutoff_annularSmooth_member (γ := γ)
    hT hf heven hperiod hχ hsupp
  obtain ⟨u, hu⟩ := hH.2.2.2.2.1
    (materialCutoffHeight T χ ((annularOpen D).indicator f)) hmember
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact materialCutoffHeight_compactRadialSupport hT hsupp
      (fun p hp => indicator_of_notMem hp f)
  · intro t ht θ
    have hp : (t, θ) ∈ annularOpen D :=
      ⟨⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩, mem_univ _⟩
    rw [hu]
    simp only [materialCutoffHeight, hone t ht, one_mul, indicator_of_mem hp, f]

end ContinuousFlexibility.Statements
