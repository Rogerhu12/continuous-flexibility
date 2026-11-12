import ContinuousFlexibility.Analysis.MaterialMultiplierEnvelopes

/-!
# Uniform L² envelopes for the actual symmetric divergence

The material-coordinate identities for ordinary partial derivatives
preserve common envelopes of families. Hence bounded smooth coefficient
families acting on one height field, or on an already dominated family
of height fields, give the common second-energy bounds needed for the
projective source derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem WeightedMixedJetEnvelopes.radialPartial {ι : Type*}
    {W : PolarPoint → ℝ} {f : ι → PolarPoint → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (henv : WeightedMixedJetEnvelopes W f) :
    WeightedMixedJetEnvelopes W (fun i => ContinuousFlexibility.radialPartial (f i)) := by
  intro a b c
  obtain ⟨G, hG, hGpos, hb⟩ := henv (a + 1) b c
  refine ⟨G, hG, hGpos, fun i p => ?_⟩
  rw [mixedDerivative_radialPartial isOpen_univ (hf i).contDiffOn a b (mem_univ p)]
  exact hb i p

theorem WeightedMixedJetEnvelopes.angularPartial {ι : Type*}
    {W : PolarPoint → ℝ} {f : ι → PolarPoint → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (henv : WeightedMixedJetEnvelopes W f) :
    WeightedMixedJetEnvelopes W (fun i => ContinuousFlexibility.angularPartial (f i)) := by
  intro a b c
  obtain ⟨G, hG, hGpos, hb⟩ := henv a (b + 1) c
  refine ⟨G, hG, hGpos, fun i p => ?_⟩
  rw [mixedDerivative_angularPartial isOpen_univ (hf i).contDiffOn a b (mem_univ p)]
  exact hb i p

theorem PhysicalJetEnvelopes.add
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f g : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (annularOpen D))
    (hfenv : PhysicalJetEnvelopes T γ f) (hgenv : PhysicalJetEnvelopes T γ g) :
    PhysicalJetEnvelopes T γ (fun i p => f i p + g i p) := by
  intro a b c
  obtain ⟨F, hF, hFpos, hfb⟩ := hfenv a b c
  obtain ⟨G, hG, hGpos, hgb⟩ := hgenv a b c
  refine ⟨fun p => F p + G p, hF.add hG,
    fun p => add_nonneg (hFpos p) (hGpos p), fun i p => ?_⟩
  rw [weightedPhysicalJet_add hT (hf i) (hg i)]
  exact (abs_add_le _ _).trans (add_le_add (hfb i p) (hgb i p))

theorem PhysicalJetEnvelopes.congr_on_annularOpen
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f g : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (henv : PhysicalJetEnvelopes T γ f)
    (heq : ∀ i, EqOn (f i) (g i) (annularOpen D)) :
    PhysicalJetEnvelopes T γ g := by
  intro a b c
  obtain ⟨G, hG, hGpos, hb⟩ := henv a b c
  refine ⟨G, hG, hGpos, fun i p => ?_⟩
  rw [← weightedPhysicalJet_eq_of_eqOn_annularOpen hT (heq i) a b c]
  exact hb i p

theorem PhysicalJetEnvelopes.angularPartial
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (henv : PhysicalJetEnvelopes T γ f) :
    PhysicalJetEnvelopes T γ (fun i => ContinuousFlexibility.angularPartial (f i)) := by
  have hG (i : ι) : ContDiff ℝ ∞ (materialPullback T γ (f i)) :=
    contDiff_materialPullback hT (hf i)
  have hGenv := physicalJetEnvelopes_iff_material.mp henv
  have henv' := WeightedMixedJetEnvelopes.angularPartial hG hGenv
  apply physicalJetEnvelopes_iff_material.mpr
  apply henv'.congr
  intro i
  exact (funext (n02n03_materialPullback_angularPartial hT (hf i))).symm

theorem PhysicalJetEnvelopes.radialPartial
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (henv : PhysicalJetEnvelopes T γ f) :
    PhysicalJetEnvelopes T γ (fun i => ContinuousFlexibility.radialPartial (f i)) := by
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let G (i : ι) : PolarPoint → ℝ := materialPullback T γ (f i)
  let L (p : PolarPoint) : ℝ :=
    γ * deriv (fun t => Real.log (T.H (T.radius t))) p.1
  let A (p : PolarPoint) : ℝ := (T.ell (T.radius p.1))⁻¹
  let V (i : ι) (p : PolarPoint) : ℝ := ContinuousFlexibility.radialPartial (G i) p + L p * G i p
  have hrange (t : ℝ) : T.radius t ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 t).1
  have hW (p : PolarPoint) : 0 ≤ W p := zero_le_one.trans (hT.2.1 _ (hrange p.1)).2.2.2
  have hG (i : ι) : ContDiff ℝ ∞ (G i) := contDiff_materialPullback hT (hf i)
  have hR (i : ι) : ContDiff ℝ ∞ (ContinuousFlexibility.radialPartial (G i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact contDiffAt_radialPartial (hG i).contDiffAt (m := ∞) (by simp)
  have hlog : ContDiff ℝ ∞ (fun t => Real.log (T.H (T.radius t))) :=
    materialRadius_comp_contDiff hT
      ((hT.1 T.H (by simp)).log (fun r hr => (hT.2.1 r hr).2.1.ne'))
  have hL : ContDiff ℝ ∞ L :=
    contDiff_const.mul ((contDiff_infty_iff_deriv.mp hlog).2.comp contDiff_fst)
  have hA : ContDiff ℝ ∞ A := (materialInvEll_radius_contDiff hT).comp contDiff_fst
  have hLb (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (_ : ι) p,
      |mixedDerivative a b L p| ≤ K * W p ^ 0 := by
    obtain ⟨K, hK, hb⟩ := materialLogH_radius_deriv_mixed_bounded hT γ a b
    exact ⟨K, hK, fun _ p => by simpa only [pow_zero, mul_one] using hb p⟩
  have hAb (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (_ : ι) p,
      |mixedDerivative a b A p| ≤ K * W p ^ 1 := by
    obtain ⟨K, hK, hb⟩ := materialInvEll_mixedDerivative_bound hT a b
    exact ⟨K, hK, fun _ p => by simpa only [pow_one] using hb p⟩
  have hGenv : WeightedMixedJetEnvelopes W G := physicalJetEnvelopes_iff_material.mp henv
  have hLGenv : WeightedMixedJetEnvelopes W (fun i p => L p * G i p) :=
    WeightedMixedJetEnvelopes.bounded_mul hW (fun _ => hL) hG 0 hLb hGenv
  have hVenv : WeightedMixedJetEnvelopes W V :=
    WeightedMixedJetEnvelopes.add hR (fun i => hL.mul (hG i))
      (WeightedMixedJetEnvelopes.radialPartial hG hGenv) hLGenv
  have hV (i : ι) : ContDiff ℝ ∞ (V i) := (hR i).add (hL.mul (hG i))
  have hproduct := WeightedMixedJetEnvelopes.bounded_mul hW (fun _ => hA) hV 1 hAb hVenv
  apply physicalJetEnvelopes_iff_material.mpr
  apply hproduct.congr
  intro i
  exact (funext (n02n03_materialPullback_radialPartial hT (hf i))).symm

theorem PhysicalJetEnvelopes.symmetric_divergence
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {A B u : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (annularOpen D))
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (annularOpen D))
    (hAb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i p, p ∈ annularOpen D →
      ‖iteratedFDeriv ℝ n (A i) p‖ ≤ K)
    (hBb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i p, p ∈ annularOpen D →
      ‖iteratedFDeriv ℝ n (B i) p‖ ≤ K)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (annularOpen D))
    (huenv : PhysicalJetEnvelopes T γ u) :
    PhysicalJetEnvelopes T γ (fun i p =>
      ContinuousFlexibility.radialPartial (fun q => A i q * ContinuousFlexibility.angularPartial (u i) q) p +
        ContinuousFlexibility.angularPartial (fun q => A i q * ContinuousFlexibility.radialPartial (u i) q +
          B i q * ContinuousFlexibility.angularPartial (u i) q) p) := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hur (i : ι) := contDiffOn_radialPartial_of_isOpen hU (hu i)
  have hut (i : ι) := contDiffOn_angularPartial_of_isOpen hU (hu i)
  have hurEnv := PhysicalJetEnvelopes.radialPartial hT hu huenv
  have hutEnv := PhysicalJetEnvelopes.angularPartial hT hu huenv
  let F (i : ι) (p : PolarPoint) : ℝ := A i p * ContinuousFlexibility.angularPartial (u i) p
  let G (i : ι) (p : PolarPoint) : ℝ :=
    A i p * ContinuousFlexibility.radialPartial (u i) p + B i p * ContinuousFlexibility.angularPartial (u i) p
  have hF (i : ι) : ContDiffOn ℝ ∞ (F i) (annularOpen D) := (hA i).mul (hut i)
  have hG (i : ι) : ContDiffOn ℝ ∞ (G i) (annularOpen D) :=
    ((hA i).mul (hur i)).add ((hB i).mul (hut i))
  have hFenv : PhysicalJetEnvelopes T γ F :=
    PhysicalJetEnvelopes.bounded_mul hT hA hAb hut hutEnv
  have hGenv : PhysicalJetEnvelopes T γ G :=
    PhysicalJetEnvelopes.add hT (fun i => (hA i).mul (hur i))
      (fun i => (hB i).mul (hut i))
      (PhysicalJetEnvelopes.bounded_mul hT hA hAb hur hurEnv)
      (PhysicalJetEnvelopes.bounded_mul hT hB hBb hut hutEnv)
  exact PhysicalJetEnvelopes.add hT
    (fun i => contDiffOn_radialPartial_of_isOpen hU (hF i))
    (fun i => contDiffOn_angularPartial_of_isOpen hU (hG i))
    (PhysicalJetEnvelopes.radialPartial hT hF hFenv)
    (PhysicalJetEnvelopes.angularPartial hT hG hGenv)

end ContinuousFlexibility.Statements
