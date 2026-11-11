import ContinuousFlexibility.Analysis.MaterialCoefficientMultipliers
import ContinuousFlexibility.Analysis.MaterialPartialEnergy

/-!
# Weighted material energy of a physical divergence error

An ordinary smooth coefficient with bounded jets multiplies every
weighted material energy class. Ordinary physical partial derivatives
preserve that class by the exact material identities. Consequently the
symmetric divergence error with two such coefficients has every
weighted physical jet in L². No independent formal jet is introduced.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem contDiffOn_radialPartial_of_isOpen
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (radialPartial f) U := by
  intro p hp
  exact (contDiffAt_radialPartial (hf.contDiffAt (hU.mem_nhds hp))
    (m := ∞) (by simp)).contDiffWithinAt

theorem contDiffOn_angularPartial_of_isOpen
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (angularPartial f) U := by
  intro p hp
  exact (contDiffAt_angularPartial (hf.contDiffAt (hU.mem_nhds hp))
    (m := ∞) (by simp)).contDiffWithinAt

theorem norm_iteratedFDeriv_pair_projections_le
    {U : Set PolarPoint} {A : PolarPoint → ℝ × ℝ}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (n : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q => (A q).1) p‖ ≤ ‖iteratedFDeriv ℝ n A p‖ ∧
      ‖iteratedFDeriv ℝ n (fun q => (A q).2) p‖ ≤ ‖iteratedFDeriv ℝ n A p‖ := by
  have hs : ContDiffAt ℝ ∞ A p := hA.contDiffAt (hU.mem_nhds hp)
  have heq : ‖iteratedFDeriv ℝ n A p‖ =
      max ‖iteratedFDeriv ℝ n (fun q => (A q).1) p‖
        ‖iteratedFDeriv ℝ n (fun q => (A q).2) p‖ := by
    change ‖iteratedFDeriv ℝ n (fun q => ((A q).1, (A q).2)) p‖ = _
    rw [iteratedFDeriv_prodMk hs.fst hs.snd (by simp),
      ContinuousMultilinearMap.opNorm_prod]
  rw [heq]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

theorem memLp_weightedPhysicalJet_add
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f g : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hg : ContDiffOn ℝ ∞ g (annularOpen D))
    {a b c : ℕ}
    (hfLp : MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure)
    (hgLp : MemLp (weightedPhysicalJet T γ a b c g) 2 materialCylinderMeasure) :
    MemLp (weightedPhysicalJet T γ a b c (fun p => f p + g p))
      2 materialCylinderMeasure := by
  apply (hfLp.add hgLp).ae_eq
  exact Eventually.of_forall fun p => by
    simp only [Pi.add_apply, weightedPhysicalJet_add hT hf hg]

theorem weightedPhysicalJet_eq_of_eqOn_annularOpen
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f g : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (heq : EqOn f g (annularOpen D)) (a b c : ℕ) :
    weightedPhysicalJet T γ a b c f = weightedPhysicalJet T γ a b c g := by
  have hpull : materialPullback T γ f = materialPullback T γ g := by
    funext p
    unfold materialPullback
    rw [heq ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩]
  simp only [weightedPhysicalJet, hpull]

theorem memLp_weightedPhysicalJet_symmetric_divergence
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {A B u : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hA : ContDiffOn ℝ ∞ A (annularOpen D))
    (hB : ContDiffOn ℝ ∞ B (annularOpen D))
    (hAb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n A p‖ ≤ K)
    (hBb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n B p‖ ≤ K)
    (hu : ContDiffOn ℝ ∞ u (annularOpen D))
    (huLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c u)
      2 materialCylinderMeasure) (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c
      (fun p => radialPartial (fun q => A q * angularPartial u q) p +
        angularPartial (fun q => A q * radialPartial u q + B q * angularPartial u q) p))
      2 materialCylinderMeasure := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hur := contDiffOn_radialPartial_of_isOpen hU hu
  have hut := contDiffOn_angularPartial_of_isOpen hU hu
  have hurLp := memLp_weightedPhysicalJet_radialPartial hT hu huLp
  have hutLp := memLp_weightedPhysicalJet_angularPartial hT hu huLp
  let F (p : PolarPoint) : ℝ := A p * angularPartial u p
  let G (p : PolarPoint) : ℝ := A p * radialPartial u p + B p * angularPartial u p
  have hF : ContDiffOn ℝ ∞ F (annularOpen D) := hA.mul hut
  have hG : ContDiffOn ℝ ∞ G (annularOpen D) := (hA.mul hur).add (hB.mul hut)
  have hFLp (i j k : ℕ) :
      MemLp (weightedPhysicalJet T γ i j k F) 2 materialCylinderMeasure :=
    memLp_weightedPhysicalJet_mul_of_bounded_coefficient hT hA hAb hut hutLp i j k
  have hGLp (i j k : ℕ) :
      MemLp (weightedPhysicalJet T γ i j k G) 2 materialCylinderMeasure :=
    memLp_weightedPhysicalJet_add hT (hA.mul hur) (hB.mul hut)
      (memLp_weightedPhysicalJet_mul_of_bounded_coefficient hT hA hAb hur hurLp i j k)
      (memLp_weightedPhysicalJet_mul_of_bounded_coefficient hT hB hBb hut hutLp i j k)
  exact memLp_weightedPhysicalJet_add hT
    (contDiffOn_radialPartial_of_isOpen hU hF)
    (contDiffOn_angularPartial_of_isOpen hU hG)
    (memLp_weightedPhysicalJet_radialPartial hT hF hFLp a b c)
    (memLp_weightedPhysicalJet_angularPartial hT hG hGLp a b c)

end ContinuousFlexibility.Statements
