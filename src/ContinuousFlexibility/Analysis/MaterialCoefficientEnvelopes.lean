import ContinuousFlexibility.Analysis.MaterialDivergenceEnvelopes

/-!
# Common source envelopes with material coefficient growth

All spatial derivatives of a coefficient may cost the same fixed power
of the material weight. The height family supplies every weighted jet,
so this growth still gives a common L² envelope for the actual fluxes
and their symmetric divergence.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem PhysicalJetEnvelopes.material_bounded_mul
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f u : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (annularOpen D)) (d : ℕ)
    (hbound : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ i p,
      |mixedDerivative a b (fun q => f i (T.radius q.1, q.2)) p| ≤
        K * T.M (T.radius p.1) ^ d)
    (henv : PhysicalJetEnvelopes T γ u) :
    PhysicalJetEnvelopes T γ (fun i p => f i p * u i p) := by
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let F (i : ι) (p : PolarPoint) : ℝ := f i (T.radius p.1, p.2)
  let G (i : ι) : PolarPoint → ℝ := materialPullback T γ (u i)
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (r : ℝ) : T.radius r ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 r).1
  have hW (p : PolarPoint) : 0 ≤ W p :=
    zero_le_one.trans (hT.2.1 _ (hinside p.1)).2.2.2
  have hF (i : ι) : ContDiff ℝ ∞ (F i) :=
    (hf i).comp_contDiff ((hr.comp contDiff_fst).prodMk contDiff_snd)
      (fun p => ⟨hinside p.1, mem_univ _⟩)
  have hG (i : ι) : ContDiff ℝ ∞ (G i) := contDiff_materialPullback hT (hu i)
  have hGenv : WeightedMixedJetEnvelopes W G := physicalJetEnvelopes_iff_material.mp henv
  have hprod := WeightedMixedJetEnvelopes.bounded_mul hW hF hG d hbound hGenv
  apply physicalJetEnvelopes_iff_material.mpr
  apply hprod.congr
  intro i
  funext p
  dsimp only [F, G, materialPullback]
  ring

theorem PhysicalJetEnvelopes.symmetric_divergence_of_material_bounds
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {A B u : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (annularOpen D))
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (annularOpen D)) (dA dB : ℕ)
    (hAb : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ i p,
      |mixedDerivative a b (fun q => A i (T.radius q.1, q.2)) p| ≤
        K * T.M (T.radius p.1) ^ dA)
    (hBb : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ i p,
      |mixedDerivative a b (fun q => B i (T.radius q.1, q.2)) p| ≤
        K * T.M (T.radius p.1) ^ dB)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (annularOpen D))
    (huenv : PhysicalJetEnvelopes T γ u) :
    PhysicalJetEnvelopes T γ (fun i p =>
      ContinuousFlexibility.Statements.radialPartial (fun q => A i q * ContinuousFlexibility.Statements.angularPartial (u i) q) p +
        ContinuousFlexibility.Statements.angularPartial (fun q => A i q * ContinuousFlexibility.Statements.radialPartial (u i) q +
          B i q * ContinuousFlexibility.Statements.angularPartial (u i) q) p) := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hur (i : ι) := contDiffOn_radialPartial_of_isOpen hU (hu i)
  have hut (i : ι) := contDiffOn_angularPartial_of_isOpen hU (hu i)
  have hurEnv := PhysicalJetEnvelopes.radialPartial hT hu huenv
  have hutEnv := PhysicalJetEnvelopes.angularPartial hT hu huenv
  let F (i : ι) (p : PolarPoint) : ℝ := A i p * ContinuousFlexibility.Statements.angularPartial (u i) p
  let G (i : ι) (p : PolarPoint) : ℝ :=
    A i p * ContinuousFlexibility.Statements.radialPartial (u i) p + B i p * ContinuousFlexibility.Statements.angularPartial (u i) p
  have hF (i : ι) : ContDiffOn ℝ ∞ (F i) (annularOpen D) := (hA i).mul (hut i)
  have hG (i : ι) : ContDiffOn ℝ ∞ (G i) (annularOpen D) :=
    ((hA i).mul (hur i)).add ((hB i).mul (hut i))
  have hFenv : PhysicalJetEnvelopes T γ F :=
    PhysicalJetEnvelopes.material_bounded_mul hT hA hut dA hAb hutEnv
  have hGenv : PhysicalJetEnvelopes T γ G :=
    PhysicalJetEnvelopes.add hT (fun i => (hA i).mul (hur i))
      (fun i => (hB i).mul (hut i))
      (PhysicalJetEnvelopes.material_bounded_mul hT hA hur dA hAb hurEnv)
      (PhysicalJetEnvelopes.material_bounded_mul hT hB hut dB hBb hutEnv)
  exact PhysicalJetEnvelopes.add hT
    (fun i => contDiffOn_radialPartial_of_isOpen hU (hF i))
    (fun i => contDiffOn_angularPartial_of_isOpen hU (hG i))
    (PhysicalJetEnvelopes.radialPartial hT hF hFenv)
    (PhysicalJetEnvelopes.angularPartial hT hG hGenv)

end ContinuousFlexibility.Statements
