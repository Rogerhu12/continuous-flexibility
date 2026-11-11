import ContinuousFlexibility.Analysis.ReturnCorrectionSourceJets
import ContinuousFlexibility.Analysis.ReturnDivergenceMembership
import ContinuousFlexibility.Analysis.MaterialCoefficientEnvelopes
import ContinuousFlexibility.Analysis.MaterialAffineEnvelopes

/-!
# Genuine second-variation energy envelopes for the source

A compact scalar segment supplies one common material bound for each
coefficient jet. The height along that segment is affine. The exact
finite fiber expansion therefore gives one weighted L² envelope for
every second parameter variation in the original source decoder.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

theorem PhysicalJetEnvelopes.finset_sum
    {ι κ : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hT : IsMaterialData D T) (I : Finset κ) (f : κ → ι → PolarPoint → ℝ)
    (hf : ∀ j ∈ I, ∀ i, ContDiffOn ℝ ∞ (f j i) (annularOpen D))
    (henv : ∀ j ∈ I, PhysicalJetEnvelopes T γ (f j)) :
    PhysicalJetEnvelopes T γ (fun i p => ∑ j ∈ I, f j i p) := by
  classical
  revert hf henv
  induction I using Finset.induction_on with
  | empty =>
      intro hf henv
      simp only [Finset.sum_empty]
      apply physicalJetEnvelopes_const
      intro a b c
      have heq : weightedPhysicalJet T γ a b c (0 : PolarPoint → ℝ) = 0 :=
        (annularWeightedJetLinear hT γ a b c).map_zero
      change MemLp (weightedPhysicalJet T γ a b c (0 : PolarPoint → ℝ))
        2 materialCylinderMeasure
      rw [heq]
      exact memLp_zero
  | @insert j I hj ih =>
      intro hf henv
      have hsum := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
        (fun k hk => henv k (Finset.mem_insert_of_mem hk))
      have hadd := PhysicalJetEnvelopes.add hT (hf j (Finset.mem_insert_self j I))
        (fun i => contDiffOn_finset_sum_fields I (fun k => f k i)
          (fun k hk => hf k (Finset.mem_insert_of_mem hk) i))
        (henv j (Finset.mem_insert_self j I)) hsum
      apply hadd.congr_on_annularOpen hT
      intro i p hp
      simp only [Finset.sum_insert hj]

theorem symmetricDivergenceBilinear_envelopes
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ι → annularSmoothCoefficientSpace D) (η : ι → HeightPair S) (d : ℕ)
    (hbound : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ i p,
      |mixedDerivative a b (fun q => ((A i).val (T.radius q.1, q.2)).1) p| ≤
        K * T.M (T.radius p.1) ^ d ∧
      |mixedDerivative a b (fun q => ((A i).val (T.radius q.1, q.2)).2) p| ≤
        K * T.M (T.radius p.1) ^ d)
    (hη : PhysicalJetEnvelopes T (3 / 4 : ℝ)
      (fun i => (S.height (3 / 4 : ℝ)).decode (η i).1)) :
    PhysicalJetEnvelopes T (3 / 4 : ℝ)
      (fun i => symmetricDivergenceBilinear hS hT (A i) (η i)) := by
  have hfirst (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ i p,
      |mixedDerivative a b (fun q => ((A i).val (T.radius q.1, q.2)).1) p| ≤
        K * T.M (T.radius p.1) ^ d :=
    ⟨(hbound a b).choose, (hbound a b).choose_spec.1,
      fun i p => ((hbound a b).choose_spec.2 i p).1⟩
  have hsecond (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ i p,
      |mixedDerivative a b (fun q => ((A i).val (T.radius q.1, q.2)).2) p| ≤
        K * T.M (T.radius p.1) ^ d :=
    ⟨(hbound a b).choose, (hbound a b).choose_spec.1,
      fun i p => ((hbound a b).choose_spec.2 i p).2⟩
  have hd := PhysicalJetEnvelopes.symmetric_divergence_of_material_bounds hT
    (fun i => (A i).property.fst) (fun i => (A i).property.snd) d d hfirst hsecond
    (fun i => ((hS.1 (3 / 4 : ℝ)).2.2.2.1 (η i).1).1) hη
  apply hd.congr_on_annularOpen hT
  intro i p hp
  rw [symmetricDivergenceBilinear_apply, if_pos hp]

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {U : Set E}

/-- Each coefficient order has a neighborhood along the fixed line.
The neighborhood is uniform over the finitely many directions used at
that order; its material growth exponent may depend on the directions. -/
def MaterialCoefficientJetLineBounds
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)) : Prop :=
  ∀ n (x : E), x ∈ U → ∀ w : E,
    ∃ δ : ℝ, 0 < δ ∧ (∀ t : ℝ, |t| < δ → x + t • w ∈ U) ∧
      ∀ v : Fin n → E, ∃ d : ℕ, ∀ a b, ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ, |t| < δ → ∀ p,
          |mixedDerivative a b
            (fun q => ((A n (x + t • w) v).val (T.radius q.1, q.2)).1) p| ≤
              K * T.M (T.radius p.1) ^ d ∧
          |mixedDerivative a b
            (fun q => ((A n (x + t • w) v).val (T.radius q.1, q.2)).2) p| ≤
              K * T.M (T.radius p.1) ^ d

theorem symmetricSourceScalarJets_secondEnvelopes
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (hline : MaterialCoefficientJetLineBounds (T := T) (U := U) A) :
    SourceJetSecondEnvelopes (T := T) (U := U ×ˢ (univ : Set (HeightPair S)))
      (symmetricSourceScalarJets hS hT A) := by
  classical
  intro n z hz v w
  obtain ⟨δ₁, hδ₁, hmem₁, hb₁⟩ := hline (n + 2) z.1 hz.1 w.1
  obtain ⟨δ₂, hδ₂, _, hb₂⟩ := hline (n + 1) z.1 hz.1 w.1
  let δ : ℝ := min δ₁ (min δ₂ 1)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ zero_lt_one)
  have ht₁ {t : ℝ} (ht : |t| < δ) : |t| < δ₁ := ht.trans_le (min_le_left _ _)
  have ht₂ {t : ℝ} (ht : |t| < δ) : |t| < δ₂ :=
    ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htone {t : ℝ} (ht : |t| < δ) : |t| ≤ 1 :=
    ht.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let I := {t : ℝ // |t| < δ}
  let vs : Fin (n + 2) → E × HeightPair S := Fin.cons w (Fin.cons w v)
  let x (t : I) : E := z.1 + t.val • w.1
  let η (t : I) : HeightPair S := z.2 + t.val • w.2
  have hη : PhysicalJetEnvelopes T (3 / 4 : ℝ)
      (fun t : I => (S.height (3 / 4 : ℝ)).decode (η t).1) :=
    physicalJetEnvelopes_decode_affine_family (hS.1 (3 / 4 : ℝ)) hT
      z.2.1 w.2.1 (fun t : I => t.val) zero_le_one (fun t => htone t.property)
  obtain ⟨d, hd⟩ := hb₁ (fun i => (vs i).1)
  have hmain : PhysicalJetEnvelopes T (3 / 4 : ℝ)
      (fun t : I => symmetricDivergenceBilinear hS hT
        (A (n + 2) (x t) (fun i => (vs i).1)) (η t)) := by
    apply symmetricDivergenceBilinear_envelopes hS hT _ η d _ hη
    intro a b
    obtain ⟨K, hK, hb⟩ := hd a b
    exact ⟨K, hK, fun t p => hb t.val (ht₁ t.property) p⟩
  let R (i : Fin (n + 2)) (t : I) := symmetricDivergenceBilinear hS hT
    (A (n + 1) (x t) (fun j => (vs (i.succAbove j)).1)) (vs i).2
  have hR (i : Fin (n + 2)) : PhysicalJetEnvelopes T (3 / 4 : ℝ) (R i) := by
    obtain ⟨di, hdi⟩ := hb₂ (fun j => (vs (i.succAbove j)).1)
    apply symmetricDivergenceBilinear_envelopes hS hT _ (fun _ : I => (vs i).2) di
    · intro a b
      obtain ⟨K, hK, hb⟩ := hdi a b
      exact ⟨K, hK, fun t p => hb t.val (ht₂ t.property) p⟩
    · exact physicalJetEnvelopes_const ((hS.1 _).2.2.2.1 (vs i).2.1).2.2.2.2
  have hsum := PhysicalJetEnvelopes.finset_sum hT Finset.univ R
    (fun i _ t => symmetricDivergenceBilinear_contDiffOn hS hT _ _) (fun i _ => hR i)
  have hall := PhysicalJetEnvelopes.add hT
    (fun t => symmetricDivergenceBilinear_contDiffOn hS hT _ _)
    (fun t => contDiffOn_finset_sum_fields Finset.univ (fun i => R i t)
      (fun i _ => symmetricDivergenceBilinear_contDiffOn hS hT _ _)) hmain hsum
  have hjet : PhysicalJetEnvelopes T (3 / 4 : ℝ)
      (fun t : I => symmetricSourceScalarJets hS hT A (n + 2) (z + t.val • w) vs) := by
    apply hall.congr_on_annularOpen hT
    intro t p hp
    simpa only [Pi.add_apply, Finset.sum_apply] using
      (congrFun (symmetricSourceScalarJets_eq_sum hS hT A (n + 1)
        (z + t.val • w) vs) p).symm
  refine ⟨δ, hδ, fun t ht => ⟨hmem₁ t (ht₁ ht), mem_univ _⟩, ?_⟩
  intro a b c
  obtain ⟨G, hG, hGpos, hb⟩ := hjet a b c
  exact ⟨G, hG, hGpos, fun t ht p => hb ⟨t, ht⟩ p⟩

end ContinuousFlexibility.Statements
