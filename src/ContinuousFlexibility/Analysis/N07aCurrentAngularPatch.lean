module

public import ContinuousFlexibility.Analysis.N07aCurrentComponentGluing
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalPatch

/-!
# Angular regularity after the actual moving cuts have been glued

Each negative component has one genuinely smooth field across its middle
cut. Restricting that field to its two reference halves is then legitimate.
The positive pieces are unchanged. The fixed reference angular patching
lemma applies only after these current-domain arguments are complete.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K J : CanonicalData S}
  {base loss n : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_current_physical_local_angular_regular
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcontrol : controlGeometryConditions D S C)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hinner : Icc (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    (w : ℕ → PolarPoint → ℝ)
    (hw : ∀ m, ContDiffOn ℝ ∞ (w m) (physicalPieceOpen S K z m))
    (hc : ∀ m, ContinuousOn (w m) (physicalPieceClosed S K z m))
    (hp : ∀ m p, p ∈ physicalPieceOpen S K z m → w m (p + (0, Real.pi)) = w m p)
    (hLp : ∀ m j, MemLp (mixedDerivative 0 j (w m)) 2 (n07aPhysicalMeasure S K z m))
    {η : PolarPoint → ℝ}
    (he : ∀ m, w m =ᵐ[n07aPhysicalMeasure S K z m] η)
    (hlocal : ∀ k θ, ∃ O : Set PolarPoint, IsOpen O ∧
      canonicalCutPoint S K z k θ ∈ O ∧ ∃ v : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ v O ∧
        EqOn v (w (K.cutPair k).1) (O ∩ physicalPieceOpen S K z (K.cutPair k).1) ∧
        EqOn v (w (K.cutPair k).2) (O ∩ physicalPieceOpen S K z (K.cutPair k).2)) :
    ∃ u : CanonicalL2 S J n, N07aCanonicalNormalRegular S J n u 0 ∧
      (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] η := by
  classical
  have hcomponent (k : ℕ) :=
    n07a_currentComponent_angular_field h04 hz hs w hw hc hp hLp he k (hlocal k)
  let W (k : ℕ) : PolarPoint → ℝ := (hcomponent k).choose
  have hW (k : ℕ) := (hcomponent k).choose_spec
  have hnegative (m : ℕ) (hm : K.positive m ≠ true) : K.positive m = false :=
    Bool.eq_false_iff.mpr hm
  have hpair (m : ℕ) (hm : K.positive m ≠ true) :=
    n07a_negative_referencePiece_cutPair h04 hcontrol m (hnegative m hm)
  let component (m : ℕ) (hm : K.positive m ≠ true) : ℕ := (hpair m hm).choose
  let f (m : ℕ) : PolarPoint → ℝ :=
    if hm : K.positive m = true then w m else W (component m hm)
  have hfield (m : ℕ) :
      ContDiffOn ℝ ∞ (f m) (referencePhysicalPieceOpen S K m) ∧
      (∀ p ∈ referencePhysicalPieceOpen S K m, f m (p + (0, Real.pi)) = f m p) ∧
      (∀ j, MemLp (mixedDerivative 0 j (f m)) 2
        (canonicalMeasure S (n07aPhysicalIntervalData K) m)) ∧
      f m =ᵐ[canonicalMeasure S (n07aPhysicalIntervalData K) m] η := by
    by_cases hm : K.positive m = true
    · have hdomain : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m :=
        (h04.1.domains z hz hs m).2.2.2.2.2.1 hm
      have hmeasure : n07aPhysicalMeasure S K z m =
          canonicalMeasure S (n07aPhysicalIntervalData K) m := by
        rw [n07aPhysicalMeasure, hdomain]
        simp only [referencePhysicalPieceOpen, canonicalMeasure,
          n07aPhysicalIntervalData, prod_inter_prod, inter_univ, univ_inter]
      simp only [f, dif_pos hm]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [hdomain] using hw m
      · intro p hpref
        exact hp m p (by rw [hdomain]; exact hpref)
      · intro j
        simpa only [hmeasure] using hLp m j
      · simpa only [hmeasure] using he m
    · let k := component m hm
      have hmk : m = (K.cutPair k).1 ∨ m = (K.cutPair k).2 := (hpair m hm).choose_spec
      have hsub := n07a_referenceCutPiece_subset_component h04 hmk
      have hmeasure : canonicalMeasure S (n07aPhysicalIntervalData K) m ≤
          volume.restrict (Ioo (C.left k) (C.right k) ×ˢ Ioc (0 : ℝ) Real.pi) := by
        change volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ
          Ioc (0 : ℝ) Real.pi) ≤ _
        apply Measure.restrict_mono _ le_rfl
        intro p hpm
        exact ⟨(hsub ⟨hpm.1, mem_univ _⟩).1, hpm.2⟩
      simp only [f, dif_neg hm]
      refine ⟨(hW k).1.mono hsub, ?_, ?_, ?_⟩
      · intro p hpm
        exact (hW k).2.1 p (hsub hpm)
      · intro j
        exact ((hW k).2.2.1 j).mono_measure hmeasure
      · exact ((hW k).2.2.2).filter_mono (ae_mono hmeasure)
  exact n07a_physical_local_angular_regular hD hT h04 href hinner f
    (fun m => (hfield m).1) (fun m => (hfield m).2.1)
    (fun m => (hfield m).2.2.1) (fun m => (hfield m).2.2.2)

end ContinuousFlexibility.Analysis
