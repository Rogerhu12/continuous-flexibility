import ContinuousFlexibility.Analysis.N07aCurrentCutMeasure
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Gluing the two moving halves of a negative component

Local smooth fields at the cut determine one smooth field on the whole
component. Its angular derivatives remain in L² because the cut is null
and the two actual open halves partition its complement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem n07a_twoPiece_subset_closure
    {A B N Z : Set PolarPoint} (hcover : A ∪ B = N \ Z)
    (hclosed : Z ⊆ closure A) : N ⊆ closure (A ∪ B) := by
  intro p hp
  by_cases hpZ : p ∈ Z
  · exact closure_mono subset_union_left (hclosed hpZ)
  · apply subset_closure
    rw [hcover]
    exact ⟨hp, hpZ⟩

/-- This gluing uses only the actual closed trace of the left field and
the local smooth field supplied at each point of the middle cut. -/
theorem n07a_twoOpenPieces_smooth_gluing
    {A B N Z : Set PolarPoint} (hA : IsOpen A) (hB : IsOpen B) (hN : IsOpen N)
    (hdis : Disjoint A B) (hcover : A ∪ B = N \ Z)
    (hclosed : Z ⊆ closure A)
    {f g : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f A) (hg : ContDiffOn ℝ ∞ g B)
    (hc : ContinuousOn f (closure A))
    (hlocal : ∀ p ∈ Z, ∃ O : Set PolarPoint, IsOpen O ∧ p ∈ O ∧
      ∃ v : PolarPoint → ℝ, ContDiffOn ℝ ∞ v O ∧
        EqOn v f (O ∩ A) ∧ EqOn v g (O ∩ B)) :
    ∃ W : PolarPoint → ℝ, ContDiffOn ℝ ∞ W N ∧ EqOn W f A ∧ EqOn W g B := by
  classical
  let W : PolarPoint → ℝ := fun p => if p ∈ B then g p else f p
  have hWA : EqOn W f A := by
    intro p hp
    exact if_neg (fun hpB => Set.disjoint_left.mp hdis hp hpB)
  have hWB : EqOn W g B := fun p hp => if_pos hp
  refine ⟨W, ?_, hWA, hWB⟩
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  by_cases hpA : p ∈ A
  · exact (hf.contDiffAt (hA.mem_nhds hpA)).congr_of_eventuallyEq
      (hWA.eventuallyEq_of_mem (hA.mem_nhds hpA))
  by_cases hpB : p ∈ B
  · exact (hg.contDiffAt (hB.mem_nhds hpB)).congr_of_eventuallyEq
      (hWB.eventuallyEq_of_mem (hB.mem_nhds hpB))
  have hpZ : p ∈ Z := by
    by_contra hpZ
    have hpU : p ∈ A ∪ B := by rw [hcover]; exact ⟨hp, hpZ⟩
    exact hpU.elim hpA hpB
  obtain ⟨O, hO, hpO, v, hv, hvA, hvB⟩ := hlocal p hpZ
  have hvcl : EqOn v f (O ∩ closure A) :=
    hvA.of_subset_closure (hv.continuousOn.mono inter_subset_left)
      (hc.mono inter_subset_right)
      (fun q hq => ⟨hq.1, subset_closure hq.2⟩) hO.inter_closure
  have he : EqOn W v (O ∩ N) := by
    intro q hq
    by_cases hqB : q ∈ B
    · exact (hWB hqB).trans (hvB ⟨hq.1, hqB⟩).symm
    by_cases hqA : q ∈ A
    · exact (hWA hqA).trans (hvA ⟨hq.1, hqA⟩).symm
    have hqZ : q ∈ Z := by
      by_contra hqZ
      have hqU : q ∈ A ∪ B := by rw [hcover]; exact ⟨hq.2, hqZ⟩
      exact hqU.elim hqA hqB
    exact (show W q = f q from if_neg hqB).trans
      (hvcl ⟨hq.1, hclosed hqZ⟩).symm
  exact (hv.contDiffAt (hO.mem_nhds hpO)).congr_of_eventuallyEq
    (he.eventuallyEq_of_mem ((hO.inter hN).mem_nhds ⟨hpO, hp⟩))

private theorem n07a_memLp_twoPieces
    {A B N Z P : Set PolarPoint}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hN : MeasurableSet N) (hP : MeasurableSet P)
    (hdis : Disjoint A B) (hcover : A ∪ B = N \ Z) (hZ : volume Z = 0)
    {f : PolarPoint → ℝ}
    (hfA : MemLp f 2 (volume.restrict (A ∩ P)))
    (hfB : MemLp f 2 (volume.restrict (B ∩ P))) :
    MemLp f 2 (volume.restrict (N ∩ P)) := by
  classical
  let μ : Measure PolarPoint := volume.restrict P
  have hAi : MemLp (A.indicator f) 2 μ := by
    apply (memLp_indicator_iff_restrict hA).mpr
    simpa only [μ, Measure.restrict_restrict hA] using hfA
  have hBi : MemLp (B.indicator f) 2 μ := by
    apply (memLp_indicator_iff_restrict hB).mpr
    simpa only [μ, Measure.restrict_restrict hB] using hfB
  have hsum := (hAi.add hBi).restrict N
  rw [show μ.restrict N = volume.restrict (N ∩ P) from Measure.restrict_restrict hN]
    at hsum
  have hZae : ∀ᵐ p ∂volume, p ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hZ
  apply (memLp_congr_ae (show (A.indicator f + B.indicator f) =ᵐ[
      volume.restrict (N ∩ P)] f from ?_)).mp hsum
  filter_upwards [ae_restrict_mem (hN.inter hP), ae_restrict_of_ae hZae] with p hp hpZ
  have hpU : p ∈ A ∪ B := by rw [hcover]; exact ⟨hp.1, hpZ⟩
  rcases hpU with hpA | hpB
  · have hnB : p ∉ B := fun hpB => Set.disjoint_left.mp hdis hpA hpB
    simp only [Pi.add_apply, indicator_of_mem hpA, indicator_of_notMem hnB, add_zero]
  · have hnA : p ∉ A := fun hpA => Set.disjoint_left.mp hdis hpA hpB
    simp only [Pi.add_apply, indicator_of_notMem hnA, indicator_of_mem hpB, zero_add]

private theorem n07a_ae_twoPieces
    {A B N Z P : Set PolarPoint}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hN : MeasurableSet N) (hP : MeasurableSet P)
    (hcover : A ∪ B = N \ Z) (hZ : volume Z = 0)
    {f g : PolarPoint → ℝ}
    (hfgA : f =ᵐ[volume.restrict (A ∩ P)] g)
    (hfgB : f =ᵐ[volume.restrict (B ∩ P)] g) :
    f =ᵐ[volume.restrict (N ∩ P)] g := by
  have hA' := (ae_restrict_iff' (hA.inter hP)).mp hfgA
  have hB' := (ae_restrict_iff' (hB.inter hP)).mp hfgB
  have hZae : ∀ᵐ p ∂volume, p ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hZ
  filter_upwards [ae_restrict_mem (hN.inter hP), ae_restrict_of_ae hZae,
    ae_restrict_of_ae hA', ae_restrict_of_ae hB'] with p hp hpZ hpA hpB
  have hpU : p ∈ A ∪ B := by rw [hcover]; exact ⟨hp.1, hpZ⟩
  exact hpU.elim (fun h => hpA ⟨h, hp.2⟩) (fun h => hpB ⟨h, hp.2⟩)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Local moving-cut gluing retains the same physical a.e. class and all
angular L² derivatives on the entire negative component. -/
theorem n07a_currentComponent_angular_field
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (w : ℕ → PolarPoint → ℝ)
    (hw : ∀ m, ContDiffOn ℝ ∞ (w m) (physicalPieceOpen S K z m))
    (hc : ∀ m, ContinuousOn (w m) (physicalPieceClosed S K z m))
    (hp : ∀ m p, p ∈ physicalPieceOpen S K z m → w m (p + (0, Real.pi)) = w m p)
    (hLp : ∀ m j, MemLp (mixedDerivative 0 j (w m)) 2 (n07aPhysicalMeasure S K z m))
    {η : PolarPoint → ℝ}
    (he : ∀ m, w m =ᵐ[n07aPhysicalMeasure S K z m] η)
    (k : ℕ)
    (hlocal : ∀ θ : ℝ, ∃ O : Set PolarPoint, IsOpen O ∧
      canonicalCutPoint S K z k θ ∈ O ∧ ∃ v : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ v O ∧
        EqOn v (w (K.cutPair k).1) (O ∩ physicalPieceOpen S K z (K.cutPair k).1) ∧
        EqOn v (w (K.cutPair k).2) (O ∩ physicalPieceOpen S K z (K.cutPair k).2)) :
    ∃ W : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ W (Ioo (C.left k) (C.right k) ×ˢ (univ : Set ℝ)) ∧
      (∀ p ∈ Ioo (C.left k) (C.right k) ×ˢ (univ : Set ℝ),
        W (p + (0, Real.pi)) = W p) ∧
      (∀ j, MemLp (mixedDerivative 0 j W) 2
        (volume.restrict (Ioo (C.left k) (C.right k) ×ˢ Ioc (0 : ℝ) Real.pi))) ∧
      W =ᵐ[volume.restrict (Ioo (C.left k) (C.right k) ×ˢ Ioc (0 : ℝ) Real.pi)] η := by
  let A := physicalPieceOpen S K z (K.cutPair k).1
  let B := physicalPieceOpen S K z (K.cutPair k).2
  let N : Set PolarPoint := Ioo (C.left k) (C.right k) ×ˢ (univ : Set ℝ)
  let Z := Set.range (canonicalCutPoint S K z k)
  let P : Set PolarPoint := (univ : Set ℝ) ×ˢ Ioc (0 : ℝ) Real.pi
  have hA : IsOpen A := (h04.1.domains z hz hs (K.cutPair k).1).1
  have hB : IsOpen B := (h04.1.domains z hz hs (K.cutPair k).2).1
  have hN : IsOpen N := isOpen_Ioo.prod isOpen_univ
  have hP : MeasurableSet P := MeasurableSet.univ.prod measurableSet_Ioc
  have hcut := h04.2.1.1.2 z hz hs k
  have hdis : Disjoint A B := hcut.2.2.1
  have hcover : A ∪ B = N \ Z := hcut.2.2.2.1
  have hclosed : Z ⊆ closure A := by
    rintro p ⟨θ, rfl⟩
    exact (n07a_currentCutPoint_mem_closed h04 hz hs k θ).1
  obtain ⟨W, hW, hWA, hWB⟩ := n07a_twoOpenPieces_smooth_gluing hA hB hN hdis hcover
    hclosed (hw (K.cutPair k).1) (hw (K.cutPair k).2) (hc (K.cutPair k).1)
    (fun p hp => by obtain ⟨θ, rfl⟩ := hp; exact hlocal θ)
  have hperiod : ∀ p ∈ N, W (p + (0, Real.pi)) = W p := by
    have hmap : MapsTo (fun p : PolarPoint => p + (0, Real.pi)) N N := by
      intro p hpN
      exact ⟨by simpa only [Prod.fst_add, add_zero] using hpN.1, mem_univ _⟩
    have heq : EqOn (fun p => W (p + (0, Real.pi))) W (A ∪ B) := by
      intro p hpAB
      rcases hpAB with hpA | hpB
      · have hshift : p + (0, Real.pi) ∈ A :=
          ((h04.1.domains z hz hs (K.cutPair k).1).2.2.2.1 p).mpr hpA
        exact (hWA hshift).trans ((hp (K.cutPair k).1 p hpA).trans (hWA hpA).symm)
      · have hshift : p + (0, Real.pi) ∈ B :=
          ((h04.1.domains z hz hs (K.cutPair k).2).2.2.2.1 p).mpr hpB
        exact (hWB hshift).trans ((hp (K.cutPair k).2 p hpB).trans (hWB hpB).symm)
    exact heq.of_subset_closure
      (hW.continuousOn.comp (continuous_id.add continuous_const).continuousOn hmap)
      hW.continuousOn
      (by intro p hpAB; rw [hcover] at hpAB; exact hpAB.1)
      (n07a_twoPiece_subset_closure hcover hclosed)
  have hNP : N ∩ P = Ioo (C.left k) (C.right k) ×ˢ Ioc (0 : ℝ) Real.pi := by
    simp only [N, P, prod_inter_prod, inter_univ, univ_inter]
  have hZ := n07a_currentCut_volume_zero h04 hz hs k
  refine ⟨W, hW, hperiod, ?_, ?_⟩
  · intro j
    have hja := n07a_mixedDerivative_eqOn hA hWA 0 j
    have hjb := n07a_mixedDerivative_eqOn hB hWB 0 j
    have hLa : MemLp (mixedDerivative 0 j W) 2 (volume.restrict (A ∩ P)) := by
      apply (memLp_congr_ae (show mixedDerivative 0 j W =ᵐ[n07aPhysicalMeasure S K z
          (K.cutPair k).1] mixedDerivative 0 j (w (K.cutPair k).1) from ?_)).mpr
        (hLp (K.cutPair k).1 j)
      exact (n07aPhysicalMeasure_ae h04 hz hs (K.cutPair k).1).mono fun p hpA => hja hpA
    have hLb : MemLp (mixedDerivative 0 j W) 2 (volume.restrict (B ∩ P)) := by
      apply (memLp_congr_ae (show mixedDerivative 0 j W =ᵐ[n07aPhysicalMeasure S K z
          (K.cutPair k).2] mixedDerivative 0 j (w (K.cutPair k).2) from ?_)).mpr
        (hLp (K.cutPair k).2 j)
      exact (n07aPhysicalMeasure_ae h04 hz hs (K.cutPair k).2).mono fun p hpB => hjb hpB
    simpa only [hNP] using
      n07a_memLp_twoPieces hA.measurableSet hB.measurableSet hN.measurableSet hP
        hdis hcover hZ hLa hLb
  · have hWae (m : ℕ) (hWm : EqOn W (w m) (physicalPieceOpen S K z m)) :
        W =ᵐ[n07aPhysicalMeasure S K z m] η := by
      filter_upwards [n07aPhysicalMeasure_ae h04 hz hs m, he m] with p hpm hη
      exact (hWm hpm).trans hη
    have hea : W =ᵐ[volume.restrict (A ∩ P)] η := hWae (K.cutPair k).1 hWA
    have heb : W =ᵐ[volume.restrict (B ∩ P)] η := hWae (K.cutPair k).2 hWB
    simpa only [hNP] using
      n07a_ae_twoPieces hA.measurableSet hB.measurableSet hN.measurableSet hP
        hcover hZ hea heb

end ContinuousFlexibility.Analysis
