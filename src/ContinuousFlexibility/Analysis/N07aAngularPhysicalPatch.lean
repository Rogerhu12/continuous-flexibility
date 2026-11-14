module

public import ContinuousFlexibility.Analysis.N07aAngularPieceExtension
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure
public import ContinuousFlexibility.Analysis.N07aAngularPieceCover
public import ContinuousFlexibility.Analysis.SpacesLpRestriction

/-!
# Angular patching across the fixed reference piece boundaries

The fixed reference pieces meeting a compact inner radial interval form a finite
set. Their zero-extended angular jet towers can therefore be summed in
the real cylinder L² space. A.e. uniqueness of the physical cover
identifies that sum with the original rough representative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology ENNReal BigOperators

variable {S : PhysicalSpacesData} {K J : CanonicalData S} {m n : ℕ}

theorem n07a_canonicalMeasure_le_cylinder : canonicalMeasure S J n ≤ materialCylinderMeasure := by
  rw [n07a_canonicalMeasure_eq_cylinder_restrict]
  exact Measure.restrict_le_self

def n07aCylinderRestriction (J : CanonicalData S) (n : ℕ) :
    CylinderL2 →L[ℝ] CanonicalL2 S J n :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using n07a_canonicalMeasure_le_cylinder (S := S) (J := J) (n := n))

theorem n07aCylinderRestriction_ae (u : CylinderL2) :
    (n07aCylinderRestriction J n u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

theorem n07aCylinderRestriction_pairing (u : CylinderL2) {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S J n φ) :
    (∫ p, n07aCylinderRestriction J n u p * φ p ∂canonicalMeasure S J n) =
      ∫ p, u p * φ p ∂materialCylinderMeasure := by
  calc
    _ = ∫ p, u p * φ p ∂canonicalMeasure S J n := by
      apply integral_congr_ae
      filter_upwards [n07aCylinderRestriction_ae (J := J) (n := n) u] with p hp
      rw [hp]
    _ = _ := n07a_canonicalIntegral_eq_cylinder (fun p hp => by
      rw [n07a_canonicalTest_zero_outside hφ hp, mul_zero])

theorem n07aCylinderRestriction_weak {u v : CylinderL2} {a b : ℕ}
    (h : HasWeakMixedDerivative u v a b) :
    N07aWeakCanonicalMixedDerivative S J n
      (n07aCylinderRestriction J n u) (n07aCylinderRestriction J n v) a b := by
  intro φ hφ
  rw [n07aCylinderRestriction_pairing v hφ,
    n07aCylinderRestriction_pairing u (n07a_canonicalTest_mixedDerivative hφ a b)]
  exact h φ (n07a_canonicalTest_isCylinderTest hφ)

private theorem n07a_cylinder_sum_ae (I : Finset ℕ) (u : ℕ → CylinderL2) :
    (fun p => (∑ i ∈ I, u i) p) =ᵐ[materialCylinderMeasure] fun p => ∑ i ∈ I, u i p := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 materialCylinderMeasure] with p hp
    simpa only [Pi.zero_apply] using hp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (u i) (∑ j ∈ I, u j), ih] with p hp hq
    rw [Finset.sum_insert hi, hp, Pi.add_apply, hq]

private theorem n07a_cylinder_angular_sum (I : Finset ℕ)
    {u v : ℕ → CylinderL2} (b : ℕ)
    (h : ∀ i ∈ I, HasWeakMixedDerivative (u i) (v i) 0 b) :
    HasWeakMixedDerivative (∑ i ∈ I, u i) (∑ i ∈ I, v i) 0 b := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro φ hφ
    rw [← cylinderTestPairing_apply φ hφ.memLp,
      ← cylinderTestPairing_apply (mixedDerivative 0 b φ) (hφ.mixedDerivative_memLp 0 b)]
    simp only [map_zero, mul_zero]
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact n07a_cylinderWeak_add (h i (Finset.mem_insert_self i I))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem n07a_finite_piece_angular_regular (I : Finset ℕ) (f : ℕ → PolarPoint → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (canonicalOpen S K i))
    (hp : ∀ i p, p ∈ canonicalOpen S K i → f i (p + (0, Real.pi)) = f i p)
    (hLp : ∀ i k, MemLp (mixedDerivative 0 k (f i)) 2 (canonicalMeasure S K i)) :
    ∃ u : CanonicalL2 S J n, N07aCanonicalNormalRegular S J n u 0 ∧
      (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n]
        fun p => ∑ i ∈ I, (canonicalOpen S K i).indicator (f i) p := by
  classical
  let E (k : ℕ) : CylinderL2 := ∑ i ∈ I, n07aPieceAngularJet (hLp i) k
  refine ⟨n07aCylinderRestriction J n (E 0), ?_, ?_⟩
  · intro a ha b
    have he : a = 0 := Nat.eq_zero_of_le_zero ha
    subst a
    refine ⟨n07aCylinderRestriction J n (E b), n07aCylinderRestriction_weak ?_⟩
    exact n07a_cylinder_angular_sum I b
      (fun i _ => n07aPieceAngularJet_weak (hf i) (hp i) (hLp i) b)
  · have hsum := n07a_cylinder_sum_ae I (fun i => n07aPieceAngularJet (hLp i) 0)
    have hpieces : ∀ᵐ p ∂materialCylinderMeasure, ∀ i,
        n07aPieceAngularJet (hLp i) 0 p = (canonicalOpen S K i).indicator (f i) p := by
      apply ae_all_iff.mpr
      intro i
      have h := n07aPieceAngularJet_ae (hLp i) 0
      simp only [spaces_mixedDerivative_zero] at h
      exact h
    have hsum' := hsum.filter_mono (ae_mono
      (n07a_canonicalMeasure_le_cylinder (S := S) (J := J) (n := n)))
    have hpieces' := hpieces.filter_mono (ae_mono
      (n07a_canonicalMeasure_le_cylinder (S := S) (J := J) (n := n)))
    filter_upwards [n07aCylinderRestriction_ae (J := J) (n := n) (E 0), hsum', hpieces']
      with p hp hq hr
    exact hp.trans (hq.trans (Finset.sum_congr rfl (fun i _ => hr i)))

variable {D : ReferenceData} {T : MaterialData} {C : NonlinearGeometryData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

private theorem n07a_physical_finite_cover_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hinner : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    (I : Finset ℕ)
    (hI : ∀ i, (Ioo (J.left n) (J.right n) ∩
      Ioo (K.physicalLeft i) (K.physicalRight i)).Nonempty → i ∈ I) :
    ∀ᵐ p ∂canonicalMeasure S J n, ∃ i ∈ I, p ∈ referencePhysicalPieceOpen S K i := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
  have hEr : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ E := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hE
  have hEr' := hEr.filter_mono (ae_mono (Measure.restrict_le_self
    (μ := (volume : Measure ℝ)) (s := Ioo (J.left n) (J.right n))))
  have hEp : ∀ᵐ p ∂canonicalMeasure S J n, p.1 ∉ E := by
    rw [n07aCanonicalMeasure_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hEr'
  filter_upwards [hEp, n07a_canonicalOpen_ae (S := S) (K := J) (m := n)] with p hp hpJ
  obtain ⟨i, hi, _⟩ := hcover p.1 ⟨hinner hpJ.1, hp⟩
  exact ⟨i, hI i ⟨p.1, hpJ.1, hi⟩, hi, mem_univ _⟩

/-- Locally finite fixed reference strips give all angular weak jets on
every strict inner interval. A moving current cut requires its separate
transmission proof before this rectangular patching lemma applies. -/
theorem n07a_physical_local_angular_regular
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hinner : Icc (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    (f : ℕ → PolarPoint → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (referencePhysicalPieceOpen S K i))
    (hp : ∀ i p, p ∈ referencePhysicalPieceOpen S K i → f i (p + (0, Real.pi)) = f i p)
    (hLp : ∀ i k, MemLp (mixedDerivative 0 k (f i)) 2
      (canonicalMeasure S (n07aPhysicalIntervalData K) i))
    {η : PolarPoint → ℝ}
    (he : ∀ i, f i =ᵐ[canonicalMeasure S (n07aPhysicalIntervalData K) i] η) :
    ∃ u : CanonicalL2 S J n, N07aCanonicalNormalRegular S J n u 0 ∧
      (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] η := by
  classical
  let M := {i : ℕ | (Icc (J.left n) (J.right n) ∩
    Ioo (K.physicalLeft i) (K.physicalRight i)).Nonempty}
  have hM : M.Finite := n07a_physicalPieces_finite_inter_compact hD hT h04 href isCompact_Icc hinner
  let I := hM.toFinset
  have hI (i : ℕ) (hi : (Ioo (J.left n) (J.right n) ∩
      Ioo (K.physicalLeft i) (K.physicalRight i)).Nonempty) : i ∈ I := by
    apply hM.mem_toFinset.mpr
    obtain ⟨r, hr, hri⟩ := hi
    exact ⟨r, Ioo_subset_Icc_self hr, hri⟩
  obtain ⟨u, hu, hue⟩ := n07a_finite_piece_angular_regular
    (K := n07aPhysicalIntervalData K) (J := J) (n := n)
    I f hf hp hLp
  refine ⟨u, hu, hue.trans ?_⟩
  have hcells : ∀ᵐ p ∂materialCylinderMeasure, ∀ i,
      p ∈ referencePhysicalPieceOpen S K i → f i p = η p :=
    ae_all_iff.mpr (fun i => n07aCanonical_ae_imp (he i))
  have hc := hcells.filter_mono (ae_mono
    (n07a_canonicalMeasure_le_cylinder (S := S) (J := J) (n := n)))
  have hcover := n07a_physical_finite_cover_ae h04
    (Ioo_subset_Icc_self.trans hinner) I hI
  have hdis := n07a_physicalPieces_pairwise_disjoint h04
  filter_upwards [hc, hcover] with p hpe hpc
  obtain ⟨i, hi, hpi⟩ := hpc
  calc
    (∑ j ∈ I, (canonicalOpen S (n07aPhysicalIntervalData K) j).indicator (f j) p) =
        (canonicalOpen S (n07aPhysicalIntervalData K) i).indicator (f i) p := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hpj : p ∉ canonicalOpen S (n07aPhysicalIntervalData K) j := by
          intro hpj
          exact Set.disjoint_left.mp (hdis hji) hpj.1 hpi.1
        exact indicator_of_notMem hpj _
      · exact fun hni => (hni hi).elim
    _ = f i p := indicator_of_mem hpi _
    _ = η p := hpe i hpi

end ContinuousFlexibility.Analysis
