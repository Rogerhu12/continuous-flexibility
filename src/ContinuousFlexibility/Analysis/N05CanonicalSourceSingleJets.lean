import ContinuousFlexibility.Analysis.N05CanonicalSourceWeakClosure
import ContinuousFlexibility.Analysis.N05CanonicalCommonCore
import ContinuousFlexibility.Analysis.N05CanonicalFiniteBlockSums
import ContinuousFlexibility.Analysis.N05CanonicalAngularSourceSingleBound

/-!
# Actual angular jets of a single canonical graph row

A finite row can be placed in a fixed stronger level by the existing
finite reweighting map. Exact cancellation of its sample weight gives
the physical weak identity for the original unweighted single source.
The derivative uses the unsigned lift, including at odd angular orders.
Only this identity uses the stronger level; no stronger-level estimate
is substituted for a same-endpoint block bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include hD hT in
/-- Every reweighted single column is exactly the original raw column,
before taking any physical representative. -/
theorem n05CanonicalJetSource_reweighted_single (s m : ℕ)
    (v : n05CanonicalClosedSubmodule S K s) (j : Fin (s + 1)) :
    n05CanonicalJetSource T S C K 1 0 s j
        (n05CanonicalFiniteReweight T S K 0 0 1 0 s {m} v).val =
      n05CanonicalAngularLift S C K (Pi.single m (v.val m j)) := by
  classical
  unfold n05CanonicalJetSource n05CanonicalAngularSource
  congr 1
  funext k
  rw [n05CanonicalAngularColumn_apply, n05CanonicalFiniteReweight_apply]
  by_cases hkm : k = m
  · subst k
    simp only [Finset.mem_singleton, eq_self_iff_true, ite_true,
      Pi.single_eq_same, smul_smul]
    rw [n05CanonicalWeightRatio_cancel hT hD.choose_spec.2.1 S K 0 0 1 0 m]
    simp only [n05CanonicalSampleWeight, neg_zero, Real.rpow_zero, one_mul, one_smul]
  · simp only [Finset.mem_singleton, hkm, ite_false, Pi.single_eq_of_ne hkm, smul_zero]

include hD hT h hcoordinates in
/-- The literal single source has all the genuine unsigned physical
angular weak derivatives encoded by its canonical graph row. -/
theorem n05CanonicalSourceLift_single_weakJet (s m : ℕ)
    (v : n05CanonicalClosedSubmodule S K s) (j : Fin (s + 1)) :
    n05_weakReferenceAngularJet D
      (n05CanonicalSourceLift S C K (Pi.single m (v.val m 0)))
      (n05CanonicalAngularLift S C K (Pi.single m (v.val m j))) j.val := by
  let w : (n05CanonicalVolumeModel T S K).level 1 0 s :=
    n05CanonicalFiniteReweight T S K 0 0 1 0 s {m} v
  have hforget : (n05CanonicalVolumeModel T S K).forget 1 0 s w =
      Pi.single m (v.val m 0) := by
    dsimp only [w]
    rw [n05CanonicalFiniteReweight_forget hT hD.choose_spec.2.1,
      n05CanonicalFiniteTruncate_forget_singleton]
    simp only [n05CanonicalSampleWeight, neg_zero, Real.rpow_zero, one_mul, one_smul]
  obtain ⟨_, _, hjets⟩ := n05CanonicalSourceLift_allAngularJets h hcoordinates hD hT
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) 0 0
    (n05CanonicalVolumeModel_actual hD hT S K)
  have hw := (hjets s w j).2.2
  rw [hforget] at hw
  change n05_weakReferenceAngularJet D _
    (n05CanonicalJetSource T S C K 1 0 s j
      (n05CanonicalFiniteReweight T S K 0 0 1 0 s {m} v).val) j.val at hw
  rw [n05CanonicalJetSource_reweighted_single hD hT s m v j] at hw
  exact hw

def n05CanonicalNormalizedSingleJetSource (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (s m : ℕ)
    (v : n05CanonicalClosedSubmodule S K s) (j : Fin (s + 1)) : PolarPoint → ℝ :=
  fun p => n05CanonicalAngularLift S C K (Pi.single m (v.val m j)) p -
    n05CanonicalAuxiliaryScalar D S C K (Pi.single m (v.val m 0)) *
      mixedDerivative 0 j.val ((S.height (3 / 4 : ℝ)).decode S.psi) p

include hD hT h hcoordinates in
/-- The correction differentiates the actual normalizer at every order.
No parity assumption is imposed on the derivative source. -/
theorem n05CanonicalNormalizedSingleJetSource_weak
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 < γ) (M : ℝ)
    (s m : ℕ) (v : n05CanonicalClosedSubmodule S K s) (j : Fin (s + 1)) :
    n05_weakReferenceAngularJet D
      (n05CanonicalNormalizedSource D S C K (Pi.single m (v.val m 0))).1
      (n05CanonicalNormalizedSingleJetSource D S C K s m v j) j.val := by
  obtain ⟨_, _, _, _, hraw⟩ :=
    n05_canonicalSourceLift_single_reference_bound hD hT h hcoordinates hγ.le M
  obtain ⟨_, _, _, _, hder⟩ :=
    n05_canonicalAngularLift_single_reference_bound hD hT h hcoordinates hγ.le M
  exact n05_normalizedSource_weak_angularJet hD.choose_spec.1.2.1.le hS
    (r11b_sourceDerivative_memLp hD hγ (hraw m (v.val m 0)).1)
    (r11b_sourceDerivative_memLp hD hγ (hder m (v.val m j)).1)
    (n05CanonicalSourceLift_single_weakJet hD hT h hcoordinates s m v j)
    (n05CanonicalAuxiliaryScalar D S C K (Pi.single m (v.val m 0)))

end ContinuousFlexibility.Statements
