import ContinuousFlexibility.Analysis.N07aAngularBoundaryFirstJet
import ContinuousFlexibility.Analysis.N07aAngularClosedPieceGluing
import ContinuousFlexibility.Analysis.N07aAngularReferenceSymmetry

/-!
# An arbitrary current smooth field has a genuine C¹ reference realization

The constructed field represents exactly the same canonical height after
subtracting the same left scalar. It uses the actual current/reference
charts and height factors on every open piece. Its global first derivative
is continuous across the roots and the designated middle cuts.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff NNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_exists_referenceTransport_C1
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hrad : ReferenceRadial S C K) (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (htrans : TransmissionGeometry D S C K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (aL : ℝ) {η : PolarPoint → ℝ} (hη : ContDiffOn ℝ ∞ η (annularOpen D))
    (hηπ : Function.Periodic η (0, Real.pi)) (hηe : ∀ r θ, η (r, -θ) = η (r, θ)) :
    ∃ v : PolarPoint → ℝ,
      ContDiffOn ℝ 1 v (annularOpen D) ∧ Function.Periodic v (0, Real.pi) ∧
      (∀ r θ, v (r, -θ) = v (r, θ)) ∧
      (∀ m, EqOn v
        (n07aReferencePieceHeight C K (liftSectorParameter S C z)
          (K.inverseChart (liftSectorParameter S C z)) aL η m) (physicalPieceOpen S K m)) ∧
      (∀ m, EqOn
        (canonicalHeight S K (C.referenceState, 0) m (fun p => v p - aL * S.chiLeft p.1))
        (canonicalHeight S K (liftSectorParameter S C z) m (fun p => η p - aL * S.chiLeft p.1))
        (canonicalOpen S K m)) ∧
      (∀ p, p ∉ annularOpen D → v p = 0) ∧
      ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
        ContDiffAt ℝ ∞ u p ∧
        ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := h01.2.2.1.liftSectorParameter_sector z
  let z' := liftSectorParameter S C z
  have hLip (m : ℕ) : ∃ M : ℝ≥0,
      LipschitzOnWith M (K.inverseChart z' m) (canonicalOpen S K m) :=
    n07a_current_inverseChart_lipschitz href hcur z hz m
      (h04.2.2.2.1 m).2.1 (h04.2.2.2.1 m).1
  have hex (m : ℕ) : ∃ g₀ : PolarPoint → PolarPoint,
      Continuous g₀ ∧ EqOn (K.inverseChart z' m) g₀ (canonicalOpen S K m) := by
    obtain ⟨g₀, hgc, hge, _⟩ := n07a_exists_actual_inverseExtension h04 hz' hs m (hLip m)
    exact ⟨g₀, hgc, hge⟩
  choose g hg using hex
  let W := n07aReferencePieceHeight C K z' g aL η
  have hgEq (m : ℕ) : EqOn (K.inverseChart z' m) (g m) (canonicalOpen S K m) := (hg m).2
  obtain ⟨v, hv, heq, hzero, hright⟩ := n07a_glue_closed_physical_pieces hD hT h04 href W
    (n07aReferencePieceHeight_contDiffOn hS h01 h04 hz' hs hgEq aL hη)
    (fun i j hij hb hc θ => by
      obtain ⟨d⟩ := n07a_interfaceJetData_exists htrans hij hb
      exact n07a_actual_referenceHeight_interface hS h01 h04 hrad hz' hs hb hc d hg hLip aL hη θ)
  have hclosedOpen (m : ℕ) : EqOn v (W m) (physicalPieceOpen S K m) := by
    intro p hp
    exact heq m p ⟨(h04.2.2.2.1 m).2.2 hp.1, mem_univ _⟩ (Ioo_subset_Icc_self hp.1)
  have hopen (m : ℕ) : EqOn v
      (n07aReferencePieceHeight C K z' (K.inverseChart z') aL η m) (physicalPieceOpen S K m) :=
    (hclosedOpen m).trans (n07aReferencePieceHeight_eq_actual h01 h04 hgEq aL η m)
  have hperiod : Function.Periodic v (0, Real.pi) := by
    apply n07a_physical_periodic_of_piecewise h04 hv.continuousOn hzero
    intro m p hp
    have hpπ : p + (0, Real.pi) ∈ physicalPieceOpen S K m :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    rw [hopen m hpπ, hopen m hp]
    exact n07aReferencePieceHeight_periodic_on h01 h04 hz' hs
      (fun _ _ _ => rfl) aL hηπ m p hp
  have heven : ∀ r θ, v (r, -θ) = v (r, θ) := by
    apply n07a_physical_even_of_piecewise h04 hv.continuousOn hzero
    intro m p hp
    rw [hopen m (show (p.1, -p.2) ∈ physicalPieceOpen S K m from ⟨hp.1, mem_univ _⟩),
      hopen m hp]
    exact n07aReferencePieceHeight_even_on h01 h04 hz' hs aL hηe m p hp
  refine ⟨v, hv, hperiod, heven, hopen, ?_, hzero, hright⟩
  intro m
  exact n07aReferencePieceHeight_canonical h01 h04 hgEq aL η m (hclosedOpen m)

end ContinuousFlexibility.Analysis
