import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly
import ContinuousFlexibility.Analysis.ActualWholeReferenceNonAuxiliaryJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAuxiliaryPackage

/-!
# The reference obligation

The non-auxiliary producer selects the literal degree-three reference family
once, with its principal certificate. For each positive transport family that
is the identity at the reference state and each smaller neighborhood carrying
the geometry, the buffered auxiliary package chooses one auxiliary column on
that neighborhood. The original typed atlas is kept: the package accepts an
arbitrary supplied atlas, and Through03 is restricted only for the package.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
  ContinuousFlexibility.Blueprint
open CanonicalGeometry
open scoped ContDiff

/-- The principal clause survives the material enlargement. -/
theorem referencePrincipal_enlargedMaterialData {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    (hpos : ∀ m, 0 < T.E0 (T.sample (K.cell m)))
    (h : ReferencePrincipal T S C K) :
    ReferencePrincipal (enlargedMaterialData T) S C K := by
  refine ⟨h.1, ?_⟩
  obtain ⟨B, hB, hlower⟩ := h.2
  refine ⟨B, hB, fun m hm p hp => le_trans ?_ (hlower m hm p hp)⟩
  have hd : 0 ≤ (p.1 - K.left m) * (K.right m - p.1) := by
    have hp' := hp
    simp only [canonicalOpen, mem_prod, mem_Ioo] at hp'
    exact mul_nonneg (sub_nonneg.mpr hp'.1.1.le) (sub_nonneg.mpr hp'.1.2.le)
  refine mul_le_mul_of_nonneg_right ?_ hd
  have hE := hpos m
  have hle : T.E0 (T.sample (K.cell m)) ≤
      (enlargedMaterialData T).E0 ((enlargedMaterialData T).sample (K.cell m)) :=
    le_enlargedMaterialData_E0 T _
  exact inv_anti₀ (mul_pos hB (Real.rpow_pos_of_pos hE _))
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE.le hle hB.le) hB.le)

/-- The principal clause survives the auxiliary replacement. -/
theorem referencePrincipal_replaceAuxiliaryColumn {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    (η : (S.height (3 / 4 : ℝ)).Space) (h : ReferencePrincipal T S C K) :
    ReferencePrincipal T (physicalSpacesReplaceAuxiliaryColumn S η)
      (geometryReplaceAuxiliaryColumn C η) (canonicalReplaceAuxiliaryColumn K η) := h

theorem n04Realization_referenceObligation : N04RealizationReferenceObligation := by
  intro W X
  have hD : IsAccumulatingProfile W.D := W.radial.1
  have hE0 : ∀ j, 1 ≤ W.T.E0 (W.T.sample j) := fun j => W.floor _
  have hprod := n04Coordinates_actual_whole_reference_nonAuxiliaryJets W.P W.metadata.selected
    W.metadata.first_two one_pos W.realizes W.hw W.coordinates W.hT W.hS W.through03 W.field
    X.e₀ hE0 X.κ_pos W.host X.optical X.cell X.cell_mem X.src
  refine ⟨hprod.choose, hprod.choose_spec.choose, hprod.choose_spec.choose_spec.1,
    hprod.choose_spec.choose_spec.2.1, ?_⟩
  intro e τ σ Q F buffer href b' ε' hb hε' hε'ε V hV hR
  have hrest := hprod.choose_spec.choose_spec.2.2 e τ σ Q buffer.region href
  have hprincipal := hrest.1 hε' hV
  have hjets := hrest.2
  have hN' := nonlinearPropertiesThrough03_restrict W.hT W.through03 hb le_rfl hε' hε'ε
  have hpack := exists_wholeReferenceGauge_auxiliary_package W.hT W.hS hN' (W.A X.e₀) e
    X.cell (fun i => positiveReferenceCylinderChart (hprod.choose i))
    (fun i => positiveReferenceCylinderInverse (hprod.choose i))
    (fun i p => hprod.choose_spec.choose i p.1) τ σ Q buffer hV hR
  let i := hpack.choose
  let l := hpack.choose_spec.choose
  let u := hpack.choose_spec.choose_spec.choose
  let η := hpack.choose_spec.choose_spec.choose_spec.choose
  have hp := hpack.choose_spec.choose_spec.choose_spec.choose_spec
  let S' := physicalSpacesReplaceAuxiliaryColumn W.S η
  let C' := geometryReplaceAuxiliaryColumn W.C η
  let L' := correctionReplaceAuxiliaryColumn W.L η
  let V' := canonicalReplaceAuxiliaryColumn V η
  have hS' : IsPhysicalSpaces W.D W.U S' := hp.2.2.2.1
  have hN'' : NonlinearPropertiesThrough03 W.D W.U S' C'
      (returnReplaceAuxiliaryColumn W.R η) L' b' W.loss ε' := hp.2.2.2.2.1
  have hgauge : AuxiliaryColumnGauge S' V' := hp.2.2.2.2.2.2.2.1
  have hauxReg : ∀ m, ContDiffOn ℝ ∞
        (atom W.D W.U S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn) unitStrip ∧
      ∀ p ∈ unitStrip,
        atom W.D W.U S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn
          (p + (0, Real.pi)) =
        atom W.D W.U S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn p :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hauxBound : ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ m p, p ∈ unitStrip →
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b
          (atom W.D W.U S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn) p| ≤
          A * W.U.E0 (W.U.sample (V'.cell m)) ^ A :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hauxEq : ∀ z ∈ stateNeighborhood S' C' b' ε', stateSector S' z.1 → ∀ m,
      EqOn (atom W.D W.U S' C' L' V' z m .auxiliaryColumn)
        (atom W.D W.U S' C' L' V' (C'.referenceState, 0) m .auxiliaryColumn) unitStrip :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hauxZero : ∀ z ∈ sectorNeighborhood S' b' ε' ε', ∀ m a b (p : unitStrip),
      differenceJets W.D W.U S' C' L' V' z .auxiliaryColumn m a b p = 0 :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsame (v : Atom) (hv : v ≠ .auxiliaryColumn) (z : AnnularState W.S × ℝ) (m : ℕ) :
      atom W.D W.U S' C' L' V' z m v = atom W.D W.U W.S W.C W.L V z m v :=
    canonicalAtom_replaceAuxiliaryColumn_of_ne W.D W.U W.S W.C W.L V η z m v hv
  have hUfloor (j : ℕ) : 1 ≤ W.U.E0 (W.U.sample j) :=
    (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hreference : ReferenceJets W.D W.U S' C' L' V' := by
    refine ⟨?_, ?_⟩
    · obtain ⟨B0, _, hother0⟩ := hjets 0
      intro m v
      by_cases hv : v = .auxiliaryColumn
      · subst v
        exact hauxReg m
      · have hf : atom W.D W.U S' C' L' V' (C'.referenceState, 0) m v =
            atom W.D W.U W.S W.C W.L V (W.C.referenceState, 0) m v :=
          hsame v hv (C'.referenceState, 0) m
        exact Eq.mpr (congrArg (fun f : PolarPoint → ℝ =>
          ContDiffOn ℝ ∞ f unitStrip ∧
            ∀ p ∈ unitStrip, f (p + (0, Real.pi)) = f p) hf)
          ⟨(hother0 m v hv).1, (hother0 m v hv).2.1⟩
    · intro s
      obtain ⟨B1, hB1, hrest⟩ := hjets s
      obtain ⟨B2, hB2, haux⟩ := hauxBound s
      let B : ℝ := max B1 B2
      have hB : 0 < B := hB1.trans_le (le_max_left _ _)
      refine ⟨B, hB, ?_⟩
      intro m v p hp a b hab
      have ht : 1 ≤ W.U.E0 (W.U.sample (V'.cell m)) := hUfloor _
      have hcost {d : ℝ} (hd : d ≤ B) :
          d * W.U.E0 (W.U.sample (V'.cell m)) ^ d ≤
            B * W.U.E0 (W.U.sample (V'.cell m)) ^ B :=
        mul_le_mul hd (Real.rpow_le_rpow_of_exponent_le ht hd)
          (Real.rpow_nonneg (zero_le_one.trans ht) _) hB.le
      by_cases hv : v = .auxiliaryColumn
      · subst v
        exact (haux m p hp a b hab).trans (hcost (le_max_right _ _))
      · have hf : atom W.D W.U S' C' L' V' (C'.referenceState, 0) m v =
            atom W.D W.U W.S W.C W.L V (W.C.referenceState, 0) m v :=
          hsame v hv (C'.referenceState, 0) m
        exact (congrArg (fun f : PolarPoint → ℝ =>
          |mixedDerivative a b f p|) hf).trans_le
            (((hrest m v hv).2.2 p hp a b hab).trans (hcost (le_max_left _ _)))
  have hpos : ∀ m, 0 < W.T.E0 (W.T.sample (V.cell m)) := fun m =>
    zero_lt_one.trans_le (hE0 _)
  refine ⟨η, hS', referencePrincipal_replaceAuxiliaryColumn η
    (referencePrincipal_enlargedMaterialData hpos hprincipal), hreference, hgauge, ?_,
    hauxZero⟩
  intro z hz m
  have hz' : liftSectorParameter S' C' z ∈ stateNeighborhood S' C' b' ε' :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector S' (liftSectorParameter S' C' z).1 :=
    hN''.1.1.2.2.1.liftSectorParameter_sector z
  have hEq := hauxEq _ hz' hs m
  refine ⟨(hauxReg m).1.congr hEq, fun p hp => ?_⟩
  have hp' : p + (0, Real.pi) ∈ unitStrip := by
    simp only [unitStrip, mem_prod, mem_univ, and_true] at hp ⊢
    simpa only [Prod.fst_add, add_zero] using hp
  rw [hEq hp', hEq hp]
  exact (hauxReg m).2 p hp

end ContinuousFlexibility.Analysis
