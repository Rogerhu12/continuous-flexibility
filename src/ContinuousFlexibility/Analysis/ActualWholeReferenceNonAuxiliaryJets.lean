import ContinuousFlexibility.Analysis.ActualPositiveReferenceFifteenAtoms
import ContinuousFlexibility.Analysis.WholeReferenceGaugePositiveScalarColumnJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeGeometryJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativePrincipalJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativePotentialReferenceJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeScalarColumnJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeReferenceRegularity
import ContinuousFlexibility.Analysis.WholeReferenceGaugeStaticReferenceJets
import ContinuousFlexibility.Analysis.CanonicalReferenceDividedJets
import ContinuousFlexibility.Analysis.CanonicalAuxiliaryAtomPreservation
import ContinuousFlexibility.Analysis.ActualPositiveReferencePrincipalAssembly

/-!
# All non-auxiliary reference atoms of one actual whole atlas

The positive producer is invoked once at the original material data. Its
coordinate, height, endpoint sources and midpoint samples are retained.
The original negative atlas is also retained. Enlarging only E0 changes
the two E0 ratios; their actual estimates come from the static-atom proof.
Every other enlarged atom is the same full function. A finite numerical
maximum is taken before the piece and atom, at each spatial order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff

theorem n04Coordinates_actual_whole_reference_nonAuxiliaryJets
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε κ : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex Γ.reference)
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j)) (hκ : 0 < κ)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      κ⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-κ) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x))
    (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
    (src : ∀ i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
      ∀ side, N04PositiveEndpointSource C i side) :
    let A := n04bActualTypedAtlas hT hS hN hfield e₀
    ∃ Y H : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℝ → ℝ,
      N04PositiveReferenceFamily A src 4 Y H ∧
      ∀ (e : ℕ ≃ N04WholePieceIndex Γ.reference)
        (τ σ : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → PolarPoint)
        (Q : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → ℝ) (N : Set ℝ),
        (∀ i, τ (C.referenceState, 0) i = id ∧
          σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
      let V := n04WholeReferenceGaugeAtlasData C L A e cell
        (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N
      let U := enlargedMaterialData T
      (∀ {newBase : ℕ} {ε' : ℝ}, 0 < ε' →
        CanonicalGeometry Γ.reference S C V newBase ε' →
          CanonicalGeometry.ReferencePrincipal T S C V) ∧
      ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧ ∀ m (v : Atom), v ≠ .auxiliaryColumn →
        ContDiffOn ℝ ∞ (atom Γ.reference U S C L V (C.referenceState, 0) m v) unitStrip ∧
        (∀ p ∈ unitStrip, atom Γ.reference U S C L V (C.referenceState, 0) m v
          (p + (0, Real.pi)) = atom Γ.reference U S C L V (C.referenceState, 0) m v p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom Γ.reference U S C L V (C.referenceState, 0) m v) p| ≤
            BM * U.E0 (U.sample (V.cell m)) ^ BM := by
  classical
  dsimp only
  obtain ⟨C0, hC0, hfloor, B, hB, hfinite, hfields⟩ :=
    n04Coordinates_actual_positive_reference_fifteenAtoms
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀
      hE0 hκ hhost hoptical cell hcell src
  let A := n04bActualTypedAtlas hT hS hN hfield e₀
  let W := fun i => B * (C0 * T.E0 (T.sample (cell i))) ^ B
  let δ := fun i => positiveReferenceTaylorWidth 3
    (n04PositiveLeft i) (n04PositiveRight i) (W i)⁻¹ (W i)
  let ys := fun i side => radialEndpointTaylorSlice 4
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src i side) A)
  let hs := fun i side => radialEndpointTaylorSlice 4
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src i side) A)
  let Y := fun i => positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (deriv (ys i false)) (deriv (ys i true))
  let H := fun i => positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (hs i false) (hs i true)
  obtain ⟨hfamily, hjets, hpositive⟩ := hfields
  have hgeometry (i) : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1 := (hfamily i).1
  have hwidth (i) : n04PositiveRight i - n04PositiveLeft i ≤ W i ∧
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ W i := by
    have hi := hfinite i (cell i) (hcell i) (src i)
    exact ⟨hi.2.2.1, hi.2.1⟩
  have hpositiveColumns := n04WholeReferenceGauge_positive_scalarColumnReferenceJets_fixedFamily
    hS hN hC0 hfloor hE0 cell hB hwidth Y H hgeometry hjets
  have hraw : ∀ m, ∃ j, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells j ∧
      ∀ x ∈ Ioo (C.left m) (C.right m),
        κ⁻¹ * T.E0 (T.sample j) ^ (-κ) * min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x) :=
    fun m => ⟨C.cell m, hhost m, hoptical m⟩
  obtain ⟨BN, hBN, hnegativePrincipal⟩ :=
    n04WholeReferenceGauge_negative_principalReferenceJets_enlargedMaterialData
      hT hS hN hfield e₀
  refine ⟨Y, H, hfamily, ?_⟩
  intro e τ σ Q N href
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L A e cell ψ χ h₀ τ σ Q N
  let U := enlargedMaterialData T
  have hUfloor (j : ℕ) : 1 ≤ U.E0 (U.sample j) :=
    one_le_enlargedMaterialData_E0 hT (materialSample_mem_interval hΓ.2.1 hT j)
  obtain ⟨hstaticRegular, hstatic⟩ :=
    n04WholeReferenceGauge_staticReferenceJets_enlargedMaterialData
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield
      e₀ e cell hcell ψ χ h₀ τ σ Q N
  have hdivided := n04WholeReferenceGauge_reference_dividedJets
    U S C L A e cell ψ χ h₀ τ σ Q N (fun j => zero_le_one.trans (hUfloor j))
  have hnegativeRegular := n04WholeReferenceGauge_negative_geometryPotentialReferenceRegularity
    hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N
  have hrefMem := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hrefSector := n04b_referenceState_sector hN.1.1.2.2.1
  dsimp only
  refine ⟨fun hε' hgeo => n04WholeReferenceGauge_actual_prescribed_referencePrincipal
    P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e₀ 3 hC0 hB hE0 hfinite
    e cell hcell src τ σ Q N href hε' hgeo, fun s => ?_⟩
  obtain ⟨BP, hBP, hpositiveS⟩ := hpositive s
  obtain ⟨BC, hBC, hpositiveColumnsS⟩ := hpositiveColumns s
  obtain ⟨BG, hBG, hnegativeGeometryS⟩ :=
    n04WholeReferenceGauge_negative_geometryReferenceJets_enlargedMaterialData
      hT hS hN hfield e₀ hκ s
  obtain ⟨BV, hBV, hnegativePotentialS⟩ :=
    n04WholeReferenceGauge_negative_potentialReferenceJets_enlargedMaterialData
      hT hS hN hfield e₀ hκ s
  obtain ⟨BZ, hBZ, hnegativeColumnsS⟩ :=
    n04WholeReferenceGauge_negative_scalarColumnReferenceJets_enlargedMaterialData
      hT hS hN hfield e₀ hκ s
  obtain ⟨BS, hBS, hstaticS⟩ := hstatic s
  obtain ⟨BD, hBD, hdividedS⟩ := hdivided s
  let BM : ℝ := 1 + BP + BC + BG + BN + BV + BZ + BS + BD
  have hBM : 0 < BM := by dsimp only [BM]; positivity
  have hlimits : BP ≤ BM ∧ BC ≤ BM ∧ BG ≤ BM ∧ BN ≤ BM ∧
      BV ≤ BM ∧ BZ ≤ BM ∧ BS ≤ BM ∧ BD ≤ BM := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [BM] <;>
      linarith only [hBP, hBC, hBG, hBN, hBV, hBZ, hBS, hBD]
  obtain ⟨hBPB, hBCB, hBGB, hBNB, hBVB, hBZB, hBSB, hBDB⟩ := hlimits
  let Estimate : ℝ → ℕ → Atom → Prop := fun d m v =>
    ContDiffOn ℝ ∞ (atom Γ.reference U S C L V (C.referenceState, 0) m v) unitStrip ∧
    (∀ p ∈ unitStrip, atom Γ.reference U S C L V (C.referenceState, 0) m v
      (p + (0, Real.pi)) = atom Γ.reference U S C L V (C.referenceState, 0) m v p) ∧
    ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (atom Γ.reference U S C L V (C.referenceState, 0) m v) p| ≤
        d * U.E0 (U.sample (V.cell m)) ^ d
  have hraise {d : ℝ} {m : ℕ} {v : Atom} (hd : d ≤ BM)
      (h : Estimate d m v) : Estimate BM m v := by
    refine ⟨h.1, h.2.1, ?_⟩
    intro p hp a b hab
    have ht := hUfloor (V.cell m)
    exact (h.2.2 p hp a b hab).trans
      (mul_le_mul hd (Real.rpow_le_rpow_of_exponent_le ht hd)
        (Real.rpow_nonneg (zero_le_one.trans ht) _) hBM.le)
  have henlarge {d : ℝ} (hd0 : 0 < d) (hd : d ≤ BM) (m : ℕ) (v : Atom)
      (hE : v ≠ .ratioE0) (hEi : v ≠ .ratioE0Inverse)
      (h : ContDiffOn ℝ ∞ (atom Γ.reference T S C L V (C.referenceState, 0) m v) unitStrip ∧
        (∀ p ∈ unitStrip, atom Γ.reference T S C L V (C.referenceState, 0) m v
          (p + (0, Real.pi)) = atom Γ.reference T S C L V (C.referenceState, 0) m v p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom Γ.reference T S C L V (C.referenceState, 0) m v) p| ≤
            d * T.E0 (T.sample (V.cell m)) ^ d) : Estimate BM m v := by
    apply hraise hd
    dsimp only [Estimate]
    rw [canonicalAtom_enlargedMaterialData_of_ne_ratios Γ.reference T S C L V
      (C.referenceState, 0) m v hE hEi]
    refine ⟨h.1, h.2.1, ?_⟩
    intro p hp a b hab
    exact (h.2.2 p hp a b hab).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans (hE0 (V.cell m)))
        (le_enlargedMaterialData_E0 T (T.sample (V.cell m))) hd0.le) hd0.le)
  have hgeom (m : ℕ) (v : Atom)
      (hv : v = .chartRadial ∨ v = .chartAngleDefect ∨ v = .inverseRadial ∨
        v = .inverseAngleDefect ∨ v = .height ∨ v = .heightInverse ∨
        v = .jacobian ∨ v = .jacobianInverse ∨
        v = .sourceFactor ∨ v = .sourceFactorInverse) : Estimate BM m v := by
    have hE : v ≠ .ratioE0 := by
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hEi : v ≠ .ratioE0Inverse := by
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    cases hm : V.positive m with
    | false =>
      have hr := hnegativeRegular m hm v (by
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      have he := canonicalAtom_enlargedMaterialData_of_ne_ratios Γ.reference T S C L V
        (C.referenceState, 0) m v hE hEi
      apply hraise hBGB
      refine ⟨?_, ?_, hnegativeGeometryS e cell ψ χ h₀ τ σ Q N hraw m hm v hv⟩
      · simpa only [he] using hr.1
      · simpa only [he] using hr.2
    | true =>
      exact henlarge hBP hBPB m v hE hEi
        (hpositiveS e τ σ Q N href m hm v (Or.inl hv))
  have hprincipal (m : ℕ) (v : Atom)
      (hv : v = .principalA ∨ v = .principalAInverse ∨
        v = .principalB ∨ v = .principalC) : Estimate BM m v := by
    cases hm : V.positive m with
    | false =>
      have hh := hnegativePrincipal e cell ψ χ h₀ τ σ Q N
        (C.referenceState, 0) hrefMem hrefSector m hm v hv
      exact hraise hBNB ⟨hh.1, hh.2.1, fun p hp a b _ => hh.2.2 p hp a b⟩
    | true =>
      exact henlarge hBP hBPB m v
        (by rcases hv with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hv with rfl | rfl | rfl | rfl <;> decide)
        (hpositiveS e τ σ Q N href m hm v (Or.inr (Or.inl hv)))
  have hpotential (m : ℕ) : Estimate BM m .potential := by
    cases hm : V.positive m with
    | false =>
      have hr := hnegativeRegular m hm .potential (by simp)
      have he := canonicalAtom_enlargedMaterialData_of_ne_ratios Γ.reference T S C L V
        (C.referenceState, 0) m .potential (by decide) (by decide)
      apply hraise hBVB
      refine ⟨?_, ?_, hnegativePotentialS e cell ψ χ h₀ τ σ Q N hraw m hm⟩
      · simpa only [he] using hr.1
      · simpa only [he] using hr.2
    | true =>
      exact henlarge hBP hBPB m .potential (by decide) (by decide)
        (hpositiveS e τ σ Q N href m hm .potential (Or.inr (Or.inr rfl)))
  have hcolumns (m : ℕ) (v : Atom) (hv : v = .leftColumn ∨ v = .nuColumn) :
      Estimate BM m v := by
    cases hm : V.positive m with
    | false =>
      exact hraise hBZB
        (hnegativeColumnsS e cell ψ χ h₀ τ σ Q N hraw m hm v hv)
    | true =>
      exact henlarge hBC hBCB m v
        (by rcases hv with rfl | rfl <;> decide)
        (by rcases hv with rfl | rfl <;> decide)
        (hpositiveColumnsS A e τ σ Q N href m hm v hv)
  have hfixed (m : ℕ) (v : Atom)
      (hv : CanonicalFixedGeometryAtom v ∨ CanonicalMaterialRatioAtom v) :
      Estimate BM m v :=
    hraise hBSB ⟨(hstaticRegular (C.referenceState, 0) m v hv).1,
      (hstaticRegular (C.referenceState, 0) m v hv).2,
      hstaticS (C.referenceState, 0) m v hv⟩
  have hdivision (m : ℕ) (v : Atom)
      (hv : v = .dividedA ∨ v = .dividedB ∨ v = .dividedC) : Estimate BM m v :=
    hraise hBDB (hdividedS m v hv)
  refine ⟨BM, hBM, ?_⟩
  intro m v haux
  change Estimate BM m v
  cases v with
  | chartRadial => exact hgeom m _ (by simp)
  | chartAngleDefect => exact hgeom m _ (by simp)
  | inverseRadial => exact hgeom m _ (by simp)
  | inverseAngleDefect => exact hgeom m _ (by simp)
  | height => exact hgeom m _ (by simp)
  | heightInverse => exact hgeom m _ (by simp)
  | jacobian => exact hgeom m _ (by simp)
  | jacobianInverse => exact hgeom m _ (by simp)
  | sourceFactor => exact hgeom m _ (by simp)
  | sourceFactorInverse => exact hgeom m _ (by simp)
  | principalA => exact hprincipal m _ (by simp)
  | principalAInverse => exact hprincipal m _ (by simp)
  | principalB => exact hprincipal m _ (by simp)
  | principalC => exact hprincipal m _ (by simp)
  | potential => exact hpotential m
  | dividedA => exact hdivision m _ (by simp)
  | dividedB => exact hdivision m _ (by simp)
  | dividedC => exact hdivision m _ (by simp)
  | leftColumn => exact hcolumns m _ (by simp)
  | nuColumn => exact hcolumns m _ (by simp)
  | auxiliaryColumn => exact (haux rfl).elim
  | physicalLength => exact hfixed m _ (by simp [CanonicalFixedGeometryAtom])
  | physicalLengthInverse => exact hfixed m _ (by simp [CanonicalFixedGeometryAtom])
  | canonicalLength => exact hfixed m _ (by simp [CanonicalFixedGeometryAtom])
  | canonicalLengthInverse => exact hfixed m _ (by simp [CanonicalFixedGeometryAtom])
  | materialEll => exact hfixed m _ (by simp [CanonicalFixedGeometryAtom])
  | materialEllInverse => exact hfixed m _ (by simp [CanonicalFixedGeometryAtom])
  | ratioH => exact hfixed m _ (by simp [CanonicalMaterialRatioAtom])
  | ratioHInverse => exact hfixed m _ (by simp [CanonicalMaterialRatioAtom])
  | ratioM => exact hfixed m _ (by simp [CanonicalMaterialRatioAtom])
  | ratioMInverse => exact hfixed m _ (by simp [CanonicalMaterialRatioAtom])
  | ratioE0 => exact hfixed m _ (by simp [CanonicalMaterialRatioAtom])
  | ratioE0Inverse => exact hfixed m _ (by simp [CanonicalMaterialRatioAtom])

end ContinuousFlexibility.Analysis
