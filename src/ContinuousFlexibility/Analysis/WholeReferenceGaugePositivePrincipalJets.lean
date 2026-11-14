import ContinuousFlexibility.Analysis.FixedPositiveReferencePrincipalMaterialJets
import ContinuousFlexibility.Analysis.WholePositiveReferencePrincipal
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.LocalMixedProductBounds
import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# Four principal reference atoms for the same positive family

The actual whole atlas uses the supplied coordinate and height. Its four
principal atoms agree on the unit strip with the scalar radial formulas.
The same original cell and normalized material data are used in both the
atlas and the estimates. No reference family is selected in this proof.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped Topology ContDiff BigOperators

private def positivePrincipalScalar (w Y H : ℝ → ℝ) : Atom → ℝ → ℝ
  | .principalA => fun t => H (Function.invFun Y t) ^ 2 *
      w (Function.invFun Y t) * deriv Y (Function.invFun Y t)
  | .principalAInverse => fun t => (H (Function.invFun Y t))⁻¹ ^ 2 *
      (w (Function.invFun Y t))⁻¹ * deriv (Function.invFun Y) t
  | .principalC => fun t => H (Function.invFun Y t) ^ 2 *
      (deriv w (Function.invFun Y t) / Function.invFun Y t) * deriv (Function.invFun Y) t
  | _ => fun _ => 0

private theorem positivePrincipal_scalar_regularity {Y H : ℝ → ℝ} {l r : ℝ}
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1) :
    ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ H ∧ ContDiff ℝ ∞ (Function.invFun Y) ∧
      ∀ x, deriv (Function.invFun Y) x = (deriv Y (Function.invFun Y x))⁻¹ := by
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hY : ContDiff ℝ ∞ Y := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def] using
      hgeometry.chart_smooth.fst.comp hline
  have hH : ContDiff ℝ ∞ H := by
    simpa only [Function.comp_def] using hgeometry.height_smooth.comp hline
  have hχ : ContDiff ℝ ∞ (Function.invFun Y) := by
    simpa only [positiveReferenceCylinderInverse, Function.comp_def] using
      hgeometry.inverse_smooth.fst.comp hline
  refine ⟨hY, hH, hχ, ?_⟩
  intro x
  have hYpos : 0 < deriv Y (Function.invFun Y x) := by
    have h := hgeometry.jacobian_positive (Function.invFun Y x, 0)
    rw [planeJacobian_positiveReferenceCylinderChart (p := (Function.invFun Y x, 0))
      (hY.differentiable (by simp) (Function.invFun Y x))] at h
    exact h
  have hright (t : ℝ) : Y (Function.invFun Y t) = t :=
    congrArg Prod.fst (hgeometry.right_inverse (t, 0))
  exact (HasDerivAt.of_local_left_inverse hχ.continuous.continuousAt
    (hY.differentiable (by simp) (Function.invFun Y x)).hasDerivAt hYpos.ne'
    (Eventually.of_forall hright)).deriv

private theorem positivePrincipalScalar_smooth
    {D : ReferenceData} (hD : RadialProfileGeometry D)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) {Y H : ℝ → ℝ}
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (v : Atom) (hv : v = .principalA ∨ v = .principalAInverse ∨
      v = .principalB ∨ v = .principalC) :
    ContDiffOn ℝ ∞ (positivePrincipalScalar D.w Y H v) (Ioo (0 : ℝ) 1) := by
  obtain ⟨hY, hH, hχ, _⟩ := positivePrincipal_scalar_regularity hgeometry
  intro x hx
  let χ : ℝ → ℝ := Function.invFun Y
  have hr : χ x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) :=
    (hgeometry.inverse_maps_open (x := (x, 0)) ⟨hx, mem_univ _⟩).1
  have hcore : χ x ∈ radialCore D :=
    n04PositiveComponent_interval_subset (hD.2.2.1.1.continuous_deriv (by simp)) i hr
  have hHc : ContDiffAt ℝ ∞ (fun t => H (χ t)) x := hH.contDiffAt.comp x hχ.contDiffAt
  have hwc : ContDiffAt ℝ ∞ (fun t => D.w (χ t)) x :=
    hD.2.2.1.1.contDiffAt.comp x hχ.contDiffAt
  have hYdc : ContDiffAt ℝ ∞ (fun t => deriv Y (χ t)) x :=
    (contDiff_infty_iff_deriv.mp hY).2.contDiffAt.comp x hχ.contDiffAt
  have hχd : ContDiffAt ℝ ∞ (deriv χ) x := (contDiff_infty_iff_deriv.mp hχ).2.contDiffAt
  have hflux0 : ContDiffAt ℝ ∞ (fun y => deriv D.w y / y) (χ x) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2.contDiffAt.div
      contDiffAt_id (hD.1.trans hcore.1).ne'
  have hflux : ContDiffAt ℝ ∞ (fun t => deriv D.w (χ t) / χ t) x :=
    hflux0.comp x hχ.contDiffAt
  rcases hv with rfl | rfl | rfl | rfl
  · exact (((hHc.pow 2).mul hwc).mul hYdc).contDiffWithinAt
  · exact ((((hHc.inv (hgeometry.height_positive (χ x, 0)).ne').pow 2).mul
      (hwc.inv (hD.2.2.2.2.1 _ hcore).ne')).mul hχd).contDiffWithinAt
  · exact contDiffWithinAt_const
  · exact (((hHc.pow 2).mul hflux).mul hχd).contDiffWithinAt

private theorem positivePrincipal_actual_atom_eqOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ)
    (m : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (href : τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    (v : Atom) (hv : v = .principalA ∨ v = .principalAInverse ∨
      v = .principalB ∨ v = .principalC) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j))
      (fun j p => H j p.1) τ σ Q N
    EqOn (atom D T S C L V (C.referenceState, 0) m v)
      (fun p : PolarPoint => positivePrincipalScalar D.w (Y i) (H i) v p.1) unitStrip := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun j => positiveReferenceCylinderChart (Y j)
  let χ := fun j => positiveReferenceCylinderInverse (Y j)
  let h₀ := fun j (p : PolarPoint) => H j p.1
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  obtain ⟨hl, hr, _, _, _, _, _, _, _, _, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell ψ χ h₀ τ σ Q N
      (C.referenceState, 0) m i hi
  have hl' : V.left m = 0 := hl
  have hr' : V.right m = 1 := hr
  have hunit (p : PolarPoint) : canonicalUnitPoint V m p = p := by
    change (V.left m + (V.right m - V.left m) * p.1, p.2) = p
    simp only [hl', hr', sub_zero, one_mul, zero_add, Prod.mk.eta]
  have hχd := (positivePrincipal_scalar_regularity hgeometry).2.2.2
  show EqOn (atom D T S C L V (C.referenceState, 0) m v)
    (fun p : PolarPoint => positivePrincipalScalar D.w (Y i) (H i) v p.1) unitStrip
  intro p hp
  have hpCanonical : p ∈ canonicalOpen S V m := by
    simpa only [unitStrip, canonicalOpen, hl', hr'] using hp
  have hf := n04WholeReferenceGaugeAtlasData_positive_reference_formulas
    hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi hgeometry href hpCanonical
  rcases hv with rfl | rfl | rfl | rfl
  · change (V.coefficients (C.referenceState, 0) m).a (canonicalUnitPoint V m p) = _
    rw [hunit, hf.1]
    rfl
  · change ((V.coefficients (C.referenceState, 0) m).a (canonicalUnitPoint V m p))⁻¹ = _
    rw [hunit, hf.1]
    simp only [positivePrincipalScalar, hχd, mul_inv_rev, ← inv_pow]
    ring
  · change (V.coefficients (C.referenceState, 0) m).b (canonicalUnitPoint V m p) = _
    rw [hunit, hf.2.1]
    rfl
  · change (V.coefficients (C.referenceState, 0) m).c (canonicalUnitPoint V m p) = _
    rw [hunit, hf.2.2.1]
    simp only [positivePrincipalScalar, hχd, div_eq_mul_inv]
    ring

/-- The actual four positive principal atoms use one fixed reference
family and one material data set. The sample floor is supplied after the
actual material normalization, before that family was selected. -/
theorem n04WholeReferenceGauge_positive_principalReferenceJets_fixedFamily
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε) (e₀ : ℕ ≃ N04PieceIndex Γ.reference)
    {C0 : ℝ} (hC0 : 1 ≤ C0) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j))
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j))
    (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
    (Y H : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℝ → ℝ)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv (k + 1) (Y i) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A ∧
        |iteratedDeriv k (H i) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A ∧
        |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
        A * (C0 * T.E0 (T.sample (cell i))) ^ A) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ (e : ℕ ≃ N04WholePieceIndex Γ.reference)
        (τ σ : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → PolarPoint)
        (Q : (AnnularState S × ℝ) →
          N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
            PolarPoint → ℝ) (N : Set ℝ),
        (∀ i, τ (C.referenceState, 0) i = id ∧
          σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
      let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N
      ∀ m, V.positive m = true → ∀ v : Atom,
        (v = .principalA ∨ v = .principalAInverse ∨ v = .principalB ∨ v = .principalC) →
        ContDiffOn ℝ ∞ (atom Γ.reference T S C L V (C.referenceState, 0) m v) unitStrip ∧
        (∀ p ∈ unitStrip, atom Γ.reference T S C L V (C.referenceState, 0) m v
          (p + (0, Real.pi)) = atom Γ.reference T S C L V (C.referenceState, 0) m v p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom Γ.reference T S C L V (C.referenceState, 0) m v) p| ≤
            B * T.E0 (T.sample (V.cell m)) ^ B := by
  classical
  have hscalar := fixedPositiveReference_principal_material_jets
    P hSelected hband hq hΓ hw hcoordinates hN.1.1.2.2.2.1 hT hC0 hfloor
    cell hcell Y H hgeometry hjets
  choose M hM hactual using hscalar
  intro s
  let D : ℝ := 1 + ∑ k : Fin (s + 1), M k.val
  have hD : 1 ≤ D := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => zero_le_one.trans (hM k.val)))
  have hMD (a : ℕ) (ha : a ≤ s) : M a ≤ D :=
    (Finset.single_le_sum (f := fun k : Fin (s + 1) => M k.val)
      (fun k _ => zero_le_one.trans (hM k.val))
      (Finset.mem_univ (⟨a, by omega⟩ : Fin (s + 1)))).trans
        (le_add_of_nonneg_left zero_le_one)
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (D * C0 ^ D) D
  refine ⟨B, hB, ?_⟩
  intro e τ σ Q N href
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  dsimp only
  intro m hm v hv
  cases hi : e m with
  | inl j =>
      have hnegative : V.positive m = false := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hnegative.symm.trans hm))
  | inr i =>
      obtain ⟨_, _, _, _, _, hsample, _, _, _, _, _, _⟩ :=
        n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell ψ χ h₀ τ σ Q N
          (C.referenceState, 0) m i hi
      have hEq := positivePrincipal_actual_atom_eqOn hT hS hN hfield e₀ e cell Y H
        τ σ Q N m i hi (hgeometry i) (href i) v hv
      have hmodel : ContDiffOn ℝ ∞
          (fun p : PolarPoint => positivePrincipalScalar Γ.reference.w (Y i) (H i) v p.1)
          unitStrip := by
        intro p hp
        exact (((positivePrincipalScalar_smooth (n04b_profileGeometry_of_through03 hN)
          i (hgeometry i) v hv).contDiffAt (isOpen_Ioo.mem_nhds hp.1)).comp p
            contDiffAt_fst).contDiffWithinAt
      refine ⟨hmodel.congr (fun p hp => hEq hp), ?_, ?_⟩
      · intro p hp
        have hp' : p + (0, Real.pi) ∈ unitStrip := by
          refine ⟨?_, mem_univ _⟩
          change 0 < p.1 + 0 ∧ p.1 + 0 < 1
          simpa only [add_zero, mem_Ioo] using hp.1
        calc
          _ = positivePrincipalScalar Γ.reference.w (Y i) (H i) v (p + (0, Real.pi)).1 := hEq hp'
          _ = positivePrincipalScalar Γ.reference.w (Y i) (H i) v p.1 := by
            simp only [Prod.add_def, add_zero]
          _ = _ := (hEq hp).symm
      · intro p hp a b hab
        rw [mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) hEq a b hp,
          n08_mixedDerivative_radial, hsample]
        let t : ℝ := T.E0 (T.sample (cell i))
        let W : ℝ := C0 * t
        have ht : 1 ≤ t := hE0 (cell i)
        have hW : 1 ≤ W := hfloor (cell i)
        have hcost : M a * W ^ M a ≤ B * t ^ B := by
          calc
            _ ≤ D * W ^ D := mul_le_mul (hMD a (by omega))
              (Real.rpow_le_rpow_of_exponent_le hW (hMD a (by omega)))
              (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hD)
            _ = (D * C0 ^ D) * t ^ D := by
              dsimp only [W]
              rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
              ring
            _ ≤ B * t ^ B := hpack t ht
        have hrhs : 0 ≤ B * t ^ B :=
          mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans ht) _)
        by_cases hb : b = 0
        · rw [if_pos hb]
          have hj := hactual a i p.1 hp.1
          rcases hv with rfl | rfl | rfl | rfl
          · exact hj.1.trans hcost
          · exact hj.2.1.trans hcost
          · simpa only [positivePrincipalScalar, iteratedDeriv_const, ite_self, abs_zero] using hrhs
          · exact hj.2.2.trans hcost
        · rw [if_neg hb, abs_zero]
          exact hrhs

end ContinuousFlexibility.Analysis
