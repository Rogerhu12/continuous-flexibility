module

public import ContinuousFlexibility.Analysis.FixedPositiveReferenceGeometryMaterialJets
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
public import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# Ten geometric reference atoms of the same positive family

The physical unit point and the canonical unit point are kept distinct.
At the reference state the stored chart, inverse and height are exactly
the supplied radial fields. Their ten geometric atoms therefore equal
the displayed scalar formulas, globally. The material bound keeps the
original sample, interval and all-order family; no interpolation is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped Topology ContDiff

private theorem positiveGeometry_scalar_data {Y H : ℝ → ℝ} {l r : ℝ}
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1) :
    ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ H ∧ ContDiff ℝ ∞ (Function.invFun Y) ∧
      (∀ x, 0 < deriv Y x) ∧
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
  have hYpos (x : ℝ) : 0 < deriv Y x := by
    have h := hgeometry.jacobian_positive (x, 0)
    rw [planeJacobian_positiveReferenceCylinderChart (p := (x, 0))
      (hY.differentiable (by simp) x)] at h
    exact h
  refine ⟨hY, hH, hχ, hYpos, ?_⟩
  intro x
  have hright (t : ℝ) : Y (Function.invFun Y t) = t :=
    congrArg Prod.fst (hgeometry.right_inverse (t, 0))
  exact (HasDerivAt.of_local_left_inverse hχ.continuous.continuousAt
    (hY.differentiable (by simp) (Function.invFun Y x)).hasDerivAt
    (hYpos _).ne' (Eventually.of_forall hright)).deriv

/-- The displayed geometry scalars are globally smooth, including the
actual inverse-coordinate derivatives used in the two source factors. -/
theorem positiveReferenceGeometryScalar_smooth {Y H : ℝ → ℝ} {l r : ℝ}
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1)
    (v : Atom) : ContDiff ℝ ∞ (positiveReferenceGeometryScalar l r Y H v) := by
  obtain ⟨hY, hH, hχ, _, _⟩ := positiveGeometry_scalar_data hgeometry
  have hHi : ContDiff ℝ ∞ (fun t => (H t)⁻¹) :=
    hH.inv (fun t => (hgeometry.height_positive (t, 0)).ne')
  have hYd : ContDiff ℝ ∞ (deriv Y) := (contDiff_infty_iff_deriv.mp hY).2
  have hχd : ContDiff ℝ ∞ (deriv (Function.invFun Y)) :=
    (contDiff_infty_iff_deriv.mp hχ).2
  have ha : ContDiff ℝ ∞ (fun t : ℝ => l + (r - l) * t) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  cases v
  case chartRadial => exact hY.comp ha
  case inverseRadial => exact (hχ.sub contDiff_const).div_const _
  case height => exact hH.comp ha
  case heightInverse => exact hHi.comp ha
  case jacobian => exact hYd.comp ha
  case jacobianInverse => exact hχd.comp (hY.comp ha)
  case sourceFactor => exact (hH.comp hχ).mul hχd
  case sourceFactorInverse => exact (hHi.comp hχ).mul (hYd.comp hχ)
  all_goals exact contDiff_const

/-- Exact stored fields and their actual endpoint metadata identify the
ten geometric atoms with the radial formulas. This is a full function
identity, so it also supplies all spatial germs without a new choice. -/
theorem positiveReferenceGeometry_actual_atom_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) {l r : ℝ} {Y H : ℝ → ℝ}
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1)
    (hl : K.left m = 0) (hr : K.right m = 1)
    (hpl : K.physicalLeft m = l) (hpr : K.physicalRight m = r)
    (hF : K.chart z m = positiveReferenceCylinderChart Y)
    (hG : K.inverseChart z m = positiveReferenceCylinderInverse Y)
    (hH : K.height z m = (fun p => H p.1))
    (v : Atom) (hv : v = .chartRadial ∨ v = .chartAngleDefect ∨
      v = .inverseRadial ∨ v = .inverseAngleDefect ∨ v = .height ∨
      v = .heightInverse ∨ v = .jacobian ∨ v = .jacobianInverse ∨
      v = .sourceFactor ∨ v = .sourceFactorInverse) :
    atom D T S C L K z m v =
      (fun p : PolarPoint => positiveReferenceGeometryScalar l r Y H v p.1) := by
  obtain ⟨hYs, _, _, hYpos, hχd⟩ := positiveGeometry_scalar_data hgeometry
  have hχY (t : ℝ) : Function.invFun Y (Y t) = t :=
    congrArg Prod.fst (hgeometry.left_inverse (t, 0))
  have hreciprocal (t : ℝ) : (deriv Y t)⁻¹ = deriv (Function.invFun Y) (Y t) := by
    rw [hχd, hχY]
  have hunit (p : PolarPoint) : canonicalUnitPoint K m p = p := by
    change (K.left m + (K.right m - K.left m) * p.1, p.2) = p
    simp only [hl, hr, sub_zero, one_mul, zero_add, Prod.mk.eta]
  have hphysical (p : PolarPoint) :
      physicalUnitPoint K m p = (l + (r - l) * p.1, p.2) := by
    simp only [physicalUnitPoint, hpl, hpr]
  have hJ (p : PolarPoint) : planeJacobian (K.chart z m) p = deriv Y p.1 := by
    rw [hF]
    exact planeJacobian_positiveReferenceCylinderChart
      (hYs.differentiable (by simp) p.1)
  have hsource (p : PolarPoint) : canonicalSource S K z m (fun _ => 1) p =
      H (Function.invFun Y p.1) * deriv (Function.invFun Y) p.1 := by
    change K.height z m (K.inverseChart z m p) * 1 /
      |planeJacobian (K.chart z m) (K.inverseChart z m p)| = _
    rw [hG, hH, hJ]
    change H (Function.invFun Y p.1) * 1 / |deriv Y (Function.invFun Y p.1)| = _
    rw [mul_one, abs_of_pos (hYpos _), div_eq_mul_inv, hχd]
  funext p
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change ((K.chart z m (physicalUnitPoint K m p)).1 - K.left m) /
      (K.right m - K.left m) = _
    rw [hphysical, hF, hl, hr]
    simp only [positiveReferenceCylinderChart, positiveReferenceGeometryScalar,
      sub_zero, div_one]
  · change (K.chart z m (physicalUnitPoint K m p)).2 -
      (physicalUnitPoint K m p).2 = _
    rw [hphysical, hF]
    simp only [positiveReferenceCylinderChart, positiveReferenceGeometryScalar, sub_self]
  · change ((K.inverseChart z m (canonicalUnitPoint K m p)).1 - K.physicalLeft m) /
      (K.physicalRight m - K.physicalLeft m) = _
    rw [hunit, hG, hpl, hpr]
    rfl
  · change (K.inverseChart z m (canonicalUnitPoint K m p)).2 -
      (canonicalUnitPoint K m p).2 = _
    rw [hunit, hG]
    simp only [positiveReferenceCylinderInverse, positiveReferenceGeometryScalar, sub_self]
  · change K.height z m (physicalUnitPoint K m p) = _
    rw [hphysical, hH]
    rfl
  · change (K.height z m (physicalUnitPoint K m p))⁻¹ = _
    rw [hphysical, hH]
    rfl
  · change |planeJacobian (K.chart z m) (physicalUnitPoint K m p)| = _
    rw [hphysical, hJ, abs_of_pos (hYpos _)]
    rfl
  · change |planeJacobian (K.chart z m) (physicalUnitPoint K m p)|⁻¹ = _
    rw [hphysical, hJ, abs_of_pos (hYpos _), hreciprocal]
    rfl
  · change canonicalSource S K z m (fun _ => 1) (canonicalUnitPoint K m p) = _
    rw [hunit, hsource]
    rfl
  · change (canonicalSource S K z m (fun _ => 1) (canonicalUnitPoint K m p))⁻¹ = _
    rw [hunit, hsource]
    simp only [positiveReferenceGeometryScalar, hχd, mul_inv_rev, inv_inv]
    ring

/-- All ten geometric atoms belong to the same supplied family and the
same actual atlas. The constants precede even the underlying negative
atlas, because no negative field is used on these positive pieces. -/
theorem n04WholeReferenceGauge_positive_geometryReferenceJets_fixedFamily
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    {C0 : ℝ} (hC0 : 1 ≤ C0) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j))
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j))
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    {B : ℝ} (hB : 1 ≤ B)
    (hwidth : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      n04PositiveRight i - n04PositiveLeft i ≤ B * (C0 * T.E0 (T.sample (cell i))) ^ B ∧
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ B * (C0 * T.E0 (T.sample (cell i))) ^ B)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
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
    ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧ ∀ (K : CanonicalData S)
      (e : ℕ ≃ N04WholePieceIndex D)
      (τ σ : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (Q : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ),
      (∀ i, τ (C.referenceState, 0) i = id ∧
        σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
      let V := n04WholeReferenceGaugeAtlasData C L K e cell
        (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N
      ∀ m, V.positive m = true → ∀ v : Atom,
        (v = .chartRadial ∨ v = .chartAngleDefect ∨ v = .inverseRadial ∨
          v = .inverseAngleDefect ∨ v = .height ∨ v = .heightInverse ∨
          v = .jacobian ∨ v = .jacobianInverse ∨
          v = .sourceFactor ∨ v = .sourceFactorInverse) →
        ContDiffOn ℝ ∞ (atom D T S C L V (C.referenceState, 0) m v) unitStrip ∧
        (∀ p ∈ unitStrip, atom D T S C L V (C.referenceState, 0) m v
          (p + (0, Real.pi)) = atom D T S C L V (C.referenceState, 0) m v p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom D T S C L V (C.referenceState, 0) m v) p| ≤
            BM * T.E0 (T.sample (V.cell m)) ^ BM := by
  have hlr (i : N04PositiveComponent D.a D.b (deriv D.w)) :
      n04PositiveLeft i < n04PositiveRight i := by
    have hx : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
    have hh := (hgeometry i).inverse_maps_open
      (x := ((1 / 2 : ℝ), 0)) ⟨hx, mem_univ _⟩
    exact hh.1.1.trans hh.1.2
  have hscalar := fixedPositiveReference_geometry_material_jets
    (fun i => C0 * T.E0 (T.sample (cell i))) (fun i => hfloor (cell i))
    n04PositiveLeft n04PositiveRight hlr hB hwidth Y H hgeometry hjets
  intro s
  obtain ⟨M, hM, hactual⟩ := hscalar s
  obtain ⟨BM, hBM, hpack⟩ := coefficientEnvelope_pack (M * C0 ^ M) M
  refine ⟨BM, hBM, ?_⟩
  intro K e τ σ Q N href
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
      obtain ⟨hl, hr, hpl, hpr, _, hsample, _, hF, hG, hH, _, _⟩ :=
        n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell ψ χ h₀ τ σ Q N
          (C.referenceState, 0) m i hi
      have he := wholePositiveReferenceGauge_reference (ψ i) (χ i) (h₀ i)
        (href i).1 (href i).2.1 (href i).2.2
      have hEq := positiveReferenceGeometry_actual_atom_eq (D := D) (T := T)
        C L V (C.referenceState, 0) m
        (hgeometry i) hl hr hpl hpr (hF.trans he.1) (hG.trans he.2.1)
        (hH.trans he.2.2) v hv
      refine ⟨?_, ?_, ?_⟩
      · rw [hEq]
        exact ((positiveReferenceGeometryScalar_smooth (hgeometry i) v).comp
          contDiff_fst).contDiffOn
      · intro p hp
        rw [hEq]
        simp only [Prod.add_def, add_zero]
      · intro p hp a b hab
        rw [hEq, n08_mixedDerivative_radial, hsample]
        let t : ℝ := T.E0 (T.sample (cell i))
        have ht : 1 ≤ t := hE0 (cell i)
        have hcost : M * (C0 * t) ^ M ≤ BM * t ^ BM := by
          calc
            _ = (M * C0 ^ M) * t ^ M := by
              rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
              ring
            _ ≤ BM * t ^ BM := hpack t ht
        by_cases hb : b = 0
        · rw [if_pos hb]
          exact (hactual i v p.1 hp.1 a (by omega)).trans hcost
        · rw [if_neg hb, abs_zero]
          exact mul_nonneg hBM.le (Real.rpow_nonneg (zero_le_one.trans ht) _)

end ContinuousFlexibility.Analysis
