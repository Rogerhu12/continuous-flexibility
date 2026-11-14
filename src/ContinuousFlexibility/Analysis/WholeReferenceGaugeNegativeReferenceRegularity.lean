import ContinuousFlexibility.Analysis.ActualNegativeReferenceGeometryFields
import ContinuousFlexibility.Analysis.ActualNegativeReferencePotentialGerms
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeAtomTransport

/-!
# Qualitative reference atoms on the same negative pieces

The stored scalar slices are smooth on their true open intervals. The
actual field identities make their unit atoms radial, including the
potential. These qualitative conclusions need no optical lower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

private theorem negativeReference_unit_radial_regular
    {f : PolarPoint → ℝ} {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioo (0 : ℝ) 1))
    (he : EqOn f (fun p : PolarPoint => g p.1) unitStrip) :
    ContDiffOn ℝ ∞ f unitStrip ∧
      ∀ p ∈ unitStrip, f (p + (0, Real.pi)) = f p := by
  have hmodel : ContDiffOn ℝ ∞ (fun p : PolarPoint => g p.1) unitStrip :=
    hg.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  refine ⟨hmodel.congr (fun p hp => he hp), ?_⟩
  intro p hp
  have hp' : p + (0, Real.pi) ∈ unitStrip := by
    refine ⟨?_, mem_univ _⟩
    simpa only [Prod.fst_add, add_zero] using hp.1
  rw [he hp', he hp]
  simp only [Prod.fst_add, add_zero]

/-- All ten negative geometric atoms and the negative potential are
smooth and pi-periodic on the actual unit strip. Only the original
Through03 geometry is used; the positive fields are arbitrary and the
old negative atlas is unchanged. -/
theorem n04WholeReferenceGauge_negative_geometryPotentialReferenceRegularity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ₀ h₀ τ σ Q N
    ∀ m, V.positive m = false → ∀ v : Atom,
      (v = .chartRadial ∨ v = .chartAngleDefect ∨ v = .inverseRadial ∨
        v = .inverseAngleDefect ∨ v = .height ∨ v = .heightInverse ∨
        v = .jacobian ∨ v = .jacobianInverse ∨ v = .sourceFactor ∨
        v = .sourceFactorInverse ∨ v = .potential) →
      ContDiffOn ℝ ∞ (atom D T S C L V (C.referenceState, 0) m v) unitStrip ∧
        ∀ p ∈ unitStrip, atom D T S C L V (C.referenceState, 0) m v
          (p + (0, Real.pi)) = atom D T S C L V (C.referenceState, 0) m v p := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ₀ h₀ τ σ Q N
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  intro m hm v hv
  cases hi : e m with
  | inr i =>
      have hpositive : V.positive m = true := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hpositive.symm.trans hm).symm)
  | inl j =>
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hk : e₀ k = .inl j := by
        rcases j with ⟨r, side⟩
        cases side <;> simp only [k, K, n04bActualTypedAtlas,
          n04bTypedAtlasData_cutPair, Bool.false_eq_true, ite_false, ite_true,
          Equiv.apply_symm_apply]
      have hki : e₀.symm (.inl (j.1, j.2)) = k := by
        rw [← hk, e₀.symm_apply_apply]
      have hnegative : K.positive k = false := by
        simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_positive, hk,
          n04TypedPiecePositive]
      have hatom := n04WholeReferenceGaugeAtlasData_negative_atom T C L K e cell
        ψ χ₀ h₀ τ σ Q N z₀ m j hi hnegative v
      rw [hatom]
      let cut := n04bActualReferenceCut hN
      let l := n04bNegativeLeft C cut j
      let r := n04bNegativeRight C cut j
      let I := Ioo l r
      let J := Ioo (K.left k) (K.right k)
      let Y : ℝ → ℝ := fun t => (K.chart z₀ k (t, 0)).1
      let H : ℝ → ℝ := fun t => K.height z₀ k (t, 0)
      let χ : ℝ → ℝ := fun t => (K.inverseChart z₀ k (t, 0)).1
      let a : ℝ → ℝ := fun t => l + (r - l) * t
      let b : ℝ → ℝ := fun t => K.left k + (K.right k - K.left k) * t
      have hpl : K.physicalLeft k = l := by
        change n04bReferenceTypedLeft C cut (e₀ k) = l
        rw [hk] <;> rfl
      have hpr : K.physicalRight k = r := by
        change n04bReferenceTypedRight C cut (e₀ k) = r
        rw [hk] <;> rfl
      have hphysical (p : PolarPoint) : physicalUnitPoint K k p = (a p.1, p.2) := by
        simp only [physicalUnitPoint, hpl, hpr, a]
      have hcanonical (p : PolarPoint) : canonicalUnitPoint K k p = (b p.1, p.2) := rfl
      have hA : Blueprint.N04PartA D S C K base ε :=
        n04b_actualTypedAtlas_partA hT hS hN hfield e₀
      have hlr : l < r := by simpa only [hpl, hpr] using (hA.referenceBounds k).1
      have hcan : K.left k < K.right k := (hA.referenceBounds k).2.1
      have hmap (u v : ℝ) (huv : u < v) :
          MapsTo (fun t : ℝ => u + (v - u) * t) (Ioo (0 : ℝ) 1) (Ioo u v) := by
        intro t ht
        refine ⟨lt_add_of_pos_right u (mul_pos (sub_pos.mpr huv) ht.1), ?_⟩
        have hh := mul_lt_mul_of_pos_left ht.2 (sub_pos.mpr huv)
        linarith only [hh]
      have ha : ContDiff ℝ ∞ a := contDiff_const.add (contDiff_const.mul contDiff_id)
      have hb : ContDiff ℝ ∞ b := contDiff_const.add (contDiff_const.mul contDiff_id)
      have haI : MapsTo a (Ioo (0 : ℝ) 1) I := hmap l r hlr
      have hbJ : MapsTo b (Ioo (0 : ℝ) 1) J := hmap (K.left k) (K.right k) hcan
      have hscalar := n04Coordinates_actual_reference_negative_scalar_inverse
        hT hS hN hfield e₀ j.1 j.2
      have hfields := n04Coordinates_actual_reference_negative_geometry_fields
        hT hS hN hfield e₀ j.1 j.2
      have hpotential := n04Coordinates_actual_reference_negative_potential_germ
        hT hS hN hfield e₀ j.1 j.2
      simp only [hki] at hscalar hfields hpotential
      have hY : ContDiffOn ℝ ∞ Y I := hscalar.1
      have hH : ContDiffOn ℝ ∞ H I := hscalar.2.1
      have hχ : ContDiffOn ℝ ∞ χ J := hscalar.2.2.1
      have hχI : MapsTo χ J I := hscalar.2.2.2.1
      have hHne (x : ℝ) (hx : x ∈ I) : H x ≠ 0 :=
        (hscalar.2.2.2.2.2.2.1 x hx).1.ne'
      have hD := n04b_profileGeometry_of_through03 hN
      have hw : ContDiffOn ℝ ∞ D.w I := hD.2.2.1.1.contDiffOn
      have hwne (x : ℝ) (hx : x ∈ I) : D.w x ≠ 0 := by
        have hcore : x ∈ radialCore D := by
          have hh : x ∈ Ioo (K.physicalLeft k) (K.physicalRight k) := by
            simpa only [hpl, hpr] using hx
          exact (hA.referenceBounds k).2.2 hh
        exact (hD.2.2.2.2.1 x hcore).ne'
      have hHi : ContDiffOn ℝ ∞ (fun x => (H x)⁻¹) I := hH.inv hHne
      have hwi : ContDiffOn ℝ ∞ (fun x => (D.w x)⁻¹) I := hw.inv hwne
      have hJ : ContDiffOn ℝ ∞ (fun x => H x ^ (-2 : ℝ) * (D.w x)⁻¹) I :=
        (hH.rpow_const_of_ne hHne).mul hwi
      have hJi : ContDiffOn ℝ ∞ (fun x => H x ^ 2 * D.w x) I := (hH.pow 2).mul hw
      have hSource : ContDiffOn ℝ ∞ (fun x => H x ^ 3 * D.w x) I := (hH.pow 3).mul hw
      have hSi : ContDiffOn ℝ ∞ (fun x => H x ^ (-3 : ℝ) * (D.w x)⁻¹) I :=
        (hH.rpow_const_of_ne hHne).mul hwi
      have hflux : ContDiffOn ℝ ∞ (fun x => D.w x * deriv H x) I :=
        hw.mul (hH.deriv_of_isOpen isOpen_Ioo (by simp))
      have hP : ContDiffOn ℝ ∞
          (fun x => D.w x * H x ^ 3 * deriv (fun t => D.w t * deriv H t) x) I :=
        (hw.mul (hH.pow 3)).mul (hflux.deriv_of_isOpen isOpen_Ioo (by simp))
      have hf (p : PolarPoint) (hp : p ∈ unitStrip) :=
        hfields.1 (a p.1, p.2) ⟨haI hp.1, mem_univ _⟩
      have hg (p : PolarPoint) (hp : p ∈ unitStrip) :=
        hfields.2 (b p.1, p.2) ⟨hbJ hp.1, mem_univ _⟩
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine negativeReference_unit_radial_regular
          (g := fun t => (Y (a t) - K.left k) / (K.right k - K.left k))
          (((hY.comp ha.contDiffOn haI).sub contDiffOn_const).div_const _) ?_
        intro p hp
        change ((K.chart z₀ k (physicalUnitPoint K k p)).1 - K.left k) /
          (K.right k - K.left k) = _
        rw [hphysical, (hf p hp).1]
      · refine negativeReference_unit_radial_regular (g := fun _ => 0) contDiffOn_const ?_
        intro p hp
        change (K.chart z₀ k (physicalUnitPoint K k p)).2 - (physicalUnitPoint K k p).2 = 0
        rw [hphysical, (hf p hp).1]
        exact sub_self _
      · refine negativeReference_unit_radial_regular
          (g := fun t => (χ (b t) - l) / (r - l))
          (((hχ.comp hb.contDiffOn hbJ).sub contDiffOn_const).div_const _) ?_
        intro p hp
        change ((K.inverseChart z₀ k (canonicalUnitPoint K k p)).1 - K.physicalLeft k) /
          (K.physicalRight k - K.physicalLeft k) = _
        rw [hcanonical, (hg p hp).1, hpl, hpr]
      · refine negativeReference_unit_radial_regular (g := fun _ => 0) contDiffOn_const ?_
        intro p hp
        change (K.inverseChart z₀ k (canonicalUnitPoint K k p)).2 - (canonicalUnitPoint K k p).2 = 0
        rw [hcanonical, (hg p hp).1]
        exact sub_self _
      · refine negativeReference_unit_radial_regular (g := fun t => H (a t))
          (hH.comp ha.contDiffOn haI) ?_
        intro p hp
        change K.height z₀ k (physicalUnitPoint K k p) = _
        rw [hphysical]
        exact (hf p hp).2.1
      · refine negativeReference_unit_radial_regular (g := fun t => (H (a t))⁻¹)
          (hHi.comp ha.contDiffOn haI) ?_
        intro p hp
        change (K.height z₀ k (physicalUnitPoint K k p))⁻¹ = _
        rw [hphysical, (hf p hp).2.1]
      · refine negativeReference_unit_radial_regular
          (g := fun t => H (a t) ^ (-2 : ℝ) * (D.w (a t))⁻¹)
          (hJ.comp ha.contDiffOn haI) ?_
        intro p hp
        change |planeJacobian (K.chart z₀ k) (physicalUnitPoint K k p)| = _
        rw [hphysical]
        exact (hf p hp).2.2.2.2.1
      · refine negativeReference_unit_radial_regular
          (g := fun t => H (a t) ^ 2 * D.w (a t)) (hJi.comp ha.contDiffOn haI) ?_
        intro p hp
        change |planeJacobian (K.chart z₀ k) (physicalUnitPoint K k p)|⁻¹ = _
        rw [hphysical]
        exact (hf p hp).2.2.2.2.2
      · refine negativeReference_unit_radial_regular
          (g := fun t => H (χ (b t)) ^ 3 * D.w (χ (b t)))
          ((hSource.comp hχ hχI).comp hb.contDiffOn hbJ) ?_
        intro p hp
        change canonicalSource S K z₀ k (fun _ => 1) (canonicalUnitPoint K k p) = _
        rw [hcanonical]
        exact (hg p hp).2.2.1
      · refine negativeReference_unit_radial_regular
          (g := fun t => H (χ (b t)) ^ (-3 : ℝ) * (D.w (χ (b t)))⁻¹)
          ((hSi.comp hχ hχI).comp hb.contDiffOn hbJ) ?_
        intro p hp
        change (canonicalSource S K z₀ k (fun _ => 1) (canonicalUnitPoint K k p))⁻¹ = _
        rw [hcanonical]
        exact (hg p hp).2.2.2
      · refine negativeReference_unit_radial_regular
          (g := fun t => D.w (χ (b t)) * H (χ (b t)) ^ 3 *
            deriv (fun x => D.w x * deriv H x) (χ (b t)))
          ((hP.comp hχ hχI).comp hb.contDiffOn hbJ) ?_
        intro p hp
        change K.potential z₀ k (canonicalUnitPoint K k p) = _
        rw [hcanonical]
        exact (hpotential (b p.1, p.2) ⟨hbJ hp.1, mem_univ _⟩).1.self_of_nhds

end ContinuousFlexibility.Analysis
