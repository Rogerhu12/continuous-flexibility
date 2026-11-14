module

public import ContinuousFlexibility.Analysis.MaterialWeightPhysicalPowerJets
public import ContinuousFlexibility.Analysis.ActualNegativeMaterialSamples
public import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient
public import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# Spatial material ratio jets on the actual negative halves

The denominator is the sample of the cell already stored in the actual
typed atlas. Its true bounded endpoint-coordinate displacement cancels
the same H or M power after physical differentiation. Unit rescaling
costs only the length of the physical annulus, not an inverse width.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

def materialHMNormalizedPower (T : MaterialData) (useM : Bool)
    (γ sample : ℝ) : ℝ → ℝ :=
  fun r => materialHMWeight T useM r ^ γ * materialHMWeight T useM sample ^ (-γ)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)

/-- Both ratio directions are included by taking gamma equal to 1 or -1.
The conclusion keeps the original sample and the original E0. -/
theorem n04bActualTypedAtlas_negative_materialRatio_physical_jets
    (useM : Bool) (γ : ℝ) (n : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) → ∀ r,
      r ∈ Icc (C.left m) (C.right m) →
      |iteratedDeriv n (materialHMNormalizedPower T useM γ
        (T.sample (K.cell k))) r| ≤ B * T.E0 (T.sample (K.cell k)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let w := materialHMWeight T useM
  obtain ⟨B, A, hB, hA, hphysical⟩ :=
    materialHMWeight_rpow_physical_jet_bound hT useM γ n
  have htransfer : ∃ J P : ℝ, 0 < J ∧ 0 ≤ P ∧
      ∀ k m side, e k = .inl (m, side) → ∀ r,
        r ∈ Icc (C.left m) (C.right m) →
        w r ^ γ * T.E0 r ^ A ≤
          J * (w (T.sample (K.cell k)) ^ γ * T.E0 (T.sample (K.cell k)) ^ P) := by
    cases useM with
    | false =>
      simpa only [w, materialHMWeight, Bool.false_eq_true, ite_false,
        Real.rpow_zero, mul_one] using
        n04bActualTypedAtlas_negative_material_sample_weights hT hS hN hfield e γ 0 A hA
    | true =>
      simpa only [w, materialHMWeight, ite_true, Real.rpow_zero, one_mul] using
        n04bActualTypedAtlas_negative_material_sample_weights hT hS hN hfield e 0 γ A hA
  obtain ⟨J, P, hJ, hP, htransfer⟩ := htransfer
  refine ⟨B * J, P, mul_nonneg hB hJ.le, hP, ?_⟩
  intro k m side hk r hr
  let s := T.sample (K.cell k)
  have hgeometry := hN.1.1.2.2.2.1.1 m
  have hrcore : r ∈ Ioo D.a D.b :=
    ⟨hgeometry.1.trans_le hr.1, hr.2.trans_lt hgeometry.2.2⟩
  have hspos : 0 < w s := materialHMWeight_pos hT useM
    (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))
  have hsnonneg : 0 ≤ w s ^ (-γ) := Real.rpow_nonneg hspos.le _
  have hcancel : w s ^ γ * w s ^ (-γ) = 1 := by
    rw [← Real.rpow_add hspos, add_neg_cancel, Real.rpow_zero]
  change |iteratedDeriv n (fun t => w t ^ γ * w s ^ (-γ)) r| ≤
    (B * J) * T.E0 s ^ P
  rw [iteratedDeriv_mul_const_field, abs_mul, abs_of_nonneg hsnonneg]
  calc
    _ ≤ (B * w r ^ γ * T.E0 r ^ A) * w s ^ (-γ) :=
      mul_le_mul_of_nonneg_right (hphysical r hrcore) hsnonneg
    _ = B * (w r ^ γ * T.E0 r ^ A) * w s ^ (-γ) := by ring
    _ ≤ B * (J * (w s ^ γ * T.E0 s ^ P)) * w s ^ (-γ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (htransfer k m side hk r hr) hB) hsnonneg
    _ = (B * J) * (w s ^ γ * w s ^ (-γ)) * T.E0 s ^ P := by ring
    _ = (B * J) * T.E0 s ^ P := by rw [hcancel, mul_one]

/-- The actual physical half, including its non-midpoint optical cut,
has positive length at most the annular width. Its unit points lie in
the same original negative component. -/
theorem n04bActualTypedAtlas_negative_physicalUnitPoint
    (k m : ℕ) (side : Bool) (hk : e k = .inl (m, side)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    0 < K.physicalRight k - K.physicalLeft k ∧
      K.physicalRight k - K.physicalLeft k ≤ D.b - D.a ∧
      ∀ p ∈ CanonicalGeometry.unitStrip,
        (CanonicalGeometry.physicalUnitPoint K k p).1 ∈ Ioo (C.left m) (C.right m) ∧
        (CanonicalGeometry.physicalUnitPoint K k p).1 ∈ Ioo D.a D.b := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  let a := n04bNegativeLeft C cut (m, side)
  let b := n04bNegativeRight C cut (m, side)
  have hleft : K.physicalLeft k = a := by
    change n04bReferenceTypedLeft C cut (e k) = a
    rw [hk]
    rfl
  have hright : K.physicalRight k = b := by
    change n04bReferenceTypedRight C cut (e k) = b
    rw [hk]
    rfl
  have hhalf : D.a < a ∧ a < b ∧ b < D.b :=
    n04b_negativeHalf_bounds hN.1.1.2.2.2.1 (n04bActualReferenceCut_mem hN) (m, side)
  have hlength : 0 < b - a := sub_pos.mpr hhalf.2.1
  refine ⟨by rw [hright, hleft]; exact hlength,
    by rw [hright, hleft]; linarith only [hhalf.1, hhalf.2.2], ?_⟩
  intro p hp
  have hlow : 0 < (b - a) * p.1 := mul_pos hlength hp.1.1
  have hupp : (b - a) * p.1 < b - a := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hp.1.2 hlength
  have hpoint : a + (b - a) * p.1 ∈ Ioo a b :=
    ⟨by linarith only [hlow], by linarith only [hupp]⟩
  change K.physicalLeft k + (K.physicalRight k - K.physicalLeft k) * p.1 ∈
    Ioo (C.left m) (C.right m) ∧
    K.physicalLeft k + (K.physicalRight k - K.physicalLeft k) * p.1 ∈ Ioo D.a D.b
  rw [hleft, hright]
  exact ⟨n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) hpoint,
    ⟨hhalf.1.trans hpoint.1, hpoint.2.trans hhalf.2.2⟩⟩

/-- All angular derivatives vanish. Each radial order of the actual
unit-half normalized power has a common sample-E0 bound. -/
theorem n04bActualTypedAtlas_negative_materialRatio_unit_jets
    (useM : Bool) (γ : ℝ) (a : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) →
      ∀ p ∈ CanonicalGeometry.unitStrip, ∀ b : ℕ,
        |mixedDerivative a b (fun q => materialHMNormalizedPower T useM γ
          (T.sample (K.cell k)) (CanonicalGeometry.physicalUnitPoint K k q).1) p| ≤
            B * T.E0 (T.sample (K.cell k)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨B, A, hB, hA, hphysical⟩ :=
    n04bActualTypedAtlas_negative_materialRatio_physical_jets hT hS hN hfield e useM γ a
  refine ⟨|D.b - D.a| ^ a * B, A,
    mul_nonneg (pow_nonneg (abs_nonneg _) _) hB, hA, ?_⟩
  intro k m side hk p hp b
  let f := materialHMNormalizedPower T useM γ (T.sample (K.cell k))
  let d := K.physicalLeft k
  let c := K.physicalRight k - K.physicalLeft k
  change |mixedDerivative a b (fun q => f (d + c * q.1)) p| ≤ _
  rw [n08_mixedDerivative_radial (fun r => f (d + c * r))]
  by_cases hb : b = 0
  · rw [if_pos hb, n07a_iteratedDeriv_comp_affine, abs_mul, abs_pow]
    obtain ⟨hc, hwidth, hpoint⟩ :=
      n04bActualTypedAtlas_negative_physicalUnitPoint hT hS hN hfield e k m side hk
    have hwhole := (hpoint p hp).1
    have hpow : |c| ^ a ≤ |D.b - D.a| ^ a := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_of_pos hc]
      exact hwidth.trans (le_abs_self _)
    have hvalue := hphysical k m side hk (d + c * p.1) ⟨hwhole.1.le, hwhole.2.le⟩
    calc
      _ ≤ |c| ^ a * (B * T.E0 (T.sample (K.cell k)) ^ A) :=
        mul_le_mul_of_nonneg_left hvalue (pow_nonneg (abs_nonneg _) _)
      _ ≤ |D.b - D.a| ^ a * (B * T.E0 (T.sample (K.cell k)) ^ A) :=
        mul_le_mul_of_nonneg_right hpow
          (mul_nonneg hB (Real.rpow_nonneg
            (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))).2.2.1.le _))
      _ = _ := by ring
  · rw [if_neg hb, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) hB)
      (Real.rpow_nonneg
        (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))).2.2.1.le _)

end ContinuousFlexibility.Analysis
