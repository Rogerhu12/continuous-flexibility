import ContinuousFlexibility.Analysis.N05ReferenceHeightWindow
import ContinuousFlexibility.Analysis.N05PhysicalPieces
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite reference-piece packing from existing N04 geometry

Disjoint actual reference intervals with an explicit positive width
have finite fibers and a quantitative count. This module uses only
the current N04 geometry; no primitive-jet certificate is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

theorem n05_reference_piece_finite_packing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {Z : Set ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hwidth : ∀ i ∈ Z, δ ≤ K.physicalRight i - K.physicalLeft i) :
    Z.Finite ∧ (Z.ncard : ℝ) * δ ≤ D.b - D.a := by
  classical
  let I : ℕ → Set ℝ := fun i => Ioo (K.physicalLeft i) (K.physicalRight i)
  have hdisjoint := n05_physicalPieces_pairwise_disjoint h04
  have hpacking (F : Finset ℕ) (hF : (F : Set ℕ) ⊆ Z) :
      (F.card : ℝ) * δ ≤ D.b - D.a := by
    have hsub : (⋃ i ∈ F, I i) ⊆ Ioo D.a D.b := by
      intro r hr
      obtain ⟨i, _, hri⟩ := mem_iUnion₂.mp hr
      exact (h04.1.referenceBounds i).2.2 hri
    have hvolume : volume.real (⋃ i ∈ F, I i) = ∑ i ∈ F, volume.real (I i) :=
      measureReal_biUnion_finset
        (fun i _ j _ hij => hdisjoint hij)
        (fun _ _ => measurableSet_Ioo)
        (fun _ _ => by
          dsimp only [I]
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)
    have hlocal (i : ℕ) (hi : i ∈ F) : δ ≤ volume.real (I i) := by
      dsimp only [I]
      rw [Real.volume_real_Ioo_of_le (h04.1.referenceBounds i).1.le]
      exact hwidth i (hF hi)
    have hab : D.a ≤ D.b := by
      have hi := h04.1.referenceBounds 0
      have hm : (K.physicalLeft 0 + K.physicalRight 0) / 2 ∈
          Ioo (K.physicalLeft 0) (K.physicalRight 0) := by
        constructor <;> linarith only [hi.1]
      exact ((hi.2.2 hm).1.trans (hi.2.2 hm).2).le
    calc
      (F.card : ℝ) * δ = ∑ i ∈ F, δ := by simp
      _ ≤ ∑ i ∈ F, volume.real (I i) := Finset.sum_le_sum hlocal
      _ = volume.real (⋃ i ∈ F, I i) := hvolume.symm
      _ ≤ volume.real (Ioo D.a D.b) :=
        measureReal_mono hsub (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)
      _ = D.b - D.a := Real.volume_real_Ioo_of_le hab
  have hfinite : Z.Finite := by
    by_contra hinf
    obtain ⟨N, hN⟩ := exists_nat_gt ((D.b - D.a) / δ)
    obtain ⟨F, hF, hcard⟩ := (show Z.Infinite from hinf).exists_subset_card_eq N
    have hb := hpacking F hF
    rw [hcard] at hb
    exact (not_le_of_gt hN) ((le_div_iff₀ hδ).mpr hb)
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hpacking hfinite.toFinset (fun i hi => hfinite.mem_toFinset.mp hi)

/-- A discrete coefficient bound for the inverse physical length gives
finite fibers and a coefficient bound for their cardinalities. -/
theorem n05_referencePieceIndex_count_of_inverse_width
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {B A : ℝ} (hB : 0 < B) (hA : 0 ≤ A)
    (hwidth : ∀ m, (K.physicalRight m - K.physicalLeft m)⁻¹ ≤
      B * radialE (D.cellIndex (K.cell m)) ^ A) :
    ∃ P : ℝ, 0 < P ∧ ∀ n : ℕ,
      {m | D.cellIndex (K.cell m) = n}.Finite ∧
        ({m | D.cellIndex (K.cell m) = n}.ncard : ℝ) ≤ P * radialE n ^ P := by
  let Q : ℝ := (D.b - D.a) * B
  let P : ℝ := max A Q + 1
  have hAP : A ≤ P := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hQP : Q ≤ P := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hP : 0 < P := by dsimp only [P]; linarith only [le_max_left A Q, hA]
  refine ⟨P, hP, fun n => ?_⟩
  let Z : Set ℕ := {m | D.cellIndex (K.cell m) = n}
  have hE : 0 < radialE n := Real.exp_pos _
  have hE1 : 1 ≤ radialE n := Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg n)
  have hden : 0 < B * radialE n ^ A := mul_pos hB (Real.rpow_pos_of_pos hE A)
  have hlower (m : ℕ) (hm : m ∈ Z) :
      (B * radialE n ^ A)⁻¹ ≤ K.physicalRight m - K.physicalLeft m := by
    have hwpos : 0 < K.physicalRight m - K.physicalLeft m :=
      sub_pos.mpr (h04.1.referenceBounds m).1
    have hw := hwidth m
    change D.cellIndex (K.cell m) = n at hm
    rw [hm] at hw
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hwpos) hw
  obtain ⟨hfinite, hpacking⟩ := n05_reference_piece_finite_packing h04
    (Z := Z) (inv_pos.mpr hden) hlower
  refine ⟨hfinite, ?_⟩
  have hcard : (Z.ncard : ℝ) ≤ Q * radialE n ^ A := by
    calc
      (Z.ncard : ℝ) = ((Z.ncard : ℝ) * (B * radialE n ^ A)⁻¹) *
          (B * radialE n ^ A) := by
        rw [mul_assoc, inv_mul_cancel₀ hden.ne', mul_one]
      _ ≤ (D.b - D.a) * (B * radialE n ^ A) :=
        mul_le_mul_of_nonneg_right hpacking hden.le
      _ = Q * radialE n ^ A := by dsimp only [Q]; ring
  exact hcard.trans (mul_le_mul hQP (Real.rpow_le_rpow_of_exponent_le hE1 hAP)
    (Real.rpow_nonneg hE.le A) hP.le)

end ContinuousFlexibility.Statements
