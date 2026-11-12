import ContinuousFlexibility.Analysis.N05NegativePieceLabels
import ContinuousFlexibility.Analysis.N05PhysicalPieces
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Real

/-!
# Counting actual negative pieces at each physical cell index

The return margin and the upper optical coefficient bound force a lower
physical length for each actual cut half. Actual point labels transfer
that bound to the assigned cell. Pairwise disjointness then gives finite
packing in the radial core. No optical root-distance lower bound or chart
coefficient estimate is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Radial
open scoped BigOperators ContDiff

private theorem n05_cut_half_width_of_physical_envelope
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {Λ : ℝ} (hΛ : 1 ≤ Λ) (htravel : 1 / Λ ≤ C.travel m)
    (hF : ∀ r ∈ Icc (C.left m) (C.right m), |(-deriv D.w r / (r * D.w r))| ≤ Λ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    (2 * Λ ^ 2)⁻¹ ≤ K.physicalRight i - K.physicalLeft i := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have h04 := h.2.2.2.2
  have hwidth : K.physicalLeft i < K.physicalRight i := (h04.2.2.2.1 i).1
  have hcore := n05_cut_physical_closed_subset_core h.1.1.1.2.2.2.1 h.2.2.2.2 m right
  have hsub := n05_cut_physical_closed_subset_component h.2.2.2.2 m right
  have hint : IntervalIntegrable (opticalSpeed D.w) volume (K.physicalLeft i) (K.physicalRight i) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hwidth.le]
    exact (n05_opticalSpeed_continuousOn_core hD.1).mono hcore
  have hspeed (r : ℝ) (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      opticalSpeed D.w r ≤ Λ := by
    change Real.sqrt (-deriv D.w r / (r * D.w r)) ≤ Λ
    apply (Real.sqrt_le_left hΛp.le).mpr
    have hf := (le_abs_self (-deriv D.w r / (r * D.w r))).trans (hF r (hsub hr))
    have hsq : Λ ≤ Λ ^ 2 := by nlinarith only [mul_nonneg hΛp.le (sub_nonneg.mpr hΛ)]
    exact hf.trans hsq
  have hintegral : opticalTravel D.w (K.physicalLeft i) (K.physicalRight i) ≤
      Λ * (K.physicalRight i - K.physicalLeft i) := by
    calc
      opticalTravel D.w (K.physicalLeft i) (K.physicalRight i) ≤
          ∫ _ in K.physicalLeft i..K.physicalRight i, Λ :=
        intervalIntegral.integral_mono_on hwidth.le hint intervalIntegrable_const hspeed
      _ = Λ * (K.physicalRight i - K.physicalLeft i) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  have hhalf : opticalTravel D.w (K.physicalLeft i) (K.physicalRight i) =
      n05TricomiTime (K.cutRadius m) := n05_cut_halfTravel_eq_time hT hS h m right
  have htotal : C.travel m = 2 * n05TricomiTime (K.cutRadius m) :=
    n05_cut_totalTravel_eq_time hT hS h m
  rw [hhalf] at hintegral
  rw [htotal] at htravel
  have hbound : 1 / Λ ≤ 2 * (Λ * (K.physicalRight i - K.physicalLeft i)) := by
    linarith only [htravel, hintegral]
  have hmul := mul_le_mul_of_nonneg_left hbound hΛp.le
  have hcancel : Λ * (1 / Λ) = 1 := by field_simp [hΛp.ne']
  rw [hcancel] at hmul
  rw [← one_div (2 * Λ ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Λ ^ 2)).mpr
  nlinarith only [hmul]

/-- Every actual negative half has a quantitative positive width at its
assigned cell index. The constants are independent of the half and index. -/
theorem n05_negativePiece_width_at_selected_cell
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hlabels : N05NegativePieceCellLabels D S K) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ i : ℕ, K.positive i = false →
      (B * radialE (D.cellIndex (K.cell i)) ^ A)⁻¹ ≤
        K.physicalRight i - K.physicalLeft i := by
  obtain ⟨B₀, A₀, hB₀, hA₀, henv⟩ :=
    n05_negative_component_physical_envelope hD h.1.1.1.2.2.2.1
  obtain ⟨window, _, hsame⟩ := n05_referenceCell_indices_at_same_radius hT
  obtain ⟨P, hP, hshift⟩ := n05_radialE_power_index_window A₀ window hA₀.le
  refine ⟨2 * (B₀ * P) ^ 2, 2 * P, by positivity, by positivity, fun i hi => ?_⟩
  have hhalf : ∃ m : ℕ, ∃ right : Bool,
      i = if right then (K.cutPair m).2 else (K.cutPair m).1 := by
    obtain ⟨m, hm⟩ := n05_negative_piece_is_cut_half h.1.1.1.2.2.2.1 h.2.2.2.2 hi
    rcases hm with hm | hm
    · exact ⟨m, false, hm⟩
    · exact ⟨m, true, hm⟩
  obtain ⟨m, right, rfl⟩ := hhalf
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨j, hcarrier, hΛ, _, htravel, hF, _⟩ := henv m
  let Λ := B₀ * radialE (D.cellIndex j) ^ A₀
  let E := radialE (D.cellIndex (K.cell i))
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hEp : 0 < E := Real.exp_pos _
  obtain ⟨r₀, hr₀, hr₀cell⟩ := hlabels i hi
  have hsub := n05_cut_physical_open_subset_component h.2.2.2.2 m right
  have hindex : |(D.cellIndex j : ℝ) - (D.cellIndex (K.cell i) : ℝ)| ≤ window :=
    hsame j (K.cell i) r₀ (hcarrier (hsub hr₀)) hr₀cell
  have hΛbound : Λ ≤ (B₀ * P) * E ^ P := by
    calc
      Λ ≤ B₀ * (P * E ^ P) :=
        mul_le_mul_of_nonneg_left (hshift (D.cellIndex j) (D.cellIndex (K.cell i)) hindex) hB₀.le
      _ = (B₀ * P) * E ^ P := (mul_assoc _ _ _).symm
  have hwidth := n05_cut_half_width_of_physical_envelope hD hT hS h m right hΛ htravel
    (fun r hr => (hF r hr).1)
  have hpow : (E ^ P) ^ 2 = E ^ (2 * P) := by
    rw [pow_two, ← Real.rpow_add hEp]
    congr 1
    ring
  have hden : 2 * Λ ^ 2 ≤ (2 * (B₀ * P) ^ 2) * E ^ (2 * P) := by
    calc
      2 * Λ ^ 2 ≤ 2 * ((B₀ * P) * E ^ P) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΛp.le hΛbound 2) (by norm_num)
      _ = (2 * (B₀ * P) ^ 2) * E ^ (2 * P) := by rw [mul_pow, hpow]; ring
  exact (inv_anti₀ (by positivity : 0 < 2 * Λ ^ 2) hden).trans hwidth

private theorem n05_physical_piece_finite_packing
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
      exact (h04.2.2.2.1 i).2.2 hri
    have hvolume : volume.real (⋃ i ∈ F, I i) = ∑ i ∈ F, volume.real (I i) :=
      measureReal_biUnion_finset
        (fun i _ j _ hij => hdisjoint hij)
        (fun _ _ => measurableSet_Ioo)
        (fun _ _ => by simp only [I, Real.volume_Ioo, ENNReal.ofReal_ne_top, not_false_eq_true])
    have hlocal (i : ℕ) (hi : i ∈ F) : δ ≤ volume.real (I i) := by
      dsimp only [I]
      rw [Real.volume_real_Ioo_of_le (h04.2.2.2.1 i).1.le]
      exact hwidth i (hF hi)
    have hab : D.a ≤ D.b := by
      have hi := h04.2.2.2.1 0
      have hm : (K.physicalLeft 0 + K.physicalRight 0) / 2 ∈
          Ioo (K.physicalLeft 0) (K.physicalRight 0) := by
        constructor <;> linarith only [hi.1]
      exact ((hi.2.2 hm).1.trans (hi.2.2 hm).2).le
    calc
      (F.card : ℝ) * δ = ∑ i ∈ F, δ := by simp
      _ ≤ ∑ i ∈ F, volume.real (I i) := Finset.sum_le_sum hlocal
      _ = volume.real (⋃ i ∈ F, I i) := hvolume.symm
      _ ≤ volume.real (Ioo D.a D.b) :=
        measureReal_mono hsub (by simp only [Real.volume_Ioo, ENNReal.ofReal_ne_top, not_false_eq_true])
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

/-- Actual negative pieces at any fixed assigned cell index form a finite
set with one uniform coefficient-power cardinality bound. -/
theorem n05_negativePieceIndex_count
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hlabels : N05NegativePieceCellLabels D S K) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      {i | K.positive i = false ∧ D.cellIndex (K.cell i) = n}.Finite ∧
        ({i | K.positive i = false ∧ D.cellIndex (K.cell i) = n}.ncard : ℝ) ≤
          B * radialE n ^ B := by
  obtain ⟨C₀, A, hC₀, hA, hwidth⟩ := n05_negativePiece_width_at_selected_cell hD hT hS h hlabels
  let P : ℝ := (D.b - D.a) * C₀
  let B : ℝ := max A P + 1
  have hAB : A ≤ B := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hPB : P ≤ B := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hB : 0 < B := hA.trans_le hAB
  refine ⟨B, hB, fun n => ?_⟩
  let Z : Set ℕ := {i | K.positive i = false ∧ D.cellIndex (K.cell i) = n}
  have hE : 0 < radialE n := Real.exp_pos _
  have hE1 : 1 ≤ radialE n := Real.one_le_exp_iff.mpr (radialQ_nonneg n)
  have hc : 0 < C₀ * radialE n ^ A := mul_pos hC₀ (Real.rpow_pos_of_pos hE A)
  obtain ⟨hfinite, hpacking⟩ := n05_physical_piece_finite_packing h.2.2.2.2
    (Z := Z) (inv_pos.mpr hc) (fun i hi => by
      have hw := hwidth i hi.1
      simpa only [hi.2] using hw)
  refine ⟨hfinite, ?_⟩
  have hcard : (Z.ncard : ℝ) ≤ P * radialE n ^ A := by
    calc
      (Z.ncard : ℝ) = ((Z.ncard : ℝ) * (C₀ * radialE n ^ A)⁻¹) *
          (C₀ * radialE n ^ A) := by
        rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
      _ ≤ (D.b - D.a) * (C₀ * radialE n ^ A) :=
        mul_le_mul_of_nonneg_right hpacking hc.le
      _ = P * radialE n ^ A := by dsimp only [P]; ring
  exact hcard.trans (mul_le_mul hPB (Real.rpow_le_rpow_of_exponent_le hE1 hAB)
    (Real.rpow_nonneg hE.le A) hB.le)

end ContinuousFlexibility.Statements
