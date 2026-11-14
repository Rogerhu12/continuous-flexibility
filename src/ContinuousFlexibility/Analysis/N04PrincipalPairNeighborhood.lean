import ContinuousFlexibility.Analysis.N04PrincipalPairValue

/-!
# Inverting a paired family on one smaller sector neighborhood

The sampled material envelope makes the value difference small relative
to the reference denominator simultaneously on every selected piece.
The radius is chosen before the reciprocal tower orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

theorem N04PrincipalPairBounds.inverse_neighborhood
    {D : ReferenceData} {S : PhysicalSpacesData} {T : MaterialData}
    {ι : Type*} {cell : ι → ℕ} {base : ℕ} {ε : ℝ}
    {f : ι → Parameter S → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}
    (hf : N04PrincipalPairBounds (parameterGrading S)
      (fun m => T.E0 (T.sample (cell m)))
      (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
      (U := sectorNeighborhood S base ε ε) (Ω := unitStrip) f f₀)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hε : 0 < ε) (hI : HasInterpolation (parameterGrading S))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hzero : ∀ m, EqOn (f m 0) (f₀ m) unitStrip)
    (href : ∃ R : ℝ, 0 < R ∧ ∀ m q, q ∈ unitStrip →
      f₀ m q ≠ 0 ∧ |(f₀ m q)⁻¹| ≤ R * T.E0 (T.sample (cell m)) ^ R) :
    ∃ b : ℕ, base ≤ b ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      N04PrincipalPairBounds (parameterGrading S)
        (fun m => T.E0 (T.sample (cell m)))
        (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
        (U := sectorNeighborhood S b δ δ) (Ω := unitStrip)
        (fun m z q => (f m z q)⁻¹) (fun m q => (f₀ m q)⁻¹) := by
  have hH (m : ι) : 0 < T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1
  have hv := hf.value_neighborhood hε hE (fun m => (hH m).le) hzero
  let b : ℕ := hv.choose
  have hbase : base ≤ b := hv.choose_spec.1
  let C : ℝ := hv.choose_spec.2.choose
  have hC : 0 < C := hv.choose_spec.2.choose_spec.1
  have hvalue := hv.choose_spec.2.choose_spec.2
  let R : ℝ := href.choose
  have hR : 0 < R := href.choose_spec.1
  have henv := n07a_materialSample_envelope_bound hD hT
    (by norm_num : 0 < (3 / 4 : ℝ)) (C + R)
  let N : ℝ := henv.choose
  have hN : 0 < N := henv.choose_spec.1
  let Q : ℝ := C * R * N
  have hQ : 0 < Q := mul_pos (mul_pos hC hR) hN
  let d : ℝ := (4 * Q)⁻¹
  have hd : 0 < d := inv_pos.mpr (mul_pos (by norm_num) hQ)
  let δ : ℝ := min (min ε (1 / 2)) d
  have hδ : 0 < δ := lt_min (lt_min hε (by norm_num)) hd
  have hδold : δ ≤ min ε (1 / 2) := min_le_left _ _
  have hδε : δ ≤ ε := hδold.trans (min_le_left _ _)
  have hδhalf : δ ≤ 1 / 2 := hδold.trans (min_le_right _ _)
  have hδd : δ ≤ d := min_le_right _ _
  let B : ℝ := 2 * R + 1
  have hB : 0 < B := by dsimp only [B]; linarith
  have hRB : R ≤ B := by dsimp only [B]; linarith
  have h2RB : 2 * R ≤ B := by dsimp only [B]; linarith
  have hrelative : ∀ m z, z ∈ sectorNeighborhood S b δ δ → ∀ q ∈ unitStrip,
      f m z q ≠ 0 ∧ |(f m z q)⁻¹| ≤ B * T.E0 (T.sample (cell m)) ^ B := by
    intro m z hz q hq
    have hzold : z ∈ sectorNeighborhood S b (min ε (1 / 2)) (min ε (1 / 2)) :=
      sectorNeighborhood_mono S le_rfl hδold hδold hz
    have hp : parameterGrading S b z < 2 * δ := by
      rw [show parameterGrading S b z = sectorGrading S b z.1 + |z.2| from
        pairGrading_apply (E := StateDirections S) (F := ℝ)
          (sectorGrading S) realGrading b z]
      linarith only [hz.1, hz.2]
    have hsmall : parameterGrading S b z < (2 * Q)⁻¹ := by
      calc
        _ < 2 * δ := hp
        _ ≤ 2 * d := mul_le_mul_of_nonneg_left hδd (by norm_num)
        _ = (2 * Q)⁻¹ := by dsimp only [d]; field_simp [hQ.ne'] <;> ring
    have hepos : 0 < T.E0 (T.sample (cell m)) := zero_lt_one.trans_le (hE m)
    let M : ℝ := C * T.E0 (T.sample (cell m)) ^ C *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
    let r : ℝ := R * T.E0 (T.sample (cell m)) ^ R
    have hprod : M * r ≤ Q := by
      calc
        _ = C * R * (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (cell m)) ^ (C + R)) := by
          dsimp only [M, r]
          rw [Real.rpow_add hepos]
          ring
        _ ≤ C * R * N := mul_le_mul_of_nonneg_left (henv.choose_spec.2 (cell m))
          (mul_nonneg hC.le hR.le)
        _ = Q := rfl
    have herr : (M * parameterGrading S b z) * r < 1 / 2 := by
      calc
        _ = (M * r) * parameterGrading S b z := by ring
        _ ≤ Q * parameterGrading S b z :=
          mul_le_mul_of_nonneg_right hprod (apply_nonneg _ _)
        _ < Q * (2 * Q)⁻¹ := mul_lt_mul_of_pos_left hsmall hQ
        _ = 1 / 2 := by field_simp [hQ.ne'] <;> ring
    have hh := n04PrincipalNegative_inverse_of_relative_error
      (href.choose_spec.2 m q hq).1 (href.choose_spec.2 m q hq).2
      (hvalue z hzold m q hq) herr
    refine ⟨hh.2.1, hh.2.2.trans ?_⟩
    have hcoef : (2 * R) * T.E0 (T.sample (cell m)) ^ R ≤
        B * T.E0 (T.sample (cell m)) ^ B := mul_le_mul h2RB
      (Real.rpow_le_rpow_of_exponent_le (hE m) hRB)
      (Real.rpow_nonneg hepos.le _) hB.le
    simpa only [r, mul_assoc] using hcoef
  have hsub : sectorNeighborhood S b δ δ ⊆ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S hbase hδε hδε
  have hU := isOpen_sectorNeighborhood S b δ δ
  have hlocal := hf.restrict hU hsub
  refine ⟨b, hbase, δ, hδ, hδε, hδhalf, ?_⟩
  exact hlocal.inv (n07aParameterGrading_monotone S) hI hU
    (isOpen_Ioo.prod isOpen_univ) hE (fun m => Real.rpow_pos_of_pos (hH m) _)
    (fun m z hz q hq => (hrelative m z hz q hq).1)
    (fun m q hq => (href.choose_spec.2 m q hq).1)
    ⟨B, hB, fun m z hz q hq => (hrelative m z hz q hq).2⟩
    ⟨R, hR, fun m q hq => (href.choose_spec.2 m q hq).2⟩

end ContinuousFlexibility.Analysis
