import ContinuousFlexibility.Analysis.ReturnCorrectionVelocityBounds
import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity
import ContinuousFlexibility.Analysis.MaterialSampleShift
import ContinuousFlexibility.Analysis.N01ControlIndexBound
import ContinuousFlexibility.Analysis.N01FlowJointRegularity

/-!
# A single neighborhood preserves the actual corrected speed gap

The actual control sample differs by a bounded index shift from its
label. The containing-cell index bound then allows the material height
decay to absorb every radial power in the cutoff and gap estimates.
The correction velocity is consequently smaller than half the original
half-gap on every transition support after one common shrinking of the
N01 neighborhood.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem N01Properties.controlSample_radial_envelope
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) :
    ∃ K : ℝ, 0 < K ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B +
        T.H (T.sample m) ^ (3 / 4 : ℝ)) * radialE (D.cellIndex j) ^ P ≤ K := by
  obtain ⟨L, hL, hindex⟩ := hN.2.2.2.2.1
  obtain ⟨CH, A, hCH, hA, hshift⟩ :=
    materialSample_H_E0_rpow_of_index_sub_bound hT hN.1.1 (3 / 4 : ℝ) hB hL.le
  obtain ⟨I, hI, hactual⟩ := hN.control_actual_cell_index_bound hS hT
  obtain ⟨CR, hCR, hradial⟩ :=
    materialSample_radialE_rpow_le_M_of_index_bound hT hN.1.1 hI hP
  have hT' := hT
  rcases hT' with ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _, _, _, _, _, _⟩
  obtain ⟨CE, hCE, he⟩ := hE A
  obtain ⟨CM, hCM, hm⟩ := materialSample_H_M_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) (2 : ℝ)
  let K := (CH * CE + 1) * CR * CM
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun m j hj => ?_⟩
  obtain ⟨_, hRef⟩ := hN.1.1
  have hs := materialSample_mem_radialCore hT hRef.2.1 m
  have hH : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    (Real.rpow_pos_of_pos (hT.2.1 _ hs).2.1 _).le
  have hM : 1 ≤ T.M (T.sample m) := (hT.2.1 _ hs).2.2.2
  have he' := he _ hs
  have hshift' := hshift (C.cell m) m (hindex m)
  have hf : T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B ≤
        (CH * CE) * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.M (T.sample m) := by
    have h := hshift'.trans (mul_le_mul_of_nonneg_left he' (mul_nonneg hCH.le hH))
    exact h.trans_eq (by ring)
  have hg : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤
      T.H (T.sample m) ^ (3 / 4 : ℝ) * T.M (T.sample m) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hM hH
  have hsum : T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B + T.H (T.sample m) ^ (3 / 4 : ℝ) ≤
      (CH * CE + 1) * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.M (T.sample m) :=
    (add_le_add hf hg).trans_eq (by ring)
  have hr := hradial m (D.cellIndex j) (hactual m j hj)
  have hprod := mul_le_mul hsum hr (Real.rpow_nonneg (Real.exp_pos _).le _)
    (mul_nonneg (mul_nonneg (by positivity) hH) (zero_le_one.trans hM))
  calc
    _ ≤ ((CH * CE + 1) * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.M (T.sample m)) *
        (CR * T.M (T.sample m)) := hprod
    _ = ((CH * CE + 1) * CR) *
        (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.M (T.sample m) ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      ring
    _ ≤ ((CH * CE + 1) * CR) * CM := by
      exact mul_le_mul_of_nonneg_left (hm m) (mul_nonneg (by positivity) hCR.le)

theorem N01Properties.returnCorrectedMinusSpeed_error_radial_small
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ) (j : ℕ → ℕ) {J A P : ℝ}
    (hJ : 0 < J) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hcutoff : ∀ m r, |deriv (χ m) r| ≤ J * radialE (D.cellIndex (j m)) ^ A) :
    ∃ V K : ℝ, 0 < V ∧ 0 < K ∧
      ∀ base' : ℕ, base ≤ base' → 1 + loss ≤ base' →
      ∀ η : ℝ, 0 ≤ η → η ≤ ε → η ≤ 1 / 2 → K * η ≤ 1 →
      ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
      ∀ m p, p.1 ∈ Icc (C.left m) (C.right m) →
      |returnCorrectedMinusSpeed D S C χ z m p -
        minusCharacteristicSpeed (originalCoefficients D S C z) p| ≤
        V * η * radialE (D.cellIndex (j m)) ^ (-P) := by
  obtain ⟨B, K, hB, hK, hvelocity⟩ := hN.returnCorrectedMinusSpeed_error_weighted hS hT
  obtain ⟨W, hW, henv⟩ := hN.controlSample_radial_envelope hS hT hB.le (add_nonneg hA hP)
  let N := max (6 * B) (2 * circleSobolevConstant)
  have hNpos : 0 < N := (mul_pos (by norm_num) hB).trans_le (le_max_left _ _)
  let V := 4 * J * N * W
  have hV : 0 < V := by dsimp only [V]; positivity
  refine ⟨V, K, hV, hK,
    fun base' hbase hhigh η hη hηε hη₁ hηK z hz hsector m p hp => ?_⟩
  let F := T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B
  let G := T.H (T.sample m) ^ (3 / 4 : ℝ)
  let E := radialE (D.cellIndex (j m))
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨_, hRef⟩ := hN.1.1
  have hpos (i : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hRef.2.1 i)
  have hF : 0 ≤ F := mul_nonneg
    (Real.rpow_nonneg (hpos (C.cell m)).2.1.le _)
    (Real.rpow_nonneg (hpos (C.cell m)).2.2.1.le _)
  have hG : 0 ≤ G := Real.rpow_nonneg (hpos m).2.1.le _
  have hweighted : 6 * B * F * η + (2 * circleSobolevConstant * η) * G ≤
      N * η * (F + G) := by
    have hf := mul_le_mul_of_nonneg_right (le_max_left (6 * B) (2 * circleSobolevConstant)) hF
    have hg := mul_le_mul_of_nonneg_right (le_max_right (6 * B) (2 * circleSobolevConstant)) hG
    have h := mul_le_mul_of_nonneg_right (add_le_add hf hg) hη
    convert h using 1 <;> ring
  have hwzero : 0 ≤ 6 * B * F * η + (2 * circleSobolevConstant * η) * G := by
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB.le) hF) hη)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hη) hG)
  have hv := hvelocity base' hbase hhigh η hη hηε hη₁ hηK z hz hsector χ m p hp
  have hvw : |returnCorrectedMinusSpeed D S C χ z m p -
      minusCharacteristicSpeed (originalCoefficients D S C z) p| ≤
      4 * |deriv (χ m) p.1| *
        (6 * B * F * η + (2 * circleSobolevConstant * η) * G) := by
    convert hv using 1 <;> dsimp only [F, G] <;> ring
  have hv' : |returnCorrectedMinusSpeed D S C χ z m p -
      minusCharacteristicSpeed (originalCoefficients D S C z) p| ≤
      (4 * J * N * η) * ((F + G) * E ^ A) := by
    have hmul := mul_le_mul
      (mul_le_mul_of_nonneg_left (hcutoff m p.1) (by norm_num : (0 : ℝ) ≤ 4))
      hweighted hwzero (mul_nonneg (by norm_num)
        (mul_nonneg hJ.le (Real.rpow_nonneg hE.le _)))
    refine hvw.trans (hmul.trans_eq ?_)
    dsimp only [F, G, E]
    ring
  have hs := mul_le_mul_of_nonneg_right hv' (Real.rpow_nonneg hE.le P)
  have henv' : (F + G) * E ^ (A + P) ≤ W := henv m (j m) (hcell m)
  have hscaled : |returnCorrectedMinusSpeed D S C χ z m p -
      minusCharacteristicSpeed (originalCoefficients D S C z) p| * E ^ P ≤ V * η := by
    calc
      _ ≤ (4 * J * N * η) * ((F + G) * E ^ (A + P)) := by
        rw [Real.rpow_add hE]
        convert hs using 1 <;> ring
      _ ≤ (4 * J * N * η) * W := mul_le_mul_of_nonneg_left henv' (by positivity)
      _ = V * η := by dsimp only [V]; ring
  rw [Real.rpow_neg hE.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hE _)).mpr hscaled


/-- The actual correction family has an ordered characteristic pair on
every component, and a strict positive gap wherever the patch is active,
on one common neighborhood derived from the original hypotheses. -/
theorem N01Properties.exists_opticalCorrection_characteristic_gap
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m)) ∧
      (∃ j : ℕ → ℕ, ∃ x δ : ℕ → ℝ, ∃ K A B lam P : ℝ,
        0 < K ∧ 0 < A ∧ 0 < B ∧ 0 < lam ∧ 0 < P ∧
        (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m) ∧
          0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
          (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A ∧
          ∀ r ∈ Icc (x m - δ m) (x m + δ m),
            radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
        (∀ m, χ m = returnOpticalCutoff (x m) (δ m)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m)) ∧
        (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
          |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n)) ∧
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
          p.1 ∈ Icc (x m - δ m) (x m + δ m) →
          let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
          0 < d ∧ d ≤ (originalCoefficients D S C z).a p ∧
          d ≤ -(originalCoefficients D S C z).c p ∧
          d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
          0 < (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ tsupport (deriv (χ m)) →
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ,
        (deriv (χ m) r ≠ 0 →
          0 < (-returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
            returnCorrectedMinusSpeed D S C χ z m (r, θ)) / 2) ∧
        returnCorrectedMinusSpeed D S C χ z m (r, θ) ≤
          -returnCorrectedMinusSpeed D S C χ z m (r, -θ) := by
  obtain ⟨b₀, ε₀, χ, j, x, δ, K₀, A, B, lam, P, hbase₀, hε₀, hε₀ε,
    hK₀, hA, hB, hlam, hP, hN₀, hcollardata, hχeq, hχ, hend₀, hjets, hclosedpos⟩ :=
    hN.exists_positive_opticalCorrectionCollars hT
  have hcell (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ D.cells (j m) :=
    (hcollardata m).1
  have hend (m : ℕ) : χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
      tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m) := by
    refine ⟨(hend₀ m).1, (hend₀ m).2.1, fun r hr => ?_⟩
    have hc := (hend₀ m).2.2 hr
    exact ⟨(hcollardata m).2.2.1.trans_le hc.1,
      hc.2.trans_lt (hcollardata m).2.2.2.1⟩
  have hpositive (z) (hz : z ∈ stateNeighborhood S C b₀ ε₀) (m) (p : PolarPoint)
      (hp : p.1 ∈ tsupport (deriv (χ m))) :=
    hclosedpos z hz m p ((hend₀ m).2.2 hp)
  obtain ⟨J, hJ, hjet⟩ := hjets 1
  have hcutoff (m : ℕ) (r : ℝ) :
      |deriv (χ m) r| ≤ J * radialE (D.cellIndex (j m)) ^ A := by
    simpa only [iteratedDeriv_one, Nat.cast_one, mul_one] using hjet m r
  obtain ⟨V, K, hV, hK, herror⟩ := hN₀.returnCorrectedMinusSpeed_error_radial_small
    hS hT χ j hJ hA.le hP.le hcell hcutoff
  obtain ⟨U, hU, hupper⟩ := hN₀.originalRadialCoefficient_uniform_upper
  let base' := max b₀ (1 + loss)
  let ε' := min ε₀ (min (1 / 2) (min K⁻¹ (lam / (4 * U * V))))
  have hε' : 0 < ε' := lt_min hε₀
    (lt_min (by norm_num) (lt_min (inv_pos.mpr hK) (div_pos hlam (by positivity))))
  have hε'₀ : ε' ≤ ε₀ := min_le_left _ _
  have hεhalf : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεK : K * ε' ≤ 1 := by
    have hεi : ε' ≤ K⁻¹ := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_le_mul_of_nonneg_left hεi hK.le).trans_eq (mul_inv_cancel₀ hK.ne')
  have hεV : V * ε' ≤ lam / (4 * U) := by
    have hεi : ε' ≤ lam / (4 * U * V) := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
    refine (mul_le_mul_of_nonneg_left hεi hV.le).trans_eq ?_
    field_simp [hU.ne', hV.ne']
    <;> ring
  have hb : b₀ ≤ base' := le_max_left _ _
  have hh : 1 + loss ≤ base' := le_max_right _ _
  have hnew := hN₀.restrict_neighborhood hT hb hε' hε'₀
  have hdisc : ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
      p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
    fun z hz m p hp =>
      (hpositive z (stateNeighborhood_mono S C hb hε'₀ hz) m p hp).2.2.2.2
  refine ⟨base', ε', χ, hbase₀.trans hb, hε', hε'₀.trans hε₀ε,
    hnew, hχ, hend, ?_, hdisc, ?_⟩
  · exact ⟨j, x, δ, K₀, A, B, lam, P, hK₀, hA, hB, hlam, hP,
      hcollardata, hχeq, fun m => (hend₀ m).2.2, hjets,
      fun z hz m p hp => hclosedpos z (stateNeighborhood_mono S C hb hε'₀ hz) m p hp⟩
  · intro z hz hsector m r hr θ
    have hz₀ := stateNeighborhood_mono S C hb hε'₀ hz
    have hC : controlGeometryConditions D S C := hN₀.2.2.2.1
    have hp : (r, θ) ∈ annularOpen D :=
      ⟨⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
    obtain ⟨ha, hbp, hc⟩ := originalCoefficients_parity_of_physical hS C z r θ
    have hreflection := minusCharacteristicSpeed_reflection (originalCoefficients D S C z)
      r θ ha hbp hc
    by_cases hχzero : deriv (χ m) r = 0
    · refine ⟨fun h => (h hχzero).elim, ?_⟩
      have hminus : returnCorrectedMinusSpeed D S C χ z m (r, θ) =
          minusCharacteristicSpeed (originalCoefficients D S C z) (r, θ) := by
        simp only [returnCorrectedMinusSpeed, hχzero, mul_zero, zero_mul, add_zero]
      have hminus' : returnCorrectedMinusSpeed D S C χ z m (r, -θ) =
          minusCharacteristicSpeed (originalCoefficients D S C z) (r, -θ) := by
        simp only [returnCorrectedMinusSpeed, hχzero, mul_zero, zero_mul, add_zero]
      rw [hminus, hminus', hreflection, neg_neg]
      have hhalf : 0 ≤ Real.sqrt ((originalCoefficients D S C z).b (r, θ) ^ 2 -
          (originalCoefficients D S C z).a (r, θ) * (originalCoefficients D S C z).c (r, θ)) /
          (originalCoefficients D S C z).a (r, θ) :=
        div_nonneg (Real.sqrt_nonneg _) (hN₀.originalRadialCoefficient_pos hz₀ hsector hp).le
      unfold minusCharacteristicSpeed plusCharacteristicSpeed
      linarith only [hhalf]
    · have hsupp : r ∈ tsupport (deriv (χ m)) := subset_tsupport _ hχzero
      have hquant := hpositive z hz₀ m (r, θ) hsupp
      have hapos : 0 < (originalCoefficients D S C z).a (r, θ) :=
        hquant.1.trans_le hquant.2.1
      have hgaplower := characteristic_halfGap_lower_of_discriminant hapos
        (hupper z hz₀ hsector (r, θ) hp) hquant.1.le hquant.2.2.2.1
      have hgap : 0 < Real.sqrt ((originalCoefficients D S C z).b (r, θ) ^ 2 -
          (originalCoefficients D S C z).a (r, θ) * (originalCoefficients D S C z).c (r, θ)) /
          (originalCoefficients D S C z).a (r, θ) :=
        div_pos (Real.sqrt_pos.mpr hquant.2.2.2.2) hapos
      have hsmall : V * ε' * radialE (D.cellIndex (j m)) ^ (-P) ≤
          (Real.sqrt ((originalCoefficients D S C z).b (r, θ) ^ 2 -
            (originalCoefficients D S C z).a (r, θ) *
              (originalCoefficients D S C z).c (r, θ)) /
            (originalCoefficients D S C z).a (r, θ)) / 2 := by
        calc
          _ ≤ (lam / (4 * U)) * radialE (D.cellIndex (j m)) ^ (-P) :=
            mul_le_mul_of_nonneg_right hεV (Real.rpow_nonneg (Real.exp_pos _).le _)
          _ = ((lam * radialE (D.cellIndex (j m)) ^ (-P) / 2) / U) / 2 := by
            field_simp [hU.ne']
            <;> ring
          _ ≤ _ := div_le_div_of_nonneg_right hgaplower (by norm_num)
      have herr (t : ℝ) :
          |returnCorrectedMinusSpeed D S C χ z m (r, t) -
            minusCharacteristicSpeed (originalCoefficients D S C z) (r, t)| ≤
            V * ε' * radialE (D.cellIndex (j m)) ^ (-P) :=
        herror base' hb hh ε' hε'.le hε'₀ hεhalf hεK z hz hsector m (r, t) ⟨hr.1.le, hr.2.le⟩
      have hstrict := returnCorrectedComponentSpeed_positive_of_error_bound
        D S C χ z m r θ hreflection hgap ((herr θ).trans hsmall) ((herr (-θ)).trans hsmall)
      refine ⟨fun _ => hstrict, ?_⟩
      linarith only [hstrict]

/-- All corrected-flow clauses requested in N03 hold for the actual
patched symmetric coefficients on a common neighborhood. -/
theorem N01Properties.exists_opticalCorrection_flow
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m)) ∧
      (∃ j : ℕ → ℕ, ∃ x δ : ℕ → ℝ, ∃ K A B lam P : ℝ,
        0 < K ∧ 0 < A ∧ 0 < B ∧ 0 < lam ∧ 0 < P ∧
        (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m) ∧
          0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
          (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A ∧
          ∀ r ∈ Icc (x m - δ m) (x m + δ m),
            radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
        (∀ m, χ m = returnOpticalCutoff (x m) (δ m)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m)) ∧
        (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
          |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n)) ∧
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
          p.1 ∈ Icc (x m - δ m) (x m + δ m) →
          let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
          0 < d ∧ d ≤ (originalCoefficients D S C z).a p ∧
          d ≤ -(originalCoefficients D S C z).c p ∧
          d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
          0 < (originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ tsupport (deriv (χ m)) →
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 → ∀ m θ,
        returnCorrectedMinusFlow S C χ z m (C.left m) θ = θ ∧
        ContinuousOn (fun r => returnCorrectedMinusFlow S C χ z m r θ)
          (Icc (C.left m) (C.right m)) ∧
        (∀ r ∈ Ioo (C.left m) (C.right m), HasDerivAt
          (fun s => returnCorrectedMinusFlow S C χ z m s θ)
          (minusCharacteristicSpeed (returnCorrectedCoefficients D S C χ z)
            (r, returnCorrectedMinusFlow S C χ z m r θ)) r) ∧
        rightChartCandidate S C z m (returnCorrectedMinusFlow S C χ z m (C.right m) θ) =
          stateLeftChart S z.1 m θ - C.travel m ∧
        rightChartCandidate S C z m (-returnCorrectedMinusFlow S C χ z m (C.right m) (-θ)) =
          stateLeftChart S z.1 m θ + C.travel m := by
  obtain ⟨base', ε', χ, hb, hε', hεε, hnew, hχ, hend, hcollars, hdisc, hgap⟩ :=
    hN.exists_opticalCorrection_characteristic_gap hS hT
  refine ⟨base', ε', χ, hb, hε', hεε, hnew, hχ, hend, hcollars, hdisc,
    fun z hz hsector m θ => ?_⟩
  exact hnew.returnCorrectedFlow_properties_of_physical hS hT hz hsector χ m
    (hχ m).1 (fun r _ => (hχ m).2 r) (hend m).1.eq_of_nhds (hend m).2.1.eq_of_nhds
    (fun r hr t => (hgap z hz hsector m r hr t).2) θ


end ContinuousFlexibility.Statements

