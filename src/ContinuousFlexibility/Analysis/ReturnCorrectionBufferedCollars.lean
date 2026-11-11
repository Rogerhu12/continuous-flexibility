import ContinuousFlexibility.Analysis.ReturnCorrectionSpeedGap

/-!
# A common positive collar around the actual cutoff transition

The cutoff uses half the width of the already proved positive optical
collar. Its whole closed derivative support is therefore strictly
inside the same positive open strip. The corrected speed gap is proved
again for this cutoff after a common shrinking of the parameter
neighborhood; all flow identities and derivative estimates use it.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem N01Properties.exists_positive_opticalCorrectionCollars_buffered
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ, ∃ j : ℕ → ℕ,
      ∃ x δ : ℕ → ℝ, ∃ K A B lam P : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      0 < K ∧ 0 < A ∧ 0 < B ∧ 0 < lam ∧ 0 < P ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m) ∧
        0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
        (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A ∧
        ∀ r ∈ Icc (x m - δ m) (x m + δ m),
          radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
      (∀ m, χ m = returnOpticalCutoff (x m) (δ m / 2)) ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Icc (x m - δ m / 2) (x m + δ m / 2)) ∧
      (∀ m, tsupport (deriv (χ m)) ⊆ Ioo (x m - δ m) (x m + δ m)) ∧
      (∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
        |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n)) ∧
      ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
        p.1 ∈ Icc (x m - δ m) (x m + δ m) →
        let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
        0 < d ∧
        d ≤ (originalCoefficients D S C z).a p ∧
        d ≤ -(originalCoefficients D S C z).c p ∧
        d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  obtain ⟨b₀, ε₀, χ₀, j, x, δ, K, A, B, lam, P, hb₀, hε₀, hε₀ε,
    hK, hA, hB, hlam, hP, hnew, hdata, _, _, _, _, hpositive⟩ :=
    hN.exists_positive_opticalCorrectionCollars hT
  let χ : ℕ → ℝ → ℝ := fun m => returnOpticalCutoff (x m) (δ m / 2)
  have hδ (m : ℕ) : 0 < δ m := (hdata m).2.1
  have hhalf (m : ℕ) : 0 < δ m / 2 := half_pos (hδ m)
  have hsupp (m : ℕ) :
      tsupport (deriv (χ m)) ⊆ Icc (x m - δ m / 2) (x m + δ m / 2) :=
    closure_minimal (returnOpticalCutoff_deriv_support_subset (x m) (hhalf m)) isClosed_Icc
  have hbuffer (m : ℕ) :
      Icc (x m - δ m / 2) (x m + δ m / 2) ⊆ Ioo (x m - δ m) (x m + δ m) := by
    intro r hr
    constructor <;> linarith only [hr.1, hr.2, hδ m]
  have hwidth (m : ℕ) : (δ m / 2)⁻¹ ≤ (2 * K) * radialE (D.cellIndex (j m)) ^ A := by
    have heq : (δ m / 2)⁻¹ = 2 * (δ m)⁻¹ := by
      field_simp [(hδ m).ne']
      <;> ring
    have hb := mul_le_mul_of_nonneg_left (hdata m).2.2.2.2.1 (by norm_num : (0 : ℝ) ≤ 2)
    exact heq.trans_le (hb.trans_eq (mul_assoc _ _ _).symm)
  have hjets : ∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
      |iteratedDeriv n (χ m) r| ≤ Kₙ * radialE (D.cellIndex (j m)) ^ (A * n) := by
    intro n
    obtain ⟨Kₙ, hKₙ, hjet⟩ := returnOpticalCutoff_iteratedDeriv_bound n
    refine ⟨Kₙ * (2 * K) ^ n, mul_pos hKₙ (pow_pos (mul_pos (by norm_num) hK) n),
      fun m r => ?_⟩
    have hpow := pow_le_pow_left₀ (inv_nonneg.mpr (hhalf m).le) (hwidth m) n
    calc
      _ ≤ Kₙ * ((δ m / 2)⁻¹) ^ n := hjet (x m) (δ m / 2) (hhalf m) r
      _ ≤ Kₙ * ((2 * K) * radialE (D.cellIndex (j m)) ^ A) ^ n :=
        mul_le_mul_of_nonneg_left hpow hKₙ.le
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Real.exp_pos _).le]
        ring
  refine ⟨b₀, ε₀, χ, j, x, δ, K, A, B, lam, P, hb₀, hε₀, hε₀ε,
    hK, hA, hB, hlam, hP, hnew, hdata, fun _ => rfl, ?_, ?_,
    fun m => (hsupp m).trans (hbuffer m), hjets, hpositive⟩
  · intro m
    exact ⟨returnOpticalCutoff_contDiff _ _, returnOpticalCutoff_mem_Icc _ _⟩
  · intro m
    have hl : C.left m < x m - δ m / 2 := by
      linarith only [(hdata m).2.2.1, hδ m]
    have hr : x m + δ m / 2 < C.right m := by
      linarith only [(hdata m).2.2.2.1, hδ m]
    exact ⟨returnOpticalCutoff_eventually_zero (hhalf m) hl,
      returnOpticalCutoff_eventually_one (hhalf m) hr, hsupp m⟩

private theorem exists_gap_neighborhood_for_positive_cutoff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hε : 0 < ε)
    (χ : ℕ → ℝ → ℝ) (j : ℕ → ℕ) {J A lam P : ℝ}
    (hJ : 0 < J) (hA : 0 ≤ A) (hlam : 0 < lam) (hP : 0 ≤ P)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hcutoff : ∀ m r, |deriv (χ m) r| ≤ J * radialE (D.cellIndex (j m)) ^ A)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
      p.1 ∈ tsupport (deriv (χ m)) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      0 < d ∧ d ≤ (originalCoefficients D S C z).a p ∧
      d ≤ -(originalCoefficients D S C z).c p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ,
        (deriv (χ m) r ≠ 0 →
          0 < (-returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
            returnCorrectedMinusSpeed D S C χ z m (r, θ)) / 2) ∧
        returnCorrectedMinusSpeed D S C χ z m (r, θ) ≤
          -returnCorrectedMinusSpeed D S C χ z m (r, -θ) := by
  obtain ⟨V, K, hV, hK, herror⟩ := hN.returnCorrectedMinusSpeed_error_radial_small
    hS hT χ j hJ hA hP hcell hcutoff
  obtain ⟨U, hU, hupper⟩ := hN.originalRadialCoefficient_uniform_upper
  let base' := max base (1 + loss)
  let ε' := min ε (min (1 / 2) (min K⁻¹ (lam / (4 * U * V))))
  have hε' : 0 < ε' := lt_min hε
    (lt_min (by norm_num) (lt_min (inv_pos.mpr hK) (div_pos hlam (by positivity))))
  have hε'₀ : ε' ≤ ε := min_le_left _ _
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
  have hb : base ≤ base' := le_max_left _ _
  have hh : 1 + loss ≤ base' := le_max_right _ _
  have hnew := hN.restrict_neighborhood hT hb hε' hε'₀
  refine ⟨base', ε', hb, hε', hε'₀, hnew, ?_⟩
  intro z hz hsector m r hr θ
  have hz₀ := stateNeighborhood_mono S C hb hε'₀ hz
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
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
      div_nonneg (Real.sqrt_nonneg _) (hN.originalRadialCoefficient_pos hz₀ hsector hp).le
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


/-- The actual half-width cutoff has the full corrected-flow conclusions,
with its transition contained in the common wider positive collar. -/
theorem N01Properties.exists_opticalCorrection_flow_buffered
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
        (∀ m, χ m = returnOpticalCutoff (x m) (δ m / 2)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Icc (x m - δ m / 2) (x m + δ m / 2)) ∧
        (∀ m, tsupport (deriv (χ m)) ⊆ Ioo (x m - δ m) (x m + δ m)) ∧
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
  obtain ⟨b₀, ε₀, χ, j, x, δ, K₀, A, B, lam, P, hbase₀, hε₀, hε₀ε,
    hK₀, hA, hB, hlam, hP, hN₀, hcollardata, hχeq, hχ, hend₀, hbuffer,
    hjets, hclosedpos⟩ := hN.exists_positive_opticalCorrectionCollars_buffered hT
  have hcell (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ D.cells (j m) :=
    (hcollardata m).1
  have hend (m : ℕ) : χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
      tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m) := by
    refine ⟨(hend₀ m).1, (hend₀ m).2.1, fun r hr => ?_⟩
    have hc := hbuffer m hr
    exact ⟨(hcollardata m).2.2.1.trans hc.1,
      hc.2.trans (hcollardata m).2.2.2.1⟩
  have hpositive (z) (hz : z ∈ stateNeighborhood S C b₀ ε₀) (m) (p : PolarPoint)
      (hp : p.1 ∈ tsupport (deriv (χ m))) :=
    hclosedpos z hz m p ⟨(hbuffer m hp).1.le, (hbuffer m hp).2.le⟩
  obtain ⟨J, hJ, hjet⟩ := hjets 1
  have hcutoff (m : ℕ) (r : ℝ) :
      |deriv (χ m) r| ≤ J * radialE (D.cellIndex (j m)) ^ A := by
    simpa only [iteratedDeriv_one, Nat.cast_one, mul_one] using hjet m r
  obtain ⟨base', ε', hb, hε', hε'₀, hnew, hgap⟩ :=
    exists_gap_neighborhood_for_positive_cutoff hN₀ hS hT hε₀ χ j hJ hA.le hlam hP.le
      hcell hcutoff hpositive
  have hdisc : ∀ z ∈ stateNeighborhood S C base' ε', ∀ m p,
      p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
    fun z hz m p hp =>
      (hpositive z (stateNeighborhood_mono S C hb hε'₀ hz) m p hp).2.2.2.2
  refine ⟨base', ε', χ, hbase₀.trans hb, hε', hε'₀.trans hε₀ε,
    hnew, hχ, hend, ?_, hdisc, ?_⟩
  · exact ⟨j, x, δ, K₀, A, B, lam, P, hK₀, hA, hB, hlam, hP,
      hcollardata, hχeq, fun m => (hend₀ m).2.2, hbuffer, hjets,
      fun z hz m p hp => hclosedpos z (stateNeighborhood_mono S C hb hε'₀ hz) m p hp⟩
  · intro z hz hsector m θ
    exact hnew.returnCorrectedFlow_properties_of_physical hS hT hz hsector χ m
      (hχ m).1 (fun r _ => (hχ m).2 r) (hend m).1.eq_of_nhds (hend m).2.1.eq_of_nhds
      (fun r hr t => (hgap z hz hsector m r hr t).2) θ

end ContinuousFlexibility.Statements
