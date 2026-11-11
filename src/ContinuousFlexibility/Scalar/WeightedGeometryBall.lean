import ContinuousFlexibility.Scalar.WeightedGeometryBounds

/-!
# A common scalar positivity ball from quantitative low-order jet bounds

The hypotheses here are intermediate estimates for the actual decoder. The
conclusion uses the original state seminorm ball, with a single radius for
every point of the annulus, including all angular variables.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarCommonHeightDecode_radialPartial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarCommonHeight S) (p : PolarPoint) :
    radialPartial (scalarCommonHeightDecode S u) p =
      radialPartial ((S.height scalarBeta).decode u.1) p + u.2 * deriv S.chiLeft p.1 := by
  have hu := (scalarHeight_decode_contDiff_and_flatJets hT hS u.1).1
  have hχ := hS.2.2.1.1
  have hχp := Radial.contDiff_radialHeightField hχ
  change radialPartial (heightFamily _ (Radial.radialHeightField S.chiLeft) u.2) p = _
  rw [radialPartial_heightFamily (hu.differentiable (by simp) p)
    (hχp.differentiable (by simp) p),
    Radial.radialPartial_radialHeightField (hχ.differentiable (by simp) p.1)]

theorem scalarCommonHeightDecode_heightAngular_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarCommonHeight S) :
    heightAngular (scalarCommonHeightDecode S u) = heightAngular ((S.height scalarBeta).decode u.1) := by
  have hu := (scalarHeight_decode_contDiff_and_flatJets hT hS u.1).1
  have hχ := hS.2.2.1.1
  have hχp := Radial.contDiff_radialHeightField hχ
  change heightAngular (heightFamily _ (Radial.radialHeightField S.chiLeft) u.2) = _
  rw [heightAngular_heightFamily (hu.differentiable (by simp)) (hχp.differentiable (by simp)),
    Radial.heightAngular_radialHeightField
      (fun r => (hχ.differentiable (by simp) r).hasDerivAt)]
  funext p
  simp only [heightFamily, mul_zero, add_zero]

/-- Exact physical positivity from reference-normalized common-height jets. -/
theorem scalarState_positivity_of_reference_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hp : p ∈ annularOpen D)
    {K A B C : ℝ}
    (hm : |angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (p.1, θ))| ≤ 1 / 2)
    (hE : 1 + scalarStateProfile D S x p.1 ^ 2 ≤ K)
    (hur : |radialPartial (scalarStateIncrement S x) p| ≤ A * D.w p.1)
    (hut : |heightAngular (scalarStateIncrement S x) p| ≤ B)
    (hutt : |angularPartial (heightAngular (scalarStateIncrement S x)) p| ≤ C * D.w p.1)
    (hqr : K * |x.2| * A ≤ 1 / 32) (hqt : K * |x.2| * B ≤ 1 / 4)
    (hqtt : K * |x.2| * C ≤ 1 / 32) :
    0 < scalarStateProfile D S x p.1 ∧
      (1 / 2 : ℝ) ≤ polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p ∧
      (7 / 8 : ℝ) * scalarStateProfile D S x p.1 ≤
        heightQ (profileEnergy (scalarStateProfile D S x) p)
          (heightRadial (scalarStateHeight D S x) p)
          (angularPartial (heightAngular (scalarStateHeight D S x)) p) := by
  have hprofile := scalarStateProfile_bounds_of_mean_small hD x hp.1 hm
  have hreference := hD.choose_spec
  have hw₀ := hreference.1.2.2.2.2.1 p.1 hp.1
  have hr : p.1 ≠ 0 := (lt_trans hreference.1.1 hp.1.1).ne'
  have hbounds := weighted_height_bounds_of_reference_jets hw₀ hprofile.2.1 hE
    hur hut hutt hqr hqt hqtt
  refine ⟨hprofile.1, ?_, ?_⟩
  · unfold polarDiscriminant
    rw [scalarStateHeight_heightRadial hD hT hS x p,
      scalarStateHeight_heightAngular hD hT hS x p]
    exact hbounds.1
  · rw [scalarStateHeight_heightRadial hD hT hS x p,
      scalarStateHeight_angularPartial_heightAngular hD hT hS x hr]
    exact hbounds.2

/-- One positive parameter controls a finite list of nonnegative constants,
with margins chosen independently of all future output derivative orders. -/
theorem exists_scalar_geometry_radius {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε * a ≤ 1 / 2 ∧ ε * b ≤ 1 / 32 ∧
      ε * c ≤ 1 / 4 ∧ ε * d ≤ 1 / 32 := by
  let L : ℝ := 1 + a + b + c + d
  have hLone : (1 : ℝ) ≤ L := by dsimp [L]; linarith only [ha, hb, hc, hd]
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  let ε : ℝ := (1 / 64) / L
  have hε : 0 < ε := div_pos (by norm_num) hL
  have hεL : ε * L = 1 / 64 := div_mul_cancel₀ _ hL.ne'
  have hεsmall : ε ≤ (1 / 64 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hLone hε.le
    nlinarith only [h, hεL]
  have hbound {t : ℝ} (ht : t ≤ L) : ε * t ≤ 1 / 64 :=
    (mul_le_mul_of_nonneg_left ht hε.le).trans_eq hεL
  refine ⟨ε, hε, lt_of_le_of_lt hεsmall (by norm_num), ?_, ?_, ?_, ?_⟩
  · exact (hbound (by dsimp [L]; linarith only [hb, hc, hd])).trans (by norm_num)
  · exact (hbound (by dsimp [L]; linarith only [ha, hc, hd])).trans (by norm_num)
  · exact (hbound (by dsimp [L]; linarith only [ha, hb, hd])).trans (by norm_num)
  · exact (hbound (by dsimp [L]; linarith only [ha, hb, hc])).trans (by norm_num)

/-- A single common seminorm ball supplies both lower bounds throughout the
physical annulus. The cutoff contributes only its radial derivative. -/
theorem exists_scalarStateBall_positivity_of_low_jet_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v₀ : ScalarHeightSpace S) (base : ℕ)
    (Cm Cr Ct Ctt Cχ M : ℝ)
    (hCm : 0 ≤ Cm) (hCr : 0 ≤ Cr) (hCt : 0 ≤ Ct) (hCtt : 0 ≤ Ctt)
    (hCχ : 0 ≤ Cχ) (hM : 0 ≤ M)
    (hprofile : ∀ r ∈ Ioo D.a D.b, D.w r ≤ M)
    (hmean : ∀ v : ScalarHeightSpace S, ∀ r ∈ Ioo D.a D.b,
      |angularMean (fun θ => (S.height scalarBeta).decode v (r, θ))| ≤
        Cm * scalarHeightGrading S base v)
    (hradial : ∀ v : ScalarHeightSpace S, ∀ p ∈ annularOpen D,
      |radialPartial ((S.height scalarBeta).decode v) p| ≤
        Cr * scalarHeightGrading S base v * D.w p.1)
    (hangular : ∀ v : ScalarHeightSpace S, ∀ p ∈ annularOpen D,
      |heightAngular ((S.height scalarBeta).decode v) p| ≤ Ct * scalarHeightGrading S base v)
    (hsecond : ∀ v : ScalarHeightSpace S, ∀ p ∈ annularOpen D,
      |angularPartial (heightAngular ((S.height scalarBeta).decode v)) p| ≤
        Ctt * scalarHeightGrading S base v * D.w p.1)
    (hcutoff : ∀ r ∈ Ioo D.a D.b, |deriv S.chiLeft r| ≤ Cχ * D.w r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ scalarStateBall S v₀ base ε,
      ∀ p ∈ annularOpen D, 0 < scalarStateProfile D S x p.1 ∧
        (1 / 2 : ℝ) ≤ polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p ∧
        (7 / 8 : ℝ) * scalarStateProfile D S x p.1 ≤
          heightQ (profileEnergy (scalarStateProfile D S x) p)
            (heightRadial (scalarStateHeight D S x) p)
            (angularPartial (heightAngular (scalarStateHeight D S x)) p) := by
  let N : ℝ := scalarHeightGrading S base v₀ + 1
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let A : ℝ := Cr * N + Cχ
  let B : ℝ := Ct * N
  let C : ℝ := Ctt * N
  let K : ℝ := 1 + 4 * M ^ 2
  have hA : 0 ≤ A := add_nonneg (mul_nonneg hCr hN) hCχ
  have hB : 0 ≤ B := mul_nonneg hCt hN
  have hC : 0 ≤ C := mul_nonneg hCtt hN
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨ε, hε, hεone, hεm, hεr, hεt, hεtt⟩ := exists_scalar_geometry_radius
    hCm (mul_nonneg hK hA) (mul_nonneg hK hB) (mul_nonneg hK hC)
  refine ⟨ε, hε, hεone, ?_⟩
  intro x hx p hp
  have hcoordinates := scalarStateBall_coordinate_bounds hx
  have hv : scalarHeightGrading S base x.1.1.2 ≤ N := by
    have h := scalarStateBall_height_bound hx
    dsimp [N]
    linarith only [h, hεone]
  have hc : |x.1.2| ≤ 1 := by
    have h := hcoordinates.2.2.1
    rw [Real.norm_eq_abs] at h
    linarith only [h, hεone]
  have hq : |x.2| ≤ ε := by
    simpa only [Real.norm_eq_abs] using hcoordinates.2.2.2.le
  have hm : |angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (p.1, θ))| ≤ 1 / 2 := by
    calc
      _ ≤ Cm * scalarHeightGrading S base x.1.1.1 := hmean _ _ hp.1
      _ ≤ Cm * ε := mul_le_mul_of_nonneg_left hcoordinates.1.le hCm
      _ ≤ 1 / 2 := by nlinarith only [hεm]
  have hw := scalarStateProfile_bounds_of_mean_small hD x hp.1 hm
  have hw₀ : 0 < D.w p.1 := hD.choose_spec.1.2.2.2.2.1 p.1 hp.1
  have hE : 1 + scalarStateProfile D S x p.1 ^ 2 ≤ K := by
    have hwupper : scalarStateProfile D S x p.1 ≤ 2 * M := by
      nlinarith [hw.2.2, hprofile p.1 hp.1]
    have hprod := mul_nonneg (sub_nonneg.mpr hwupper)
      (show 0 ≤ 2 * M + scalarStateProfile D S x p.1 from by linarith only [hM, hw.1.le])
    dsimp [K]
    nlinarith only [hprod]
  have hur : |radialPartial (scalarStateIncrement S x) p| ≤ A * D.w p.1 := by
    change |radialPartial (scalarCommonHeightDecode S (x.1.1.2, x.1.2)) p| ≤ _
    rw [scalarCommonHeightDecode_radialPartial hT hS]
    calc
      _ ≤ |radialPartial ((S.height scalarBeta).decode x.1.1.2) p| +
          |x.1.2 * deriv S.chiLeft p.1| := abs_add _ _
      _ ≤ Cr * scalarHeightGrading S base x.1.1.2 * D.w p.1 +
          |x.1.2| * (Cχ * D.w p.1) := by
        rw [abs_mul]
        exact add_le_add (hradial _ _ hp)
          (mul_le_mul_of_nonneg_left (hcutoff _ hp.1) (abs_nonneg _))
      _ ≤ Cr * N * D.w p.1 + 1 * (Cχ * D.w p.1) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hCr) hw₀.le)
          (mul_le_mul_of_nonneg_right hc (mul_nonneg hCχ hw₀.le))
      _ = A * D.w p.1 := by dsimp [A]; ring
  have hut : |heightAngular (scalarStateIncrement S x) p| ≤ B := by
    change |heightAngular (scalarCommonHeightDecode S (x.1.1.2, x.1.2)) p| ≤ _
    rw [scalarCommonHeightDecode_heightAngular_eq hT hS]
    exact (hangular _ _ hp).trans (mul_le_mul_of_nonneg_left hv hCt)
  have hutt : |angularPartial (heightAngular (scalarStateIncrement S x)) p| ≤ C * D.w p.1 := by
    change |angularPartial (heightAngular (scalarCommonHeightDecode S (x.1.1.2, x.1.2))) p| ≤ _
    rw [scalarCommonHeightDecode_heightAngular_eq hT hS]
    exact (hsecond _ _ hp).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hCtt) hw₀.le)
  have hscale {L bound : ℝ} (hL : 0 ≤ L) (hεL : ε * (K * L) ≤ bound) :
      K * |x.2| * L ≤ bound := by
    calc
      K * |x.2| * L = |x.2| * (K * L) := by ring
      _ ≤ ε * (K * L) := mul_le_mul_of_nonneg_right hq (mul_nonneg hK hL)
      _ ≤ bound := hεL
  exact scalarState_positivity_of_reference_jets hD hT hS x hp hm hE hur hut hutt
    (hscale hA hεr) (hscale hB hεt) (hscale hC hεtt)

end ContinuousFlexibility.Statements
