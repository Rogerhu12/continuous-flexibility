import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Scalar.WeightedGeometryLowJets

/-!
# One low-order neighbourhood for the actual state denominators

The height estimates use the actual nonlinear state, including its left
constant.  Only a comparison of the actual profile with the reference profile
is needed from the separate control construction.  All radii below are chosen
before any higher derivative order is requested.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem neighborhoodStateGrading_apply (S : PhysicalSpacesData) (s : ℕ)
    (x : AnnularState S) :
    stateGrading S s x = (S.height (3 / 4 : ℝ)).grading s x.1.1 + ‖x.1.2‖ +
      (‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
        (S.circle (3 / 4 : ℝ)).grading s x.2.2.2)) := rfl

theorem neighborhoodStateGrading_height_le (S : PhysicalSpacesData) (s : ℕ)
    (x : AnnularState S) :
    (S.height (3 / 4 : ℝ)).grading s x.1.1 ≤ stateGrading S s x ∧
      |x.1.2| ≤ stateGrading S s x := by
  have hrest : 0 ≤ ‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.2) :=
    add_nonneg (norm_nonneg x.2.1)
      (add_nonneg (apply_nonneg ((S.circle (3 / 4 : ℝ)).grading s) x.2.2.1)
        (apply_nonneg ((S.circle (3 / 4 : ℝ)).grading s) x.2.2.2))
  have hp : (S.height (3 / 4 : ℝ)).grading s x.1.1 + ‖x.1.2‖ ≤
      stateGrading S s x :=
    (le_add_of_nonneg_right hrest).trans_eq (neighborhoodStateGrading_apply S s x).symm
  exact ⟨(le_add_of_nonneg_right (norm_nonneg x.1.2)).trans hp,
    (Real.norm_eq_abs x.1.2).symm.trans_le
      ((le_add_of_nonneg_left
        (apply_nonneg ((S.height (3 / 4 : ℝ)).grading s) x.1.1)).trans hp)⟩

private theorem neighborhood_seminorm_center_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E)
    {x c : E} {ε : ℝ} (hε : ε ≤ 1) (hx : p (x - c) < ε) :
    p x ≤ p c + 1 := by
  calc
    p x = p ((x - c) + c) := congrArg p (sub_add_cancel x c).symm
    _ ≤ p (x - c) + p c := map_add_le_add p (x - c) c
    _ ≤ ε + p c := add_le_add_right hx.le _
    _ ≤ 1 + p c := add_le_add_right hε _
    _ = p c + 1 := add_comm _ _

theorem neighborhoodStateGrading_bound {C : NonlinearGeometryData S}
    {base : ℕ} {ε : ℝ} (hε : ε ≤ 1) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) :
    stateGrading S base z.1 ≤ stateGrading S base C.referenceState + 1 :=
  neighborhood_seminorm_center_bound (stateGrading S base) hε hz.1

/-- The scalar common-height decoder is exactly the nonlinear height pair. -/
theorem neighborhood_stateU_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) : ContDiff ℝ ∞ (stateU S x) := by
  change ContDiff ℝ ∞ (scalarCommonHeightDecode S x.1)
  exact scalarCommonHeightDecode_contDiff hT hS x.1

/-- The three actual height jets have one fixed order-four bound. -/
theorem stateU_low_jet_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ∃ Cr Ct Ctt : ℝ, 0 ≤ Cr ∧ 0 ≤ Ct ∧ 0 ≤ Ctt ∧
      ∀ x : AnnularState S, ∀ p ∈ annularOpen D,
        |radialPartial (stateU S x) p| ≤ Cr * stateGrading S 4 x * D.w p.1 ∧
        |heightAngular (stateU S x) p| ≤ Ct * stateGrading S 4 x ∧
        |angularPartial (heightAngular (stateU S x)) p| ≤
          Ctt * stateGrading S 4 x * D.w p.1 := by
  have pr := scalarHeight_radial_low_jet_bound (D := D) (T := T) (S := S) hD hT hS
  have pt := scalarHeight_angular_low_jet_bound (D := D) (T := T) (S := S) hD hT hS
  have ptt := scalarHeight_angularSecond_low_jet_bound (D := D) (T := T) (S := S) hD hT hS
  have pχ := scalarCutoff_deriv_le_reference hD hS
  let Cr : ℝ := pr.choose
  let Ct : ℝ := pt.choose
  let Ctt : ℝ := ptt.choose
  let Cχ : ℝ := pχ.choose
  have hCr : 0 ≤ Cr := pr.choose_spec.1
  have hCt : 0 ≤ Ct := pt.choose_spec.1
  have hCtt : 0 ≤ Ctt := ptt.choose_spec.1
  have hCχ : 0 ≤ Cχ := pχ.choose_spec.1
  have hr := pr.choose_spec.2
  have ht := pt.choose_spec.2
  have htt := ptt.choose_spec.2
  have hχ := pχ.choose_spec.2
  refine ⟨Cr + Cχ, Ct, Ctt, add_nonneg hCr hCχ, hCt, hCtt, ?_⟩
  intro x p hp
  have hc := neighborhoodStateGrading_height_le S 4 x
  have hw : 0 ≤ D.w p.1 := (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1).le
  refine ⟨?_, ?_, ?_⟩
  · change |radialPartial (scalarCommonHeightDecode S x.1) p| ≤ _
    rw [scalarCommonHeightDecode_radialPartial hT hS]
    calc
      _ ≤ |radialPartial ((S.height scalarBeta).decode x.1.1) p| +
          |x.1.2 * deriv S.chiLeft p.1| := abs_add_le _ _
      _ ≤ Cr * scalarHeightGrading S 4 x.1.1 * D.w p.1 +
          |x.1.2| * (Cχ * D.w p.1) := by
        rw [abs_mul]
        exact add_le_add (hr _ _ hp)
          (mul_le_mul_of_nonneg_left (hχ _ hp.1) (abs_nonneg _))
      _ ≤ Cr * stateGrading S 4 x * D.w p.1 +
          stateGrading S 4 x * (Cχ * D.w p.1) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc.1 hCr) hw)
          (mul_le_mul_of_nonneg_right hc.2 (mul_nonneg hCχ hw))
      _ = _ := by ring
  · change |heightAngular (scalarCommonHeightDecode S x.1) p| ≤ _
    rw [scalarCommonHeightDecode_heightAngular_eq hT hS]
    exact (ht _ _ hp).trans (mul_le_mul_of_nonneg_left hc.1 hCt)
  · change |angularPartial (heightAngular (scalarCommonHeightDecode S x.1)) p| ≤ _
    rw [scalarCommonHeightDecode_heightAngular_eq hT hS]
    exact (htt _ _ hp).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc.1 hCtt) hw)

/-- The lower-bound calculation also bounds the opposite perturbation, giving
both sides of each denominator on the same numerical scale. -/
theorem neighborhood_height_bounds_of_scaled_jets {w a b c K : ℝ}
    (hw : 0 ≤ w) (hE : 1 + w ^ 2 ≤ K)
    (ha : K * |a| ≤ w / 16) (hb : K * |b| ≤ 1 / 4)
    (hc : K * |c| ≤ w / 16) :
    (1 / 2 : ℝ) ≤ heightDiscriminant (radialEnergy w) (w + a) b ∧
      heightDiscriminant (radialEnergy w) (w + a) b ≤ (3 / 2 : ℝ) ∧
      (7 / 8 : ℝ) * w ≤ heightQ (radialEnergy w) (w + a) c ∧
      heightQ (radialEnergy w) (w + a) c ≤ (9 / 8 : ℝ) * w ∧
      (3 / 4 : ℝ) ≤ 1 - b ^ 2 := by
  have hp := weighted_height_bounds_of_scaled_jets hw hE ha hb hc
  have hn := weighted_height_bounds_of_scaled_jets (a := -a) (c := -c) hw hE
    (by simpa only [abs_neg] using ha) hb (by simpa only [abs_neg] using hc)
  have hKone : (1 : ℝ) ≤ K := by nlinarith only [hE, sq_nonneg w]
  have hbsmall : |b| ≤ (1 / 4 : ℝ) := by
    have hh := mul_nonneg (sub_nonneg.mpr hKone) (abs_nonneg b)
    nlinarith only [hb, hh]
  refine ⟨hp.1, ?_, hp.2, ?_, ?_⟩
  · have hh := hn.1
    rw [weighted_heightDiscriminant_expansion] at hh ⊢
    nlinarith only [hh, sq_nonneg a, sq_nonneg b, sq_nonneg (w * b)]
  · have hh := hn.2
    rw [weighted_heightQ_expansion] at hh ⊢
    nlinarith only [hh]
  · have hh := mul_le_mul hbsmall hbsmall (abs_nonneg b) (by norm_num)
    nlinarith only [hh, sq_abs b]

theorem neighborhood_height_bounds_of_reference_jets
    {w₀ w q ur ut utt K A B C : ℝ}
    (hw₀ : 0 < w₀) (hw : w₀ / 2 ≤ w) (hE : 1 + w ^ 2 ≤ K)
    (hur : |ur| ≤ A * w₀) (hut : |ut| ≤ B) (hutt : |utt| ≤ C * w₀)
    (hqr : K * |q| * A ≤ 1 / 32) (hqt : K * |q| * B ≤ 1 / 4)
    (hqtt : K * |q| * C ≤ 1 / 32) :
    (1 / 2 : ℝ) ≤ heightDiscriminant (radialEnergy w) (w + q * ur) (q * ut) ∧
      heightDiscriminant (radialEnergy w) (w + q * ur) (q * ut) ≤ (3 / 2 : ℝ) ∧
      (7 / 8 : ℝ) * w ≤ heightQ (radialEnergy w) (w + q * ur) (q * utt) ∧
      heightQ (radialEnergy w) (w + q * ur) (q * utt) ≤ (9 / 8 : ℝ) * w ∧
      (3 / 4 : ℝ) ≤ 1 - (q * ut) ^ 2 := by
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hK : 0 ≤ K := by nlinarith only [hE, sq_nonneg w]
  have hKq : 0 ≤ K * |q| := mul_nonneg hK (abs_nonneg q)
  have hrelative {d L : ℝ} (hd : |d| ≤ L * w₀)
      (hqL : K * |q| * L ≤ 1 / 32) : K * |q * d| ≤ w / 16 := by
    calc
      K * |q * d| = (K * |q|) * |d| := by rw [abs_mul]; ring
      _ ≤ (K * |q|) * (L * w₀) := mul_le_mul_of_nonneg_left hd hKq
      _ = (K * |q| * L) * w₀ := by ring
      _ ≤ (1 / 32 : ℝ) * w₀ := mul_le_mul_of_nonneg_right hqL hw₀.le
      _ ≤ w / 16 := by nlinarith only [hw]
  have hangular : K * |q * ut| ≤ 1 / 4 := by
    calc
      K * |q * ut| = (K * |q|) * |ut| := by rw [abs_mul]; ring
      _ ≤ (K * |q|) * B := mul_le_mul_of_nonneg_left hut hKq
      _ ≤ 1 / 4 := hqt
  exact neighborhood_height_bounds_of_scaled_jets hwpos.le hE
    (hrelative hur hqr) hangular (hrelative hutt hqtt)

theorem stateRadialHeight_hasDerivAt_of_contDiff {C : NonlinearGeometryData S}
    {x : AnnularState S} (hw : ContDiff ℝ ∞ (stateProfile D S C x)) (r : ℝ) :
    HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable D.b r)
    hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuous.continuousAt

theorem stateRadialHeight_contDiff_of_contDiff {C : NonlinearGeometryData S}
    {x : AnnularState S} (hw : ContDiff ℝ ∞ (stateProfile D S C x)) :
    ContDiff ℝ ∞ (stateRadialHeight D S C x) := by
  refine contDiff_infty_iff_deriv.mpr
    ⟨fun r => (stateRadialHeight_hasDerivAt_of_contDiff hw r).differentiableAt, ?_⟩
  have he : deriv (stateRadialHeight D S C x) = stateProfile D S C x :=
    funext fun r => (stateRadialHeight_hasDerivAt_of_contDiff hw r).deriv
  rw [he]
  exact hw

theorem stateHeight_heightRadial_of_contDiff_profile
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {C : NonlinearGeometryData S} {z : AnnularState S × ℝ}
    (hw : ContDiff ℝ ∞ (stateProfile D S C z.1)) (p : PolarPoint) :
    heightRadial (stateHeight D S C z) p =
      stateProfile D S C z.1 p.1 + z.2 * radialPartial (stateU S z.1) p := by
  have hh := Radial.contDiff_radialHeightField (stateRadialHeight_contDiff_of_contDiff hw)
  have hu := neighborhood_stateU_contDiff hT hS z.1
  change heightRadial (heightFamily
    (Radial.radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2) p = _
  rw [heightRadial_heightFamily (hh.differentiable (by simp)) (hu.differentiable (by simp)),
    Radial.heightRadial_radialHeightField (stateRadialHeight_hasDerivAt_of_contDiff hw)]
  rfl

theorem stateHeight_heightAngular_of_contDiff_profile
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {C : NonlinearGeometryData S} {z : AnnularState S × ℝ}
    (hw : ContDiff ℝ ∞ (stateProfile D S C z.1)) (p : PolarPoint) :
    heightAngular (stateHeight D S C z) p = z.2 * heightAngular (stateU S z.1) p := by
  have hh := Radial.contDiff_radialHeightField (stateRadialHeight_contDiff_of_contDiff hw)
  have hu := neighborhood_stateU_contDiff hT hS z.1
  change heightAngular (heightFamily
    (Radial.radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2) p = _
  rw [heightAngular_heightFamily (hh.differentiable (by simp)) (hu.differentiable (by simp)),
    Radial.heightAngular_radialHeightField (stateRadialHeight_hasDerivAt_of_contDiff hw)]
  simp only [heightFamily, zero_add]

theorem stateHeight_angularPartial_heightAngular_of_contDiff_profile
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {C : NonlinearGeometryData S} {z : AnnularState S × ℝ}
    (hw : ContDiff ℝ ∞ (stateProfile D S C z.1)) {p : PolarPoint} (hr : p.1 ≠ 0) :
    angularPartial (heightAngular (stateHeight D S C z)) p =
      z.2 * angularPartial (heightAngular (stateU S z.1)) p := by
  have hh := Radial.contDiff_radialHeightField (stateRadialHeight_contDiff_of_contDiff hw)
  have hu := neighborhood_stateU_contDiff hT hS z.1
  change angularPartial (heightAngular (heightFamily
    (Radial.radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2)) p = _
  rw [angularPartial_heightAngular_heightFamily hh hu hr,
    Radial.heightAngular_radialHeightField (stateRadialHeight_hasDerivAt_of_contDiff hw),
    angularPartial_const, zero_add]

/-- One radius works for every state and physical point, once the separately
constructed profile has its uniform reference comparison. -/
theorem exists_stateNeighborhood_denominator_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ z ∈ stateNeighborhood S C 4 ε,
      ContDiff ℝ ∞ (stateProfile D S C z.1) →
      (∀ r ∈ Ioo D.a D.b, (1 / 2 : ℝ) ≤ stateProfile D S C z.1 r / D.w r ∧
        stateProfile D S C z.1 r / D.w r ≤ 2) →
      ∀ p ∈ annularOpen D,
        (7 / 8 : ℝ) ≤ heightQ (profileEnergy (stateProfile D S C z.1) p)
          (heightRadial (stateHeight D S C z) p)
          (angularPartial (heightAngular (stateHeight D S C z)) p) /
            stateProfile D S C z.1 p.1 ∧
        heightQ (profileEnergy (stateProfile D S C z.1) p)
          (heightRadial (stateHeight D S C z) p)
          (angularPartial (heightAngular (stateHeight D S C z)) p) /
            stateProfile D S C z.1 p.1 ≤ (9 / 8 : ℝ) ∧
        (1 / 2 : ℝ) ≤ polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ≤ (3 / 2 : ℝ) ∧
        (3 / 4 : ℝ) ≤ 1 - heightAngular (stateHeight D S C z) p ^ 2 := by
  obtain ⟨Cr, Ct, Ctt, hCr, hCt, hCtt, hjet⟩ := stateU_low_jet_bounds hD hT hS
  obtain ⟨M, hM, hMbound⟩ := referenceProfile_uniform_upper_bound hD
  let N : ℝ := stateGrading S 4 C.referenceState + 1
  let A : ℝ := Cr * N
  let B : ℝ := Ct * N
  let E : ℝ := Ctt * N
  let K : ℝ := 1 + 4 * M ^ 2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hA : 0 ≤ A := mul_nonneg hCr hN
  have hB : 0 ≤ B := mul_nonneg hCt hN
  have hE : 0 ≤ E := mul_nonneg hCtt hN
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨ε, hε, hεone, _, hεr, hεt, hεtt⟩ := exists_scalar_geometry_radius
    (show (0 : ℝ) ≤ 0 from le_rfl) (mul_nonneg hK hA)
    (mul_nonneg hK hB) (mul_nonneg hK hE)
  refine ⟨ε, hε, hεone, ?_⟩
  intro z hz hws hcompare p hp
  have hsize : stateGrading S 4 z.1 ≤ N := neighborhoodStateGrading_bound hεone.le hz
  have hq : |z.2| ≤ ε := hz.2.le
  have hw₀ : 0 < D.w p.1 := hD.choose_spec.1.2.2.2.2.1 p.1 hp.1
  have hcomp := hcompare p.1 hp.1
  have hwlow : D.w p.1 / 2 ≤ stateProfile D S C z.1 p.1 := by
    have hh := (le_div_iff₀ hw₀).mp hcomp.1
    linarith only [hh]
  have hw : 0 < stateProfile D S C z.1 p.1 :=
    lt_of_lt_of_le (by positivity) hwlow
  have hwupper : stateProfile D S C z.1 p.1 ≤ 2 * M :=
    ((div_le_iff₀ hw₀).mp hcomp.2).trans
      (mul_le_mul_of_nonneg_left (hMbound p.1 hp.1) (by norm_num))
  have henergy : 1 + stateProfile D S C z.1 p.1 ^ 2 ≤ K := by
    have hh := mul_nonneg (sub_nonneg.mpr hwupper)
      (show 0 ≤ 2 * M + stateProfile D S C z.1 p.1 from by linarith only [hM, hw.le])
    dsimp [K]
    nlinarith only [hh]
  have hj := hjet z.1 p hp
  have hur : |radialPartial (stateU S z.1) p| ≤ A * D.w p.1 :=
    hj.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsize hCr) hw₀.le)
  have hut : |heightAngular (stateU S z.1) p| ≤ B :=
    hj.2.1.trans (mul_le_mul_of_nonneg_left hsize hCt)
  have hutt : |angularPartial (heightAngular (stateU S z.1)) p| ≤ E * D.w p.1 :=
    hj.2.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsize hCtt) hw₀.le)
  have hscale {L bound : ℝ} (hL : 0 ≤ L) (hεL : ε * (K * L) ≤ bound) :
      K * |z.2| * L ≤ bound := by
    calc
      K * |z.2| * L = |z.2| * (K * L) := by ring
      _ ≤ ε * (K * L) := mul_le_mul_of_nonneg_right hq (mul_nonneg hK hL)
      _ ≤ bound := hεL
  have hb := neighborhood_height_bounds_of_reference_jets hw₀ hwlow henergy hur hut hutt
    (hscale hA hεr) (hscale hB hεt) (hscale hE hεtt)
  have hr := stateHeight_heightRadial_of_contDiff_profile hT hS (z := z) hws p
  have ht := stateHeight_heightAngular_of_contDiff_profile hT hS (z := z) hws p
  have htt := stateHeight_angularPartial_heightAngular_of_contDiff_profile hT hS
    (z := z) hws (p := p)
    (lt_trans hD.choose_spec.1.1 hp.1.1).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hr, htt]
    exact (le_div_iff₀ hw).mpr hb.2.2.1
  · rw [hr, htt]
    exact (div_le_iff₀ hw).mpr hb.2.2.2.1
  · simpa only [polarDiscriminant, profileEnergy, hr, ht] using hb.1
  · simpa only [polarDiscriminant, profileEnergy, hr, ht] using hb.2.1
  · rw [ht]
    exact hb.2.2.2.2

end ContinuousFlexibility.Statements
