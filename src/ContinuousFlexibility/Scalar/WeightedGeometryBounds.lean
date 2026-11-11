import ContinuousFlexibility.Scalar.WeightedStateRegularity
import ContinuousFlexibility.Scalar.WeightedNeighborhood

/-!
# Quantitative positivity for the actual scalar state

The profile and the three height jets are the functions fixed in the scalar
statement. Their exact algebraic expansions reduce positivity to explicit
small-jet inequalities. These are intermediate estimates, not new hypotheses
in a blueprint statement.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem weighted_profile_bounds_of_mean_small {w m : ℝ}
    (hw : 0 < w) (hm : |m| ≤ 1 / 2) :
    0 < w * (1 + m) ∧ w / 2 ≤ w * (1 + m) ∧ w * (1 + m) ≤ (3 / 2 : ℝ) * w := by
  have hm' := abs_le.mp hm
  have hlo : w / 2 ≤ w * (1 + m) := by nlinarith
  exact ⟨lt_of_lt_of_le (by positivity) hlo, hlo, by nlinarith⟩

theorem weighted_heightDiscriminant_expansion (w a b : ℝ) :
    heightDiscriminant (radialEnergy w) (w + a) b =
      1 - 2 * w * a - a ^ 2 - (1 + w ^ 2) * b ^ 2 := by
  unfold heightDiscriminant radialEnergy
  ring

theorem weighted_heightQ_expansion (w a c : ℝ) :
    heightQ (radialEnergy w) (w + a) c = w + a + (1 + w ^ 2) * c := rfl

/-- A fixed upper bound on the radial metric coefficient gives a single
numerical smallness scale for all the physical positivity requirements. -/
theorem weighted_height_bounds_of_scaled_jets {w a b c K : ℝ}
    (hw : 0 ≤ w) (hE : 1 + w ^ 2 ≤ K)
    (ha : K * |a| ≤ w / 16) (hb : K * |b| ≤ 1 / 4)
    (hc : K * |c| ≤ w / 16) :
    (1 / 2 : ℝ) ≤ heightDiscriminant (radialEnergy w) (w + a) b ∧
      (7 / 8 : ℝ) * w ≤ heightQ (radialEnergy w) (w + a) c := by
  have hKone : (1 : ℝ) ≤ K := by nlinarith [sq_nonneg w]
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hwK : w ≤ K := by nlinarith [sq_nonneg (w - 1)]
  have haK : K * |a| ≤ K / 16 := ha.trans (by nlinarith only [hwK])
  have haSmall : |a| ≤ (1 / 16 : ℝ) := by
    apply (mul_le_mul_iff_left₀ hK).mp
    nlinarith only [haK]
  have haw : w * |a| ≤ (1 / 16 : ℝ) := by
    apply (mul_le_mul_iff_left₀ hK).mp
    calc
      (w * |a|) * K = w * (K * |a|) := by ring
      _ ≤ w * (w / 16) := mul_le_mul_of_nonneg_left ha hw
      _ ≤ (1 / 16) * K := by nlinarith only [hE]
  have hbSmall : |b| ≤ (1 / 4 : ℝ) := by
    have hbK : |b| ≤ K * |b| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKone) (abs_nonneg b)]
    exact hbK.trans hb
  have hbEnergy : (1 + w ^ 2) * b ^ 2 ≤ (1 / 16 : ℝ) := by
    calc
      (1 + w ^ 2) * b ^ 2 ≤ K * b ^ 2 :=
        mul_le_mul_of_nonneg_right hE (sq_nonneg b)
      _ = (K * |b|) * |b| := by rw [← sq_abs b]; ring
      _ ≤ (1 / 4 : ℝ) * (1 / 4) :=
        mul_le_mul hb hbSmall (abs_nonneg b) (by norm_num)
      _ = 1 / 16 := by norm_num
  have haSquare : a ^ 2 ≤ (1 / 256 : ℝ) := by
    have h := mul_le_mul haSmall haSmall (abs_nonneg a) (by norm_num)
    nlinarith only [h, sq_abs a]
  have haUpper : w * a ≤ (1 / 16 : ℝ) :=
    (mul_le_mul_of_nonneg_left (le_abs_self a) hw).trans haw
  have haRelative : |a| ≤ w / 16 := by
    have haK' : |a| ≤ K * |a| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKone) (abs_nonneg a)]
    exact haK'.trans ha
  have hcEnergy : (1 + w ^ 2) * |c| ≤ w / 16 :=
    (mul_le_mul_of_nonneg_right hE (abs_nonneg c)).trans hc
  have hcLower : -(w / 16) ≤ (1 + w ^ 2) * c := by
    have h := mul_le_mul_of_nonneg_left (neg_abs_le c)
      (by positivity : (0 : ℝ) ≤ 1 + w ^ 2)
    nlinarith only [h, hcEnergy]
  constructor
  · rw [weighted_heightDiscriminant_expansion]
    nlinarith only [haUpper, haSquare, hbEnergy]
  · rw [weighted_heightQ_expansion]
    have haLower : -(w / 16) ≤ a := (neg_le_neg haRelative).trans (neg_abs_le a)
    linarith only [haLower, hcLower]

/-- Division by the positive actual profile is only a convenient way to
state the two relative smallness conditions; the proof uses scaled jets. -/
theorem weighted_height_bounds_of_normalized_jets {w a b c K : ℝ}
    (hw : 0 < w) (hE : 1 + w ^ 2 ≤ K)
    (ha : K * |a / w| ≤ 1 / 16) (hb : K * |b| ≤ 1 / 4)
    (hc : K * |c / w| ≤ 1 / 16) :
    (1 / 2 : ℝ) ≤ heightDiscriminant (radialEnergy w) (w + a) b ∧
      (7 / 8 : ℝ) * w ≤ heightQ (radialEnergy w) (w + a) c := by
  have hscale {d : ℝ} (hd : K * |d / w| ≤ 1 / 16) : K * |d| ≤ w / 16 := by
    rw [abs_div, abs_of_pos hw, ← mul_div_assoc] at hd
    have h := (div_le_iff₀ hw).mp hd
    nlinarith only [h]
  exact weighted_height_bounds_of_scaled_jets hw.le hE (hscale ha) hb (hscale hc)

/-- Reference-profile jet bounds transfer to the perturbed profile using
the uniform lower comparison `w₀/2 ≤ w`. The same constants work at all radii. -/
theorem weighted_height_bounds_of_reference_jets
    {w₀ w q ur ut utt K A B C : ℝ}
    (hw₀ : 0 < w₀) (hw : w₀ / 2 ≤ w) (hE : 1 + w ^ 2 ≤ K)
    (hur : |ur| ≤ A * w₀) (hut : |ut| ≤ B) (hutt : |utt| ≤ C * w₀)
    (hqr : K * |q| * A ≤ 1 / 32) (hqt : K * |q| * B ≤ 1 / 4)
    (hqtt : K * |q| * C ≤ 1 / 32) :
    (1 / 2 : ℝ) ≤ heightDiscriminant (radialEnergy w) (w + q * ur) (q * ut) ∧
      (7 / 8 : ℝ) * w ≤ heightQ (radialEnergy w) (w + q * ur) (q * utt) := by
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hK : 0 ≤ K := by nlinarith [sq_nonneg w]
  have hKq : 0 ≤ K * |q| := mul_nonneg hK (abs_nonneg q)
  have hrelative {d L : ℝ} (hd : |d| ≤ L * w₀) (hqL : K * |q| * L ≤ 1 / 32) :
      K * |q * d| ≤ w / 16 := by
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
  exact weighted_height_bounds_of_scaled_jets hwpos.le hE
    (hrelative hur hqr) hangular (hrelative hutt hqtt)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarStateProfile_bounds_of_mean_small
    (hD : IsAccumulatingProfile D) (x : ScalarWeightedState S) {r : ℝ}
    (hr : r ∈ Ioo D.a D.b)
    (hm : |angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (r, θ))| ≤ 1 / 2) :
    0 < scalarStateProfile D S x r ∧ D.w r / 2 ≤ scalarStateProfile D S x r ∧
      scalarStateProfile D S x r ≤ (3 / 2 : ℝ) * D.w r := by
  obtain ⟨_, hD⟩ := hD
  exact weighted_profile_bounds_of_mean_small (hD.1.2.2.2.2.1 r hr) hm

theorem scalarStateHeight_heightRadial
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    heightRadial (scalarStateHeight D S x) p =
      scalarStateProfile D S x p.1 + x.2 * radialPartial (scalarStateIncrement S x) p := by
  have hh := Radial.contDiff_radialHeightField (scalarStatePrimitive_contDiff hD hT hS x)
  have hu := scalarStateIncrement_contDiff hT hS x
  change heightRadial (heightFamily _ _ x.2) p = _
  rw [heightRadial_heightFamily (hh.differentiable (by simp)) (hu.differentiable (by simp)),
    Radial.heightRadial_radialHeightField (scalarStatePrimitive_hasDerivAt hD hT hS x)]
  rfl

theorem scalarStateHeight_heightAngular
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    heightAngular (scalarStateHeight D S x) p = x.2 * heightAngular (scalarStateIncrement S x) p := by
  have hh := Radial.contDiff_radialHeightField (scalarStatePrimitive_contDiff hD hT hS x)
  have hu := scalarStateIncrement_contDiff hT hS x
  change heightAngular (heightFamily _ _ x.2) p = _
  rw [heightAngular_heightFamily (hh.differentiable (by simp)) (hu.differentiable (by simp)),
    Radial.heightAngular_radialHeightField (scalarStatePrimitive_hasDerivAt hD hT hS x)]
  simp only [heightFamily, zero_add]

theorem scalarStateHeight_angularPartial_heightAngular
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0) :
    angularPartial (heightAngular (scalarStateHeight D S x)) p =
      x.2 * angularPartial (heightAngular (scalarStateIncrement S x)) p := by
  have hh := Radial.contDiff_radialHeightField (scalarStatePrimitive_contDiff hD hT hS x)
  have hu := scalarStateIncrement_contDiff hT hS x
  change angularPartial (heightAngular (heightFamily _ _ x.2)) p = _
  rw [angularPartial_heightAngular_heightFamily hh hu hr,
    Radial.heightAngular_radialHeightField (scalarStatePrimitive_hasDerivAt hD hT hS x),
    angularPartial_const, zero_add]

theorem scalarState_discriminant_expansion
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (p : PolarPoint) :
    polarDiscriminant (scalarStateProfile D S x) (scalarStateHeight D S x) p =
      1 - 2 * scalarStateProfile D S x p.1 *
          (x.2 * radialPartial (scalarStateIncrement S x) p) -
        (x.2 * radialPartial (scalarStateIncrement S x) p) ^ 2 -
        (1 + scalarStateProfile D S x p.1 ^ 2) *
          (x.2 * heightAngular (scalarStateIncrement S x) p) ^ 2 := by
  unfold polarDiscriminant
  rw [scalarStateHeight_heightRadial hD hT hS x p,
    scalarStateHeight_heightAngular hD hT hS x p]
  exact weighted_heightDiscriminant_expansion _ _ _

theorem scalarState_Q_expansion
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) {p : PolarPoint} (hr : p.1 ≠ 0) :
    heightQ (profileEnergy (scalarStateProfile D S x) p)
      (heightRadial (scalarStateHeight D S x) p)
      (angularPartial (heightAngular (scalarStateHeight D S x)) p) =
      scalarStateProfile D S x p.1 + x.2 *
        (radialPartial (scalarStateIncrement S x) p +
          (1 + scalarStateProfile D S x p.1 ^ 2) *
            angularPartial (heightAngular (scalarStateIncrement S x)) p) := by
  rw [scalarStateHeight_heightRadial hD hT hS x p,
    scalarStateHeight_angularPartial_heightAngular hD hT hS x hr]
  unfold heightQ profileEnergy radialEnergy
  ring

end ContinuousFlexibility.Statements
