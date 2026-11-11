import ContinuousFlexibility.Analysis.SpacesTracePackets
import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds
import ContinuousFlexibility.Analysis.SpacesTraceRestriction
import ContinuousFlexibility.Analysis.SpacesTraceSeries

/-!
# Uniform estimates for the extension packets

Every inverse material window radius costs one sample weight, regardless of
the derivative order. Two additional sample weights leave a square summable
inverse-weight factor, allowing the packet series to converge in every
physical jet norm with one fixed loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)

def spacesTraceRadius : ℕ → ℝ := Classical.choose (spaces_trace_windows hD hT)

theorem spacesTraceRadius_pos (m : ℕ) : 0 < spacesTraceRadius hD hT m :=
  ((Classical.choose_spec (spaces_trace_windows hD hT)).1 m).1

theorem spacesTraceRadius_le_one (m : ℕ) : spacesTraceRadius hD hT m ≤ 1 :=
  ((Classical.choose_spec (spaces_trace_windows hD hT)).1 m).2

theorem spacesTraceRadius_disjoint : Pairwise (fun m n => Disjoint
    (Ioo (spaces_trace_center T m - spacesTraceRadius hD hT m)
      (spaces_trace_center T m + spacesTraceRadius hD hT m))
    (Ioo (spaces_trace_center T n - spacesTraceRadius hD hT n)
      (spaces_trace_center T n + spacesTraceRadius hD hT n))) :=
  (Classical.choose_spec (spaces_trace_windows hD hT)).2.2.1

theorem spacesTraceRadius_locallyFinite : LocallyFinite (fun m =>
    Icc (spaces_trace_center T m - spacesTraceRadius hD hT m)
      (spaces_trace_center T m + spacesTraceRadius hD hT m)) :=
  (Classical.choose_spec (spaces_trace_windows hD hT)).2.2.2.1

theorem spacesTraceRadius_inv_pow_bound (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, (spacesTraceRadius hD hT m)⁻¹ ^ a ≤ C * T.M (T.sample m) :=
  (Classical.choose_spec (spaces_trace_windows hD hT)).2.2.2.2 a

def spacesTraceNormalized (γ : ℝ) (f : ℕ → ℝ → ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  T.H (T.sample m) ^ (-γ) * f m θ

def spacesTraceMaterialExtension (γ : ℝ) (f : ℕ → ℝ → ℝ) : PolarPoint → ℝ :=
  spacesTracePacketSum (spaces_trace_center T) (spacesTraceRadius hD hT)
    (spacesTraceNormalized (T := T) γ f)

def spacesTracePacketJet (γ : ℝ) (f : ℕ → ℝ → ℝ)
    (a b c m : ℕ) (p : PolarPoint) : ℝ :=
  T.M (T.radius p.1) ^ c *
    (iteratedDeriv a (spacesTraceBump (spaces_trace_center T m) (spacesTraceRadius hD hT m)) p.1 *
      (T.H (T.sample m) ^ (-γ) * iteratedDeriv b (f m) p.2))

theorem spacesTraceMaterialExtension_contDiff {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) : ContDiff ℝ ∞ (spacesTraceMaterialExtension hD hT γ f) :=
  spacesTracePacketSum_contDiff _ _ (spacesTraceRadius_pos hD hT)
    (spacesTraceRadius_locallyFinite hD hT)
    (fun m => contDiff_const.mul (hf.1 m).1)

theorem spacesTraceMaterialExtension_periodic {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) :
    Function.Periodic (spacesTraceMaterialExtension hD hT γ f) (0, Real.pi) :=
  spacesTracePacketSum_periodic _ _ (fun m θ =>
    congrArg (T.H (T.sample m) ^ (-γ) * ·) ((hf.1 m).2 θ))

theorem spacesTraceMaterialExtension_even (γ : ℝ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ m θ, f m (-θ) = f m θ) (x θ : ℝ) :
    spacesTraceMaterialExtension hD hT γ f (x, -θ) =
      spacesTraceMaterialExtension hD hT γ f (x, θ) :=
  spacesTracePacketSum_even _ _ (v := spacesTraceNormalized (T := T) γ f)
    (fun m θ => congrArg (T.H (T.sample m) ^ (-γ) * ·) (hf m θ)) x θ

theorem spacesTraceMaterialExtension_center (γ : ℝ) (f : ℕ → ℝ → ℝ) (m : ℕ) (θ : ℝ) :
    spacesTraceMaterialExtension hD hT γ f (spaces_trace_center T m, θ) =
      T.H (T.sample m) ^ (-γ) * f m θ :=
  spacesTracePacketSum_center _ _ (spacesTraceRadius_pos hD hT)
    (spacesTraceRadius_disjoint hD hT) _ m θ

theorem spacesTraceMaterialExtension_weighted_mixedDerivative {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) (a b c : ℕ) (p : PolarPoint) :
    T.M (T.radius p.1) ^ c * mixedDerivative a b (spacesTraceMaterialExtension hD hT γ f) p =
      ∑' m, spacesTracePacketJet hD hT γ f a b c m p := by
  have hv (m : ℕ) : ContDiff ℝ ∞ (spacesTraceNormalized (T := T) γ f m) :=
    contDiff_const.mul (hf.1 m).1
  rw [spacesTraceMaterialExtension, spacesTracePacketSum_mixedDerivative _ _
    (spacesTraceRadius_pos hD hT) (spacesTraceRadius_locallyFinite hD hT)
    hv]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  have hd : iteratedDeriv b (spacesTraceNormalized (T := T) γ f m) =
      fun θ => T.H (T.sample m) ^ (-γ) * iteratedDeriv b (f m) θ := by
    funext θ
    exact iteratedDeriv_const_mul_field _ _
  rw [hd]
  rfl

theorem spacesTracePacketJet_continuous {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) (a b c m : ℕ) :
    Continuous (spacesTracePacketJet hD hT γ f a b c m) := by
  have hM : ContDiff ℝ ∞ (fun p : PolarPoint => T.M (T.radius p.1)) :=
    (hT.1 T.M (by simp)).comp_contDiff (hT.2.2.2.2.2.2.1.comp contDiff_fst)
      (fun p => (hT.2.2.2.2.2.2.2.1 p.1).1)
  exact (hM.pow c).continuous.mul
    (((spaces_contDiff_iteratedDeriv (spacesTraceBump_contDiff _ _) a).continuous.comp
      continuous_fst).mul (continuous_const.mul
        ((spaces_contDiff_iteratedDeriv (hf.1 m).1 b).continuous.comp continuous_snd)))

theorem spacesTracePacketJet_zero (γ : ℝ) (f : ℕ → ℝ → ℝ) (a b c m : ℕ)
    (p : PolarPoint) (hp : p.1 ∉ Icc (spaces_trace_center T m - spacesTraceRadius hD hT m)
      (spaces_trace_center T m + spacesTraceRadius hD hT m)) :
    spacesTracePacketJet hD hT γ f a b c m p = 0 := by
  rw [spacesTracePacketJet, spacesTraceBump_iteratedDeriv_zero (spacesTraceRadius_pos hD hT m) a hp,
    zero_mul, mul_zero]

/-- All radial derivative orders cost only one sample weight. The fixed
angular loss leaves an inverse sample weight for summation. -/
theorem spacesTracePacketJet_pointwise_bound :
    ∃ C : ℕ → ℕ → ℝ, (∀ a c, 0 ≤ C a c) ∧
      ∀ (γ : ℝ) (f : ℕ → ℝ → ℝ) (hf : CircleMember T γ f)
        (n m a b c : ℕ), b + c + 3 ≤ n → ∀ p : PolarPoint,
        |spacesTracePacketJet hD hT γ f a b c m p| ≤
          C a c * ((T.M (T.sample m))⁻¹ * ‖circleJetEncodeHilbert hf n m‖) := by
  obtain ⟨K, hK, hcompare⟩ := material_M_unit_window_comparison hT
  choose A hA hAbound using spacesTraceBump_derivative_bound
  choose B hB hBbound using spacesTraceRadius_inv_pow_bound hD hT
  let C (a c : ℕ) := Real.exp ((c : ℝ) * K) * (A a * B a) * anglePairEvaluationConstant
  have hC (a c : ℕ) : 0 ≤ C a c :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (hA a) (hB a).le))
      anglePairEvaluationConstant_nonneg
  refine ⟨C, hC, fun γ f hf n m a b c horder p => ?_⟩
  have hs := spaces_trace_sample_mem hD hT m
  have hM : 0 < T.M (T.sample m) := zero_lt_one.trans_le (hT.2.1 _ hs).2.2.2
  have hMp : 0 < T.M (T.radius p.1) :=
    zero_lt_one.trans_le (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2
  by_cases hp : p.1 ∈ Icc (spaces_trace_center T m - spacesTraceRadius hD hT m)
      (spaces_trace_center T m + spacesTraceRadius hD hT m)
  · have hdist : |p.1 - spaces_trace_center T m| ≤ 1 := by
      have hsmall : |p.1 - spaces_trace_center T m| ≤ spacesTraceRadius hD hT m :=
        abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
      exact hsmall.trans (spacesTraceRadius_le_one hD hT m)
    have hc : T.M (T.radius p.1) ^ c ≤
        Real.exp ((c : ℝ) * K) * T.M (T.sample m) ^ c := by
      have hr := hT.2.2.2.2.2.2.2.2.1 _ hs
      simpa only [Real.rpow_natCast, spaces_trace_center, hr] using
        hcompare (c : ℝ) (Nat.cast_nonneg c) p.1 (spaces_trace_center T m) hdist
    have ha : |iteratedDeriv a
        (spacesTraceBump (spaces_trace_center T m) (spacesTraceRadius hD hT m)) p.1| ≤
        (A a * B a) * T.M (T.sample m) := by
      calc
        _ ≤ A a * (spacesTraceRadius hD hT m)⁻¹ ^ a :=
          hAbound a _ _ (spacesTraceRadius_pos hD hT m) _
        _ ≤ A a * (B a * T.M (T.sample m)) := mul_le_mul_of_nonneg_left (hBbound a m) (hA a)
        _ = _ := (mul_assoc _ _ _).symm
    have hrow := spaces_circle_weighted_pointwise hf n m b (c + 2) (by omega) p.2
    let q := |T.H (T.sample m) ^ (-γ) * iteratedDeriv b (f m) p.2|
    have hrow' : T.M (T.sample m) ^ (c + 2) * q ≤
        anglePairEvaluationConstant * ‖circleJetEncodeHilbert hf n m‖ := by
      simpa only [q, mul_assoc, abs_mul, abs_of_nonneg (pow_nonneg hM.le (c + 2))] using hrow
    calc
      |spacesTracePacketJet hD hT γ f a b c m p| =
          T.M (T.radius p.1) ^ c *
            |iteratedDeriv a (spacesTraceBump (spaces_trace_center T m) (spacesTraceRadius hD hT m)) p.1| * q := by
        rw [spacesTracePacketJet, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hMp.le c)]
        exact (mul_assoc _ _ _).symm
      _ ≤ (Real.exp ((c : ℝ) * K) * T.M (T.sample m) ^ c) *
          ((A a * B a) * T.M (T.sample m)) * q :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc ha (abs_nonneg _)
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg hM.le _))) (abs_nonneg _)
      _ = (Real.exp ((c : ℝ) * K) * (A a * B a)) * (T.M (T.sample m))⁻¹ *
          (T.M (T.sample m) ^ (c + 2) * q) := by
        rw [pow_add]
        field_simp [hM.ne']
      _ ≤ (Real.exp ((c : ℝ) * K) * (A a * B a)) * (T.M (T.sample m))⁻¹ *
          (anglePairEvaluationConstant * ‖circleJetEncodeHilbert hf n m‖) :=
        mul_le_mul_of_nonneg_left hrow'
          (mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (hA a) (hB a).le))
            (inv_pos.mpr hM).le)
      _ = C a c * ((T.M (T.sample m))⁻¹ * ‖circleJetEncodeHilbert hf n m‖) := by
        dsimp only [C]
        ring
  · rw [spacesTracePacketJet_zero hD hT γ f a b c m p hp, abs_zero]
    exact mul_nonneg (hC a c) (mul_nonneg (inv_pos.mpr hM).le (norm_nonneg _))

/-- The actual locally finite packet sum belongs to every weighted L² jet
class. Its estimate loses three circle orders, independently of the radial
and angular derivative orders. -/
theorem spacesTraceMaterialExtension_jet_bound :
    ∃ C : ℕ → ℕ → ℝ, (∀ a c, 0 ≤ C a c) ∧
      ∀ (γ : ℝ) (f : ℕ → ℝ → ℝ) (_hf : CircleMember T γ f)
        (n a b c : ℕ), b + c + 3 ≤ n →
        MemLp (fun p : PolarPoint => T.M (T.radius p.1) ^ c *
          mixedDerivative a b (spacesTraceMaterialExtension hD hT γ f) p) 2 materialCylinderMeasure ∧
        (eLpNorm (fun p : PolarPoint => T.M (T.radius p.1) ^ c *
          mixedDerivative a b (spacesTraceMaterialExtension hD hT γ f) p)
          2 materialCylinderMeasure).toReal ≤ C a c * circleNorm T γ n f := by
  obtain ⟨C, hC, hpoint⟩ := spacesTracePacketJet_pointwise_bound hD hT
  let L := Real.sqrt (∑' m, ((T.M (T.sample m))⁻¹) ^ 2)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hw (m : ℕ) : 0 ≤ (T.M (T.sample m))⁻¹ :=
    inv_nonneg.mpr ((zero_lt_one.trans_le (hT.2.1 _ (spaces_trace_sample_mem hD hT m)).2.2.2).le)
  refine ⟨fun a c => (spacesTraceStripConstant * C a c) * L,
    fun a c => mul_nonneg (mul_nonneg spacesTraceStripConstant_nonneg (hC a c)) hL,
    fun γ f hf n a b c horder => ?_⟩
  let z := circleJetEncodeHilbert hf n
  have hrows := spaces_circle_weighted_row_summable hf n hw (spaces_trace_sample_inv_sq_summable hD hT)
  have hpack (m : ℕ) :
      MemLp (spacesTracePacketJet hD hT γ f a b c m) 2 materialCylinderMeasure ∧
      (eLpNorm (spacesTracePacketJet hD hT γ f a b c m) 2 materialCylinderMeasure).toReal ≤
        (spacesTraceStripConstant * C a c) * ((T.M (T.sample m))⁻¹ * ‖z m‖) := by
    have h := spaces_memLp_norm_le_of_unit_radial_support
      (spacesTracePacketJet_continuous hD hT hf a b c m).aestronglyMeasurable
      (spaces_trace_center T m)
      (mul_nonneg (hC a c) (mul_nonneg (hw m) (norm_nonneg _)))
      (hpoint γ f hf n m a b c horder) (fun p hp => ?_)
    · exact ⟨h.1, by simpa only [mul_assoc] using h.2⟩
    · apply spacesTracePacketJet_zero hD hT γ f a b c m p
      intro hp'
      apply hp
      have hr := spacesTraceRadius_le_one hD hT m
      exact ⟨by linarith [hp'.1], by linarith [hp'.2]⟩
  have hmajor : Summable (fun m =>
      (spacesTraceStripConstant * C a c) * ((T.M (T.sample m))⁻¹ * ‖z m‖)) :=
    hrows.1.mul_left _
  have hsum : Summable (fun m =>
      (eLpNorm (spacesTracePacketJet hD hT γ f a b c m) 2 materialCylinderMeasure).toReal) :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) (fun m => (hpack m).2) hmajor
  have hseries := spaces_memLp_tsum_of_summable_norm
    (spacesTracePacketJet hD hT γ f a b c) (fun m => (hpack m).1) hsum
  have he : (fun p : PolarPoint => T.M (T.radius p.1) ^ c *
      mixedDerivative a b (spacesTraceMaterialExtension hD hT γ f) p) =
      fun p => ∑' m, spacesTracePacketJet hD hT γ f a b c m p :=
    funext (spacesTraceMaterialExtension_weighted_mixedDerivative hD hT hf a b c)
  rw [he]
  refine ⟨hseries.1, hseries.2.trans ?_⟩
  calc
    (∑' m, (eLpNorm (spacesTracePacketJet hD hT γ f a b c m) 2 materialCylinderMeasure).toReal) ≤
        ∑' m, (spacesTraceStripConstant * C a c) * ((T.M (T.sample m))⁻¹ * ‖z m‖) :=
      Summable.tsum_le_tsum (fun m => (hpack m).2) hsum hmajor
    _ = (spacesTraceStripConstant * C a c) * (∑' m, (T.M (T.sample m))⁻¹ * ‖z m‖) := tsum_mul_left
    _ ≤ (spacesTraceStripConstant * C a c) * (L * circleNorm T γ n f) :=
      mul_le_mul_of_nonneg_left hrows.2 (mul_nonneg spacesTraceStripConstant_nonneg (hC a c))
    _ = ((spacesTraceStripConstant * C a c) * L) * circleNorm T γ n f := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Statements
