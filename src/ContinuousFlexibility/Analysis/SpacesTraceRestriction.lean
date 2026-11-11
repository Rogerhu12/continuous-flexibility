import ContinuousFlexibility.Analysis.SpacesTracePointwise
import ContinuousFlexibility.Analysis.CircleJetEncoding

/-!
# Restriction to all sample circles

Weighted pointwise bounds and the summable inverse sample weights make
restriction to the complete family of sample circles a map into the actual
weighted circle class. Its grading estimate has one fixed loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem spaces_trace_sample_mem {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (m : ℕ) :
    T.sample m ∈ Ioo D.a D.b := by
  obtain ⟨_, hprofile⟩ := hD
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _⟩ := hT
  exact hprofile.2.1.2.2.2.1 m (hsample m)

def spacesTraceFunction (T : MaterialData) (f : PolarPoint → ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  f (T.sample m, θ)

theorem spacesTraceFunction_contDiff {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (m : ℕ) :
    ContDiff ℝ ∞ (spacesTraceFunction T f m) :=
  hf.1.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun θ => ⟨spaces_trace_sample_mem hD hT m, mem_univ θ⟩)

theorem spacesTraceFunction_periodic {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (m : ℕ) :
    Function.Periodic (spacesTraceFunction T f m) Real.pi := by
  intro θ
  change f (T.sample m, θ + Real.pi) = f (T.sample m, θ)
  have h := hf.2.2.1 (T.sample m, θ)
  change f (T.sample m + 0, θ + Real.pi) = f (T.sample m, θ) at h
  simpa only [add_zero] using h

theorem spacesTraceFunction_normalized_derivative {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (γ : ℝ) (f : PolarPoint → ℝ) (m b : ℕ) (θ : ℝ) :
    T.H (T.sample m) ^ (-γ) * iteratedDeriv b (spacesTraceFunction T f m) θ =
      mixedDerivative 0 b (materialPullback T γ f) (spaces_trace_center T m, θ) := by
  have hr := hT.2.2.2.2.2.2.2.2.1 _ (spaces_trace_sample_mem hD hT m)
  change T.H (T.sample m) ^ (-γ) * iteratedDeriv b (fun t => f (T.sample m, t)) θ = _
  simp only [mixedDerivative, iteratedDeriv_zero, materialPullback, spaces_trace_center,
    hr, iteratedDeriv_const_mul_field]

/-- Every weighted angular jet of the trace has a common pointwise bound
at a fixed output order, with one inverse sample weight left for summation. -/
theorem spaces_trace_jet_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : ℝ) (f : PolarPoint → ℝ), HeightMember D T γ f →
      ∀ s m : ℕ, ∀ j : CircleJetIndex s, ∀ θ : ℝ,
        |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
            iteratedDeriv (j.val 0).val (spacesTraceFunction T f m) θ| ≤
          ((4 * Real.sqrt Real.pi * Real.exp (((s + 1 : ℕ) : ℝ) * K)) *
            physicalNorm T γ (s + 3) f) * (T.M (T.sample m))⁻¹ := by
  obtain ⟨K, hK, hbound⟩ := spaces_weighted_mixed_pointwise hT
  refine ⟨K, hK, fun γ f hf s m j θ => ?_⟩
  have hj := j.property
  have hs := spaces_trace_sample_mem hD hT m
  have hM : 0 < T.M (T.sample m) := zero_lt_one.trans_le (hT.2.1 _ hs).2.2.2
  have hr := hT.2.2.2.2.2.2.2.2.1 _ hs
  have hb := hbound γ f hf 0 (j.val 0).val ((j.val 1).val + 1) (s + 3)
    (by omega) (spaces_trace_center T m, θ)
  rw [← spacesTraceFunction_normalized_derivative hD hT γ f m (j.val 0).val θ] at hb
  simp only [spaces_trace_center, hr] at hb
  have he : Real.exp ((((j.val 1).val + 1 : ℕ) : ℝ) * K) ≤
      Real.exp (((s + 1 : ℕ) : ℝ) * K) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hK
    exact_mod_cast (show (j.val 1).val + 1 ≤ s + 1 by omega)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by positivity)) (Real.sqrt_nonneg _))
  calc
    |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val (spacesTraceFunction T f m) θ| =
      T.M (T.sample m) ^ (j.val 1).val *
        |T.H (T.sample m) ^ (-γ) * iteratedDeriv (j.val 0).val (spacesTraceFunction T f m) θ| := by
      rw [mul_assoc, abs_mul, abs_of_nonneg (pow_nonneg hM.le _)]
    _ = (T.M (T.sample m))⁻¹ *
        (T.M (T.sample m) ^ ((j.val 1).val + 1) *
          |T.H (T.sample m) ^ (-γ) * iteratedDeriv (j.val 0).val (spacesTraceFunction T f m) θ|) := by
      rw [pow_succ]
      field_simp [hM.ne']
    _ ≤ (T.M (T.sample m))⁻¹ *
        ((4 * Real.sqrt Real.pi * Real.exp (((s + 1 : ℕ) : ℝ) * K)) *
          physicalNorm T γ (s + 3) f) := mul_le_mul_of_nonneg_left hb' (inv_pos.mpr hM).le
    _ = _ := mul_comm _ _

private theorem spaces_angle_one_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure := by
  simpa only [iteratedDeriv_zero] using
    memLp_angleMeasure_iteratedDeriv_of_contDiff
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ))) 0

def spacesAngleL2Constant : ℝ := (eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure).toReal

theorem spacesAngleL2Constant_nonneg : 0 ≤ spacesAngleL2Constant := ENNReal.toReal_nonneg

theorem spaces_angle_norm_le_of_abs_le {f : ℝ → ℝ} (hf : AEStronglyMeasurable f angleMeasure)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ θ, |f θ| ≤ C) :
    (eLpNorm f 2 angleMeasure).toReal ≤ spacesAngleL2Constant * C := by
  have he : eLpNorm f 2 angleMeasure ≤ eLpNorm (fun _ : ℝ => C) 2 angleMeasure :=
    eLpNorm_mono hf (fun θ => by simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using hbound θ)
  have heq : (fun _ : ℝ => C) = C • (fun _ : ℝ => (1 : ℝ)) := by ext; simp
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hC] at he
  have hfin : ENNReal.ofReal C * eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top spaces_angle_one_memLp.eLpNorm_ne_top
  simpa only [spacesAngleL2Constant, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, mul_comm] using
    ENNReal.toReal_mono hfin he

private theorem spaces_circle_jet_energy_eq {T : MaterialData} {γ : ℝ}
    {v : ℕ → ℝ → ℝ} (hv : ∀ m, ContDiff ℝ ∞ (v m)) (m : ℕ) {s : ℕ} (j : CircleJetIndex s) :
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 =
    ENNReal.ofReal ((eLpNorm
      (fun θ => (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val (v m) θ) 2 angleMeasure).toReal ^ 2) := by
  let c := T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)
  let g := iteratedDeriv (j.val 0).val (v m)
  have hm : MemLp (c • g) 2 angleMeasure :=
    (memLp_angleMeasure_iteratedDeriv_of_contDiff (hv m) (j.val 0).val).const_smul c
  change ENNReal.ofReal (c ^ 2) * eLpNorm g 2 angleMeasure ^ 2 =
    ENNReal.ofReal ((eLpNorm (c • g) 2 angleMeasure).toReal ^ 2)
  symm
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hm.eLpNorm_ne_top,
    eLpNorm_const_smul, mul_pow, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg c), sq_abs]

private theorem spaces_circle_energy_le_of_weighted_bound
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (hv : ∀ m, ContDiff ℝ ∞ (v m)) (s : ℕ)
    {A : ℝ} (hA : 0 ≤ A) {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m)
    (hwsum : Summable (fun m => w m ^ 2))
    (hbound : ∀ m, ∀ j : CircleJetIndex s, ∀ θ,
      |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val (v m) θ| ≤ A * w m) :
    (∑' m, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2) ≤
      ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) *
        (spacesAngleL2Constant * A) ^ 2 * ∑' m, w m ^ 2) := by
  have hjet (m : ℕ) (j : CircleJetIndex s) :
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 ≤
        ENNReal.ofReal (((spacesAngleL2Constant * A) * w m) ^ 2) := by
    rw [spaces_circle_jet_energy_eq hv]
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ ENNReal.toReal_nonneg _ 2
    have hm : AEStronglyMeasurable
        (fun θ => (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
          iteratedDeriv (j.val 0).val (v m) θ) angleMeasure :=
      (continuous_const.mul ((hv m).continuous_iteratedDeriv (j.val 0).val (by simp))).aestronglyMeasurable
    simpa only [mul_assoc] using spaces_angle_norm_le_of_abs_le hm (mul_nonneg hA (hw m)) (hbound m j)
  let R : ℝ := (Fintype.card (CircleJetIndex s) : ℝ) * (spacesAngleL2Constant * A) ^ 2
  have hR : 0 ≤ R := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hrow (m : ℕ) :
      (∑ j : CircleJetIndex s,
        ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2) ≤
        ENNReal.ofReal (R * w m ^ 2) := by
    calc
      _ ≤ ∑ _j : CircleJetIndex s, ENNReal.ofReal (((spacesAngleL2Constant * A) * w m) ^ 2) :=
        Finset.sum_le_sum (fun j _ => hjet m j)
      _ = ENNReal.ofReal (∑ _j : CircleJetIndex s, ((spacesAngleL2Constant * A) * w m) ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
      _ = _ := by
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R, mul_pow, mul_assoc]
  calc
    _ ≤ ∑' m, ENNReal.ofReal (R * w m ^ 2) := ENNReal.tsum_le_tsum hrow
    _ = ENNReal.ofReal (∑' m, R * w m ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg hR (sq_nonneg _)) (hwsum.mul_left R)).symm
    _ = _ := by rw [tsum_mul_left]

private theorem spaces_circleNorm_le_of_weighted_bound
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (hv : ∀ m, ContDiff ℝ ∞ (v m)) (s : ℕ)
    {A : ℝ} (hA : 0 ≤ A) {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m)
    (hwsum : Summable (fun m => w m ^ 2))
    (hbound : ∀ m, ∀ j : CircleJetIndex s, ∀ θ,
      |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val (v m) θ| ≤ A * w m) :
    circleNorm T γ s v ≤
      Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * ∑' m, w m ^ 2) *
        (spacesAngleL2Constant * A) := by
  have hsum : 0 ≤ ∑' m, w m ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
  have hbase : 0 ≤ (Fintype.card (CircleJetIndex s) : ℝ) * ∑' m, w m ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) hsum
  have henergy := spaces_circle_energy_le_of_weighted_bound hv s hA hw hwsum hbound
  have hre := ENNReal.toReal_mono ENNReal.ofReal_ne_top henergy
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hsum)] at hre
  unfold circleNorm
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg spacesAngleL2Constant_nonneg hA), ?_⟩
  calc
    _ ≤ (Fintype.card (CircleJetIndex s) : ℝ) * (spacesAngleL2Constant * A) ^ 2 *
        ∑' m, w m ^ 2 := hre
    _ = _ := by simp only [mul_pow, Real.sq_sqrt hbase]; ring

/-- Restriction belongs to the exact circle class, with a uniform loss of
three orders in the physical grading. The constants do not depend on the
height exponent or on the height being restricted. -/
theorem spaces_trace_circleMember_and_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (γ : ℝ) (f : PolarPoint → ℝ), HeightMember D T γ f →
        CircleMember T γ (spacesTraceFunction T f) ∧
        ∀ s, circleNorm T γ s (spacesTraceFunction T f) ≤ C s * physicalNorm T γ (s + 3) f := by
  obtain ⟨K, hK, hjet⟩ := spaces_trace_jet_bound hD hT
  let w : ℕ → ℝ := fun m => (T.M (T.sample m))⁻¹
  have hw (m : ℕ) : 0 ≤ w m := inv_nonneg.mpr
    (zero_le_one.trans (hT.2.1 _ (spaces_trace_sample_mem hD hT m)).2.2.2)
  have hsum : Summable (fun m => w m ^ 2) := spaces_trace_sample_inv_sq_summable hD hT
  let A : ℕ → ℝ := fun s => 4 * Real.sqrt Real.pi * Real.exp (((s + 1 : ℕ) : ℝ) * K)
  have hA (s : ℕ) : 0 ≤ A s := by dsimp only [A]; positivity
  let C : ℕ → ℝ := fun s =>
    Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * ∑' m, w m ^ 2) *
      spacesAngleL2Constant * A s
  have hC (s : ℕ) : 0 ≤ C s :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) spacesAngleL2Constant_nonneg) (hA s)
  refine ⟨C, hC, fun γ f hf => ?_⟩
  have htrace (m : ℕ) : ContDiff ℝ ∞ (spacesTraceFunction T f m) :=
    spacesTraceFunction_contDiff hD hT hf m
  have hbound (s : ℕ) := hjet γ f hf s
  have hn (s : ℕ) : 0 ≤ A s * physicalNorm T γ (s + 3) f :=
    mul_nonneg (hA s) (Real.sqrt_nonneg _)
  constructor
  · refine ⟨fun m => ⟨htrace m, spacesTraceFunction_periodic hf m⟩,
      fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (htrace m) b, fun s => ?_⟩
    exact (spaces_circle_energy_le_of_weighted_bound htrace s (hn s) hw hsum (hbound s)).trans_lt
      ENNReal.ofReal_lt_top
  · intro s
    exact (spaces_circleNorm_le_of_weighted_bound htrace s (hn s) hw hsum (hbound s)).trans_eq
      (by dsimp only [C]; ring)

section Models

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ}
  {H : SobolevModelData} {C : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hH : IsSobolevModel D T γ H) (hC : IsCircleModel T γ C)

include hD hT hH hC in
private theorem spacesTraceCircle_exists (u : H.Space) :
    ∃ v : C.Space, C.decode v = spacesTraceFunction T (H.decode u) := by
  obtain ⟨_, _, htrace⟩ := spaces_trace_circleMember_and_bound hD hT
  exact hC.2.2.2.2.1 _ (htrace γ (H.decode u) (hH.2.2.2.1 u)).1

def spacesTraceCircleFun (u : H.Space) : C.Space :=
  Classical.choose (spacesTraceCircle_exists hD hT hH hC u)

theorem spacesTraceCircleFun_decode (u : H.Space) :
    C.decode (spacesTraceCircleFun hD hT hH hC u) = spacesTraceFunction T (H.decode u) :=
  Classical.choose_spec (spacesTraceCircle_exists hD hT hH hC u)

theorem spacesTraceCircleFun_add (u v : H.Space) :
    spacesTraceCircleFun hD hT hH hC (u + v) =
      spacesTraceCircleFun hD hT hH hC u + spacesTraceCircleFun hD hT hH hC v := by
  apply hC.2.2.2.2.2.1
  calc
    C.decode (spacesTraceCircleFun hD hT hH hC (u + v)) =
        spacesTraceFunction T (H.decode (u + v)) := spacesTraceCircleFun_decode hD hT hH hC _
    _ = spacesTraceFunction T (H.decode u) + spacesTraceFunction T (H.decode v) := by
      funext m θ
      change H.decode (u + v) (T.sample m, θ) =
        H.decode u (T.sample m, θ) + H.decode v (T.sample m, θ)
      exact congrFun (H.decode.map_add u v) (T.sample m, θ)
    _ = C.decode (spacesTraceCircleFun hD hT hH hC u) +
        C.decode (spacesTraceCircleFun hD hT hH hC v) :=
      congrArg₂ (fun f g : ℕ → ℝ → ℝ => f + g)
        (spacesTraceCircleFun_decode hD hT hH hC u).symm
        (spacesTraceCircleFun_decode hD hT hH hC v).symm
    _ = _ := (C.decode.map_add _ _).symm

theorem spacesTraceCircleFun_smul (c : ℝ) (u : H.Space) :
    spacesTraceCircleFun hD hT hH hC (c • u) = c • spacesTraceCircleFun hD hT hH hC u := by
  apply hC.2.2.2.2.2.1
  calc
    C.decode (spacesTraceCircleFun hD hT hH hC (c • u)) =
        spacesTraceFunction T (H.decode (c • u)) := spacesTraceCircleFun_decode hD hT hH hC _
    _ = c • spacesTraceFunction T (H.decode u) := by
      funext m θ
      change H.decode (c • u) (T.sample m, θ) = c • H.decode u (T.sample m, θ)
      exact congrFun (H.decode.map_smul c u) (T.sample m, θ)
    _ = c • C.decode (spacesTraceCircleFun hD hT hH hC u) :=
      congrArg (fun f : ℕ → ℝ → ℝ => c • f) (spacesTraceCircleFun_decode hD hT hH hC u).symm
    _ = _ := (C.decode.map_smul c _).symm

def spacesTraceCircleLinear : H.Space →ₗ[ℝ] C.Space where
  toFun := spacesTraceCircleFun hD hT hH hC
  map_add' := spacesTraceCircleFun_add hD hT hH hC
  map_smul' := spacesTraceCircleFun_smul hD hT hH hC

theorem spacesTraceCircleLinear_decode (u : H.Space) :
    C.decode (spacesTraceCircleLinear hD hT hH hC u) = spacesTraceFunction T (H.decode u) :=
  spacesTraceCircleFun_decode hD hT hH hC u

theorem spacesTraceCircleLinear_isTame :
    IsTameLinear H.grading C.grading (spacesTraceCircleLinear hD hT hH hC) 3 0 := by
  obtain ⟨constants, hnonneg, hbound⟩ := spaces_trace_circleMember_and_bound hD hT
  intro s _
  have hsum : 0 ≤ ∑ i ∈ Finset.Iic s, constants i :=
    Finset.sum_nonneg (fun i _ => hnonneg i)
  refine ⟨⟨∑ i ∈ Finset.Iic s, constants i, hsum⟩, fun u => ?_⟩
  apply (gradedSeminorm_le_iff _ _ s _ (mul_nonneg hsum (apply_nonneg _ _))).mpr
  intro i hi
  have hn := (hbound γ (H.decode u) (hH.2.2.2.1 u)).2 i
  rw [← hH.2.2.2.2.2.2.2 u (i + 3)] at hn
  have hCi : constants i ≤ ∑ j ∈ Finset.Iic s, constants j :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_Iic.mpr hi)
  calc
    ‖(spacesTraceCircleLinear hD hT hH hC u).val i‖ =
        circleNorm T γ i (spacesTraceFunction T (H.decode u)) := by
      rw [hC.2.2.2.2.2.2.2, spacesTraceCircleLinear_decode]
    _ ≤ constants i * ‖u.val (i + 3)‖ := hn
    _ ≤ (∑ j ∈ Finset.Iic s, constants j) * H.grading (s + 3) u :=
      mul_le_mul hCi (norm_coordinate_le_graded _ _ (by omega) u) (norm_nonneg _) hsum

/-- Restriction to all sample circles as an actual continuous linear map. -/
def spacesTraceCircleMap : H.Space →L[ℝ] C.Space :=
  (spacesTraceCircleLinear_isTame hD hT hH hC).toContinuousLinearMap
    (withSeminorms_graded _ _) (withSeminorms_graded _ _) (gradedSeminorm_monotone _ _)

theorem spacesTraceCircleMap_decode (u : H.Space) (m : ℕ) (θ : ℝ) :
    C.decode (spacesTraceCircleMap hD hT hH hC u) m θ = H.decode u (T.sample m, θ) :=
  congrFun (congrFun (spacesTraceCircleLinear_decode hD hT hH hC u) m) θ

theorem spacesTraceCircleMap_isTame :
    IsTameLinear H.grading C.grading (spacesTraceCircleMap hD hT hH hC).toLinearMap 3 0 :=
  spacesTraceCircleLinear_isTame hD hT hH hC

end Models

/-- The trace lands in the even circle subspace required in W02. -/
def spacesEvenTrace {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hH : IsSobolevModel D T γ (S.height γ)) (hC : IsCircleModel T γ (S.circle γ)) :
    (S.height γ).Space →L[ℝ] EvenCircleAt S γ :=
  (spacesTraceCircleMap hD hT hH hC).codRestrict (evenCircleSubmoduleAt S γ) (by
    intro u m θ
    rw [spacesTraceCircleMap_decode, spacesTraceCircleMap_decode]
    exact (hH.2.2.2.1 u).2.1 (T.sample m) θ)

theorem spacesEvenTrace_decode {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hH : IsSobolevModel D T γ (S.height γ)) (hC : IsCircleModel T γ (S.circle γ))
    (u : (S.height γ).Space) (m : ℕ) (θ : ℝ) :
    (S.circle γ).decode (spacesEvenTrace hD hT hH hC u).val m θ =
      (S.height γ).decode u (T.sample m, θ) :=
  spacesTraceCircleMap_decode hD hT hH hC u m θ

theorem spacesEvenTrace_isTame {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hH : IsSobolevModel D T γ (S.height γ)) (hC : IsCircleModel T γ (S.circle γ)) :
    IsTameLinear (S.height γ).grading (evenCircleGradingAt S γ)
      (spacesEvenTrace hD hT hH hC).toLinearMap 3 0 :=
  spacesTraceCircleMap_isTame hD hT hH hC

end ContinuousFlexibility.Statements
