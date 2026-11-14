module

public import ContinuousFlexibility.Analysis.CircleJetEvaluation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace ContinuousFlexibility.Statements

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem angle_iteratedDeriv_periodic {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (b : ℕ) :
    Function.Periodic (iteratedDeriv b f) Real.pi := by
  intro x
  have hshift : (fun t : ℝ => f (t + Real.pi)) = f := funext hp
  have h := congrFun (iteratedDeriv_comp_add_const b f Real.pi) x
  rw [hshift] at h
  exact h.symm

private theorem contDiff_angle_iteratedDeriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : ℕ) : ContDiff ℝ ∞ (iteratedDeriv b f) := by
  induction b with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ b ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

private theorem integral_angle_periodic_deriv_mul {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hfp : Function.Periodic f Real.pi) (hφp : Function.Periodic φ Real.pi) :
    (∫ x, deriv f x * φ x ∂angleMeasure) = -(∫ x, f x * deriv φ x ∂angleMeasure) := by
  have hfend : f Real.pi = f 0 := by simpa only [zero_add] using hfp 0
  have hφend : φ Real.pi = φ 0 := by simpa only [zero_add] using hφp 0
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := Real.pi)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hf).2.continuous.intervalIntegrable 0 Real.pi)
    ((contDiff_infty_iff_deriv.mp hφ).2.continuous.intervalIntegrable 0 Real.pi)
  simp only [hfend, hφend, sub_self, zero_sub,
    intervalIntegral.integral_of_le Real.pi_pos.le] at hIBP
  change (∫ x in Ioc (0 : ℝ) Real.pi, deriv f x * φ x) =
    -(∫ x in Ioc (0 : ℝ) Real.pi, f x * deriv φ x)
  linarith

theorem integral_angle_iteratedDeriv_mul {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfp : Function.Periodic f Real.pi) (b : ℕ)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ Real.pi) :
    (∫ x, iteratedDeriv b f x * φ x ∂angleMeasure) =
      (-1 : ℝ) ^ b * ∫ x, f x * iteratedDeriv b φ x ∂angleMeasure := by
  induction b generalizing φ with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ b ih =>
    have hφder : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have hφderp : Function.Periodic (deriv φ) Real.pi := by
      simpa only [iteratedDeriv_one] using angle_iteratedDeriv_periodic hφp 1
    calc
      (∫ x, iteratedDeriv (b + 1) f x * φ x ∂angleMeasure) =
          -(∫ x, iteratedDeriv b f x * deriv φ x ∂angleMeasure) := by
        rw [iteratedDeriv_succ]
        exact integral_angle_periodic_deriv_mul (contDiff_angle_iteratedDeriv hf b) hφ
          (angle_iteratedDeriv_periodic hfp b) hφp
      _ = -((-1 : ℝ) ^ b * ∫ x, f x * iteratedDeriv b (deriv φ) x ∂angleMeasure) :=
        congrArg Neg.neg (ih hφder hφderp)
      _ = _ := by
        rw [iteratedDeriv_succ', pow_succ]
        ring

theorem hasWeakAngularDerivative_toLp_iteratedDeriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (b : ℕ)
    (h₀ : MemLp f 2 angleMeasure) (hb : MemLp (iteratedDeriv b f) 2 angleMeasure) :
    HasWeakAngularDerivative (h₀.toLp f) (hb.toLp (iteratedDeriv b f)) b := by
  intro φ hφ hφp
  have hleft : (∫ x, hb.toLp (iteratedDeriv b f) x * φ x ∂angleMeasure) =
      ∫ x, iteratedDeriv b f x * φ x ∂angleMeasure := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hb] with x hx
    rw [hx]
  have hright : (∫ x, h₀.toLp f x * iteratedDeriv b φ x ∂angleMeasure) =
      ∫ x, f x * iteratedDeriv b φ x ∂angleMeasure := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp h₀] with x hx
    rw [hx]
  rw [hleft, hright]
  exact integral_angle_iteratedDeriv_mul hf hp b hφ hφp

variable {T : MaterialData} {γ : ℝ} {f : ℕ → ℝ → ℝ}

private def circleJetEncodedFunction (T : MaterialData) (γ : ℝ) (f : ℕ → ℝ → ℝ)
    (m : ℕ) {s : ℕ} (j : CircleJetIndex s) (x : ℝ) : ℝ :=
  (circleJetWeight T m j * T.H (T.sample m) ^ (-γ)) * iteratedDeriv (j.val 0).val (f m) x

private theorem memLp_circleJetEncodedFunction (hf : CircleMember T γ f)
    (m : ℕ) {s : ℕ} (j : CircleJetIndex s) :
    MemLp (circleJetEncodedFunction T γ f m j) 2 angleMeasure :=
  (hf.2.1 m (j.val 0).val).const_smul (circleJetWeight T m j * T.H (T.sample m) ^ (-γ))

private def circleJetEncodedCoordinate (hf : CircleMember T γ f)
    (m : ℕ) {s : ℕ} (j : CircleJetIndex s) : AngleL2 :=
  (memLp_circleJetEncodedFunction hf m j).toLp (circleJetEncodedFunction T γ f m j)

private theorem circleJetEncodedCoordinate_ae (hf : CircleMember T γ f)
    (m : ℕ) {s : ℕ} (j : CircleJetIndex s) :
    (⇑(circleJetEncodedCoordinate hf m j)) =ᵐ[angleMeasure] circleJetEncodedFunction T γ f m j :=
  MemLp.coeFn_toLp (memLp_circleJetEncodedFunction hf m j)

private def circleJetEncodedRow (hf : CircleMember T γ f) (s m : ℕ) :
    PiLp 2 (fun _ : CircleJetIndex s => AngleL2) :=
  WithLp.toLp 2 (fun j => circleJetEncodedCoordinate hf m j)

private def circleJetCellEnergy (T : MaterialData) (γ : ℝ) (f : ℕ → ℝ → ℝ)
    (s m : ℕ) : ℝ≥0∞ :=
  ∑ j : CircleJetIndex s,
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (f m)) 2 angleMeasure ^ 2

private theorem circleJetEncodedRow_energy_eq (hf : CircleMember T γ f) (s m : ℕ) :
    ENNReal.ofReal (‖circleJetEncodedRow hf s m‖ ^ 2) = circleJetCellEnergy T γ f s m := by
  rw [PiLp.norm_sq_eq_of_L2, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  unfold circleJetCellEnergy
  apply Finset.sum_congr rfl
  intro j _
  let c := circleJetWeight T m j * T.H (T.sample m) ^ (-γ)
  let g := iteratedDeriv (j.val 0).val (f m)
  change ENNReal.ofReal (‖circleJetEncodedCoordinate hf m j‖ ^ 2) =
    ENNReal.ofReal (c ^ 2) * eLpNorm g 2 angleMeasure ^ 2
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae (circleJetEncodedCoordinate_ae hf m j)]
  change eLpNorm (c • g) 2 angleMeasure ^ 2 = _
  rw [eLpNorm_const_smul, mul_pow, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg c), sq_abs]

private theorem summable_circleJetEncodedRow (hf : CircleMember T γ f) (s : ℕ) :
    Summable (fun m : ℕ => ‖circleJetEncodedRow hf s m‖ ^ 2) := by
  have hsum : (∑' m : ℕ, circleJetCellEnergy T γ f s m) < (⊤ : ℝ≥0∞) := hf.2.2 s
  simpa only [← circleJetEncodedRow_energy_eq hf s, ENNReal.toReal_ofReal (sq_nonneg _)] using
    ENNReal.summable_toReal hsum.ne

/-- The actual weighted square-summable jets of a smooth periodic sequence. -/
def circleJetEncodeHilbert (hf : CircleMember T γ f) (s : ℕ) : CircleJetHilbert s :=
  ⟨circleJetEncodedRow hf s, memℓp_gen (by
    have hpow (x : ℝ) : x ^ (2 : ℝ≥0∞).toReal = x ^ (2 : ℕ) := by norm_cast
    simpa only [hpow] using summable_circleJetEncodedRow hf s)⟩

theorem circleJetEncodeHilbert_ae (hf : CircleMember T γ f) (s m : ℕ) (j : CircleJetIndex s) :
    (⇑(circleJetEncodeHilbert hf s m j)) =ᵐ[angleMeasure]
      fun x => (circleJetWeight T m j * T.H (T.sample m) ^ (-γ)) * iteratedDeriv (j.val 0).val (f m) x :=
  circleJetEncodedCoordinate_ae hf m j

theorem circleJetEncodeHilbert_norm (hf : CircleMember T γ f) (s : ℕ) :
    ‖circleJetEncodeHilbert hf s‖ = circleNorm T γ s f := by
  have he : (∑' m, circleJetCellEnergy T γ f s m) =
      ENNReal.ofReal (‖circleJetEncodeHilbert hf s‖ ^ 2) := by
    rw [circleJetHilbert_norm_sq,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (circleJetHilbert_summable_sq _)]
    apply tsum_congr
    intro m
    exact (circleJetEncodedRow_energy_eq hf s m).symm
  change ‖circleJetEncodeHilbert hf s‖ = Real.sqrt ((∑' m, circleJetCellEnergy T γ f s m).toReal)
  rw [he, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem circleJetEncodeHilbert_zero_ae (hf : CircleMember T γ f) (s m : ℕ) :
    (⇑(circleJetEncodeHilbert hf s m (zeroCircleJetIndex s))) =ᵐ[angleMeasure]
      fun x => T.H (T.sample m) ^ (-γ) * f m x := by
  simpa [circleJetWeight, zeroCircleJetIndex] using
    circleJetEncodeHilbert_ae hf s m (zeroCircleJetIndex s)

theorem circleJetEncodeHilbert_mem_graph (hf : CircleMember T γ f) (s : ℕ) :
    circleJetEncodeHilbert hf s ∈ circleJetGraph T s := by
  intro m j
  let c := T.H (T.sample m) ^ (-γ)
  let g : ℝ → ℝ := fun x => c * f m x
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul (hf.1 m).1
  have hgp : Function.Periodic g Real.pi := by
    intro x
    exact congrArg (c * ·) ((hf.1 m).2 x)
  let b := (j.val 0).val
  have h₀ := memLp_angleMeasure_of_continuous hg.continuous
  have hb := memLp_angleMeasure_iteratedDeriv_of_contDiff hg b
  let d := hb.toLp (iteratedDeriv b g)
  have hbase : circleJetEncodeHilbert hf s m (zeroCircleJetIndex s) = h₀.toLp g := by
    apply Lp.ext
    exact (circleJetEncodeHilbert_zero_ae hf s m).trans (MemLp.coeFn_toLp h₀).symm
  refine ⟨d, ?_, ?_⟩
  · rw [hbase]
    exact hasWeakAngularDerivative_toLp_iteratedDeriv hg hgp b h₀ hb
  · filter_upwards [circleJetEncodeHilbert_ae hf s m j, MemLp.coeFn_toLp hb] with x hx hd
    change circleJetEncodeHilbert hf s m j x = circleJetWeight T m j * d x
    change d x = iteratedDeriv b (fun y => c * f m y) x at hd
    rw [hx, hd, iteratedDeriv_const_mul_field]
    exact mul_assoc _ _ _

variable (hM : ∀ m, 0 < T.M (T.sample m))

def circleJetEncodeLevel (hf : CircleMember T γ f) (s : ℕ) : circleJetClosedSubmodule T s :=
  ⟨circleJetEncodeHilbert hf s, by
    rw [← SetLike.mem_coe, circleJetClosedSubmodule_carrier hM]
    exact circleJetEncodeHilbert_mem_graph hf s⟩

/-- Encoding in the genuine projective carrier. The lower level is
the literal restriction of the higher one. -/
def circleJetEncode (hf : CircleMember T γ f) : CircleJetProjectiveLimit T hM :=
  ⟨circleJetEncodeLevel hM hf, by
    intro s
    apply Subtype.ext
    apply lp.ext
    funext m
    apply (WithLp.ext_iff 2).mpr
    funext j
    apply Lp.ext
    change (⇑(circleJetHilbertRestrict (Nat.le_succ s) (circleJetEncodeHilbert hf (s + 1)) m j))
      =ᵐ[angleMeasure] (⇑(circleJetEncodeHilbert hf s m j))
    rw [circleJetHilbertRestrict_apply]
    apply (circleJetEncodeHilbert_ae hf (s + 1) m (circleJetIndexOfLE (Nat.le_succ s) j)).trans
    simpa only [circleJetWeight, circleJetIndexOfLE_val] using
      (circleJetEncodeHilbert_ae hf s m j).symm⟩

theorem circleJetDecoded_encode (hH : ∀ m, 0 < T.H (T.sample m)) (hf : CircleMember T γ f) :
    circleJetDecoded (circleJetEncode hM hf) γ = f := by
  funext m
  let u := circleJetEncode hM hf
  have hu := circleJetDecoded_zero_ae hH u γ 0 m
  have hv := circleJetEncodeHilbert_zero_ae hf 0 m
  have hweighted : (fun x => T.H (T.sample m) ^ (-γ) * circleJetDecoded u γ m x)
      =ᵐ[angleMeasure] (fun x => T.H (T.sample m) ^ (-γ) * f m x) := hu.symm.trans hv
  have hn : T.H (T.sample m) ^ (-γ) ≠ 0 := (Real.rpow_pos_of_pos (hH m) _).ne'
  have hae : circleJetDecoded u γ m =ᵐ[angleMeasure] f m :=
    hweighted.mono fun _ hx => mul_left_cancel₀ hn hx
  exact angle_periodic_eq_of_ae_eq (circleJetDecoded_contDiff u γ m).continuous
    (hf.1 m).1.continuous (circleJetDecoded_periodic u γ m) (hf.1 m).2 hae

theorem circleJetDecoded_injective (hH : ∀ m, 0 < T.H (T.sample m)) (γ : ℝ) :
    Function.Injective (fun u : CircleJetProjectiveLimit T hM => circleJetDecoded u γ) := by
  intro u v huv
  change circleJetDecoded u γ = circleJetDecoded v γ at huv
  apply Subtype.ext
  funext s
  apply Subtype.ext
  apply lp.ext
  funext m
  apply (WithLp.ext_iff 2).mpr
  funext j
  apply Lp.ext
  have hu := circleJetDecoded_level_ae hH u γ s m j
  rw [huv] at hu
  exact hu.trans (circleJetDecoded_level_ae hH v γ s m j).symm

theorem circleJetEncode_decoded (hH : ∀ m, 0 < T.H (T.sample m))
    (u : CircleJetProjectiveLimit T hM) (γ : ℝ) :
    circleJetEncode hM (circleJetDecoded_circleMember hH u γ) = u :=
  circleJetDecoded_injective hM hH γ
    (circleJetDecoded_encode hM hH (circleJetDecoded_circleMember hH u γ))

/-- Concrete circle model with the prescribed closed levels and decode. -/
def canonicalCircleModelData (T : MaterialData) (hM : ∀ m, 0 < T.M (T.sample m))
    (γ : ℝ) : CircleModelData where
  level := circleJetClosedSubmodule T
  bond := circleJetBond T hM
  decode := (circleJetDecodeCLM T hM γ).toLinearMap

theorem canonicalCircleModelData_decode (γ : ℝ)
    (u : (canonicalCircleModelData T hM γ).Space) :
    (canonicalCircleModelData T hM γ).decode u = circleJetDecoded (hM := hM) u γ :=
  circleJetDecodeCLM_apply T hM γ u

theorem isCircleModel_canonicalCircleModelData (hH : ∀ m, 0 < T.H (T.sample m))
    (γ : ℝ) : IsCircleModel T γ (canonicalCircleModelData T hM γ) := by
  refine ⟨fun s => circleJetClosedSubmodule_carrier (s := s) hM,
    isClosed_circleJetClosedSubmodule T, (circleJetDecodeCLM T hM γ).continuous, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [canonicalCircleModelData_decode]
    exact circleJetDecoded_circleMember hH u γ
  · intro f hf
    refine ⟨circleJetEncode hM hf, ?_⟩
    rw [canonicalCircleModelData_decode, circleJetDecoded_encode hM hH hf]
  · intro u v huv
    apply circleJetDecoded_injective hM hH γ
    simpa only [canonicalCircleModelData_decode] using huv
  · intro u s m
    rw [canonicalCircleModelData_decode]
    exact circleJetDecoded_zero_ae hH u γ s m
  · intro u s
    rw [canonicalCircleModelData_decode]
    exact circleJetDecoded_circleNorm hH u γ s

include hM in
theorem exists_isCircleModel_of_sample_pos (hH : ∀ m, 0 < T.H (T.sample m)) (γ : ℝ) :
    ∃ S : CircleModelData, IsCircleModel T γ S :=
  ⟨canonicalCircleModelData T hM γ, isCircleModel_canonicalCircleModelData hM hH γ⟩

theorem exists_isCircleModel_of_materialData {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (γ : ℝ) :
    ∃ S : CircleModelData, IsCircleModel T γ S := by
  obtain ⟨_, hD⟩ := hD
  have hcells : ∀ m, D.cells m ⊆ radialCore D := hD.2.1.2.2.2.1
  rcases hT with ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _, _⟩
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b := hcells m (hs m)
  exact exists_isCircleModel_of_sample_pos
    (fun m => zero_lt_one.trans_le (hpos _ (hsample m)).2.2.2)
    (fun m => (hpos _ (hsample m)).2.1) γ

end

end ContinuousFlexibility.Statements
