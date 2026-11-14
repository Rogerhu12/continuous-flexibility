module

public import ContinuousFlexibility.Analysis.SpacesPhysicalCellPolynomials
public import ContinuousFlexibility.Analysis.SpacesPhysicalEncode

/-!
# Evenization of actual cylinder jets

Angular reflection is an isometry of the prescribed cylinder measure.
Its signed average contracts every derivative coordinate and is exactly
the mixed derivative of the smooth even average of a cylinder function.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def spacesCylinderParity (b : ℕ) : CylinderL2 →L[ℝ] CylinderL2 :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ CylinderL2 +
    (-1 : ℝ) ^ b • cylinderReflectionL2.toContinuousLinearMap)

theorem spacesCylinderParity_apply (b : ℕ) (u : CylinderL2) :
    spacesCylinderParity b u = (1 / 2 : ℝ) • (u + (-1 : ℝ) ^ b • cylinderReflectionL2 u) := by
  simp only [spacesCylinderParity, smul_apply, add_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap]

theorem spacesCylinderParity_norm_le (b : ℕ) (u : CylinderL2) :
    ‖spacesCylinderParity b u‖ ≤ ‖u‖ := by
  rw [spacesCylinderParity_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
  calc
    (1 / 2 : ℝ) * ‖u + (-1 : ℝ) ^ b • cylinderReflectionL2 u‖ ≤
        (1 / 2 : ℝ) * (‖u‖ + ‖(-1 : ℝ) ^ b • cylinderReflectionL2 u‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        cylinderReflectionL2.norm_map]
      ring

theorem spacesCylinderParity_ae (b : ℕ) (u : CylinderL2) :
    (spacesCylinderParity b u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      fun p => (1 / 2 : ℝ) * (u p + (-1 : ℝ) ^ b * u (p.1, Real.pi - p.2)) := by
  rw [spacesCylinderParity_apply]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u + (-1 : ℝ) ^ b • cylinderReflectionL2 u),
    Lp.coeFn_add u ((-1 : ℝ) ^ b • cylinderReflectionL2 u),
    Lp.coeFn_smul ((-1 : ℝ) ^ b) (cylinderReflectionL2 u), cylinderReflectionL2_ae u]
    with p hhalf hadd hsign href
  rw [hhalf]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsign]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [href]

theorem spaces_mixedDerivative_add {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q + g q) p =
      mixedDerivative a b f p + mixedDerivative a b g p := by
  have hfr : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) := by
    have h := (contDiff_mixedDerivative hf 0 b).comp (contDiff_id.prodMk (contDiff_const (c := p.2)))
    simpa only [Function.comp_def, id_eq, mixedDerivative, iteratedDeriv_zero] using h
  have hgr : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => g (r, θ)) p.2) := by
    have h := (contDiff_mixedDerivative hg 0 b).comp (contDiff_id.prodMk (contDiff_const (c := p.2)))
    simpa only [Function.comp_def, id_eq, mixedDerivative, iteratedDeriv_zero] using h
  have he (r : ℝ) : iteratedDeriv b (fun θ => f (r, θ) + g (r, θ)) p.2 =
      iteratedDeriv b (fun θ => f (r, θ)) p.2 + iteratedDeriv b (fun θ => g (r, θ)) p.2 :=
    iteratedDeriv_fun_add ((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
      ((hg.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  unfold mixedDerivative
  simp_rw [he]
  exact iteratedDeriv_fun_add (hfr.contDiffAt.of_le (by simp)) (hgr.contDiffAt.of_le (by simp))

theorem spaces_mixedDerivative_const_mul (f : PolarPoint → ℝ) (c : ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => c * f q) p = c * mixedDerivative a b f p := by
  simp only [mixedDerivative, iteratedDeriv_const_mul_field]

theorem spaces_mixedDerivative_reflection (f : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f (q.1, Real.pi - q.2)) p =
      (-1 : ℝ) ^ b * mixedDerivative a b f (p.1, Real.pi - p.2) := by
  have he (r : ℝ) : iteratedDeriv b (fun θ => f (r, Real.pi - θ)) =
      fun θ => (-1 : ℝ) ^ b * iteratedDeriv b (fun θ => f (r, θ)) (Real.pi - θ) := by
    simpa only [smul_eq_mul] using
      (iteratedDeriv_comp_const_sub (f := fun θ => f (r, θ)) (n := b) (s := Real.pi))
  unfold mixedDerivative
  simp_rw [he]
  rw [iteratedDeriv_const_mul_field]

def spacesCylinderEvenFunction (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (1 / 2 : ℝ) * (f p + f (p.1, Real.pi - p.2))

theorem spacesCylinderEvenFunction_contDiff {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spacesCylinderEvenFunction f) :=
  contDiff_const.mul (hf.add (hf.comp (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd))))

theorem spacesCylinderEvenFunction_reflection (f : PolarPoint → ℝ) (p : PolarPoint) :
    spacesCylinderEvenFunction f (p.1, Real.pi - p.2) = spacesCylinderEvenFunction f p := by
  simp only [spacesCylinderEvenFunction, sub_sub_cancel, add_comm]

theorem spacesCylinderEvenFunction_periodic {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) :
    Function.Periodic (spacesCylinderEvenFunction f) (0, Real.pi) := by
  intro p
  have h := hf (p.1, -p.2)
  simp only [Prod.mk_add_mk, add_zero] at h
  simp only [spacesCylinderEvenFunction, Prod.fst_add, Prod.snd_add, add_zero]
  rw [hf p]
  rw [show Real.pi - (p.2 + Real.pi) = -p.2 by ring,
    show Real.pi - p.2 = -p.2 + Real.pi by ring, h]

theorem spacesCylinderEvenFunction_mixedDerivative {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (spacesCylinderEvenFunction f) p =
      (1 / 2 : ℝ) * (mixedDerivative a b f p +
        (-1 : ℝ) ^ b * mixedDerivative a b f (p.1, Real.pi - p.2)) := by
  change mixedDerivative a b (fun q => (1 / 2 : ℝ) * (f q + f (q.1, Real.pi - q.2))) p = _
  have hrf : ContDiff ℝ ∞ (fun q : PolarPoint => f (q.1, Real.pi - q.2)) :=
    hf.comp (contDiff_fst.prodMk ((contDiff_const (c := Real.pi)).sub contDiff_snd))
  rw [spaces_mixedDerivative_const_mul,
    spaces_mixedDerivative_add hf hrf,
    spaces_mixedDerivative_reflection]

theorem IsCylinderTest.spaces_even {f : PolarPoint → ℝ} (hf : IsCylinderTest f) :
    IsCylinderTest (spacesCylinderEvenFunction f) := by
  obtain ⟨R, hR, hz⟩ := hf.2.2
  refine ⟨spacesCylinderEvenFunction_contDiff hf.1, spacesCylinderEvenFunction_periodic hf.2.1,
    R, hR, fun p hp => ?_⟩
  simp only [spacesCylinderEvenFunction, hz p hp, hz (p.1, Real.pi - p.2) hp, add_zero, mul_zero]

theorem spaces_physicalJetGraph_of_test (T : MaterialData) (s : ℕ)
    {v : PolarPoint → ℝ} (hv : IsCylinderTest v)
    (href : ∀ p : PolarPoint, v (p.1, Real.pi - p.2) = v p)
    (z : PhysicalJetHilbert s)
    (hz : ∀ j : JetIndex s, (z j : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      fun p => T.M (T.radius p.1) ^ (j.val 2).val *
        mixedDerivative (j.val 0).val (j.val 1).val v p) :
    z ∈ physicalJetGraph T s := by
  have hzero : (z (zeroJetIndex s) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] v := by
    simpa only [zeroJetIndex, Fin.val_zero, pow_zero, one_mul, spaces_mixedDerivative_zero] using
      hz (zeroJetIndex s)
  have heq : z (zeroJetIndex s) = hv.memLp.toLp v := Lp.ext (hzero.trans (MemLp.coeFn_toLp _).symm)
  refine ⟨?_, fun j => ?_⟩
  · have hr := measurePreserving_cylinderAngularReflection.quasiMeasurePreserving.ae_eq_comp hzero
    filter_upwards [hr, hzero] with p hr hp
    exact hr.trans ((href p).trans hp.symm)
  · let hd := hv.mixedDerivative_memLp (j.val 0).val (j.val 1).val
    refine ⟨hd.toLp (mixedDerivative (j.val 0).val (j.val 1).val v), ?_, ?_⟩
    · rw [heq]
      exact spaces_hasWeakMixedDerivative_of_smooth hv.1 hv.2.1 _ _ hv.memLp hd
    · filter_upwards [hz j, MemLp.coeFn_toLp hd] with p hp hdp
      rw [hdp]
      exact hp

end ContinuousFlexibility.Statements
