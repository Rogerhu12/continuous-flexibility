import ContinuousFlexibility.Radial.BufferLocalPrimitive
import ContinuousFlexibility.Radial.PositiveBufferEnergyLift

/-!
# The closed Dirichlet energy domain

The public domain is the closure of the actual supported smooth core.
We use the Hilbert graph product to characterize this closure by its
annihilator; the argument keeps the actual weak derivative and potential
weight throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

def bufferIntervalCoreSubmodule (V : ℝ → ℝ) (l h : ℝ) :
    Submodule ℝ (RadialL2 × RadialL2 × RadialL2) where
  carrier := IntervalEnergyCore V l h
  zero_mem' := by
    refine ⟨⟨fun _ => 0, contDiff_const, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact HasCompactSupport.intro (isCompact_empty : IsCompact (∅ : Set ℝ))
        (fun _ _ => rfl)
    · filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
      change (0 : RadialL2) x = (0 : ℝ)
      change (0 : RadialL2) x = (0 : ℝ) at hx
      exact hx
    · filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
      change (0 : RadialL2) x = deriv (fun _ : ℝ => (0 : ℝ)) x
      rw [deriv_const]
      change (0 : RadialL2) x = (0 : ℝ) at hx
      exact hx
    · filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
      change (0 : RadialL2) x = sqrt (1 + |V x|) * 0
      rw [mul_zero]
      change (0 : RadialL2) x = (0 : ℝ) at hx
      exact hx
    · exact ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 (volume : Measure ℝ))
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨⟨φ, hφ, hcφ, hp0, hp1, hp2⟩, hps⟩
    rcases hq with ⟨⟨ψ, hψ, hcψ, hq0, hq1, hq2⟩, hqs⟩
    refine ⟨⟨φ + ψ, hφ.add hψ, hcφ.add hcψ, ?_, ?_, ?_⟩, ?_⟩
    · filter_upwards [Lp.coeFn_add p.1 q.1, hp0, hq0] with x ha hp hq
      change (p.1 + q.1) x = (φ + ψ) x
      rw [ha]
      simp only [Pi.add_apply, hp, hq]
    · filter_upwards [Lp.coeFn_add p.2.1 q.2.1, hp1, hq1] with x ha hp hq
      change (p.2.1 + q.2.1) x = deriv (φ + ψ) x
      rw [ha, deriv_add (hφ.differentiable (by simp) x) (hψ.differentiable (by simp) x)]
      simp only [Pi.add_apply, hp, hq]
    · filter_upwards [Lp.coeFn_add p.2.2 q.2.2, hp2, hq2] with x ha hp hq
      change (p.2.2 + q.2.2) x = sqrt (1 + |V x|) * (φ + ψ) x
      rw [ha]
      simp only [Pi.add_apply, hp, hq]
      ring
    · filter_upwards [ae_restrict_of_ae (Lp.coeFn_add p.1 q.1), hps, hqs] with x ha hp hq
      change (p.1 + q.1) x = 0
      rw [ha]
      simp only [Pi.add_apply, hp, hq, add_zero]
  smul_mem' := by
    intro c p hp
    rcases hp with ⟨⟨φ, hφ, hcφ, hp0, hp1, hp2⟩, hps⟩
    refine ⟨⟨fun x => c * φ x, contDiff_const.mul hφ, hcφ.mul_left, ?_, ?_, ?_⟩, ?_⟩
    · filter_upwards [Lp.coeFn_smul c p.1, hp0] with x ha hp
      change (c • p.1) x = c * φ x
      rw [ha]
      simp only [Pi.smul_apply, smul_eq_mul, hp]
    · filter_upwards [Lp.coeFn_smul c p.2.1, hp1] with x ha hp
      change (c • p.2.1) x = deriv (fun t => c * φ t) x
      rw [ha, deriv_const_mul c (hφ.differentiable (by simp) x)]
      simp only [Pi.smul_apply, smul_eq_mul, hp]
    · filter_upwards [Lp.coeFn_smul c p.2.2, hp2] with x ha hp
      change (c • p.2.2) x = sqrt (1 + |V x|) * (c * φ x)
      rw [ha]
      simp only [Pi.smul_apply, smul_eq_mul, hp]
      ring
    · filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c p.1), hps] with x ha hp
      change (c • p.1) x = 0
      rw [ha]
      simp only [Pi.smul_apply, smul_eq_mul, hp, mul_zero]

def bufferEnergyTripleMap :
    PositiveBufferEnergyTriple →L[ℝ] (RadialL2 × RadialL2 × RadialL2) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RadialL2) 0).prod
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RadialL2) 1).prod
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RadialL2) 2))

@[simp] theorem bufferEnergyTripleMap_apply (z : PositiveBufferEnergyTriple) :
    bufferEnergyTripleMap z = (z 0, z 1, z 2) := rfl

def bufferHilbertIntervalCore (V : ℝ → ℝ) (l h : ℝ) :
    Submodule ℝ PositiveBufferEnergyTriple :=
  (bufferIntervalCoreSubmodule V l h).comap bufferEnergyTripleMap.toLinearMap

theorem bufferHilbertIntervalCore_mem_iff (V : ℝ → ℝ) (l h : ℝ)
    (z : PositiveBufferEnergyTriple) :
    z ∈ bufferHilbertIntervalCore V l h ↔ (z 0, z 1, z 2) ∈ IntervalEnergyCore V l h := Iff.rfl

theorem bufferHilbertIntervalCore_closure_maps (V : ℝ → ℝ) (l h : ℝ)
    {z : PositiveBufferEnergyTriple}
    (hz : z ∈ (bufferHilbertIntervalCore V l h).topologicalClosure) :
    (z 0, z 1, z 2) ∈ closure (IntervalEnergyCore V l h) := by
  have hclosed : IsClosed {z : PositiveBufferEnergyTriple |
      bufferEnergyTripleMap z ∈ closure (IntervalEnergyCore V l h)} :=
    isClosed_closure.preimage bufferEnergyTripleMap.continuous
  have hsub : (bufferHilbertIntervalCore V l h : Set PositiveBufferEnergyTriple) ⊆
      {w : PositiveBufferEnergyTriple |
        bufferEnergyTripleMap w ∈ closure (IntervalEnergyCore V l h)} := by
    intro w hw
    exact subset_closure ((bufferHilbertIntervalCore_mem_iff V l h w).mp hw)
  change z ∈ closure (bufferHilbertIntervalCore V l h : Set PositiveBufferEnergyTriple) at hz
  exact (closure_minimal hsub hclosed) hz

theorem bufferCompactEnergyLift_mem_intervalCore (V : ℝ → ℝ) (hV : Continuous V)
    (l h : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo l h) :
    (positiveBufferCompactEnergyLift V hV φ hφ hc).val ∈ bufferHilbertIntervalCore V l h := by
  apply (bufferHilbertIntervalCore_mem_iff V l h _).mpr
  apply intervalEnergyCore_of_compactSmooth hφ hc ((subset_tsupport φ).trans hs)
  · exact positiveBufferCompactEnergyLift_base_ae V hV φ hφ hc
  · exact positiveBufferCompactEnergyLift_derivative_ae V hV φ hφ hc
  · exact MemLp.coeFn_toLp (positiveBufferCompact_weight_memLp hV hφ hc)

/-- An annihilator of the smooth graph core has a real weak derivative on
the interval; this is the dual characterization used in the density proof. -/
theorem bufferIntervalCore_orthogonal_weak_derivative {V : ℝ → ℝ} (hV : Continuous V)
    {l h : ℝ} {z : PositiveBufferEnergyTriple}
    (hz : z ∈ (bufferHilbertIntervalCore V l h)ᗮ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo l h) :
    (∫ x : ℝ, z 1 x * deriv φ x) =
      -(∫ x : ℝ, (z 0 x + sqrt (1 + |V x|) * z 2 x) * φ x) := by
  let v := positiveBufferCompactEnergyLift V hV φ hφ hc
  have hv := bufferCompactEnergyLift_mem_intervalCore V hV l h φ hφ hc hs
  have he := (Submodule.mem_orthogonal _ _).mp hz v.val hv
  rw [PiLp.inner_apply, Fin.sum_univ_three] at he
  simp only [positiveBufferL2_inner_integral] at he
  have h0 : (∫ x : ℝ, v.val 0 x * z 0 x) = ∫ x : ℝ, z 0 x * φ x := by
    apply integral_congr_ae
    filter_upwards [positiveBufferCompactEnergyLift_base_ae V hV φ hφ hc] with x hx
    change positiveBufferEnergyCoordinate V 0 v x * z 0 x = z 0 x * φ x
    rw [hx]
    ring
  have h1 : (∫ x : ℝ, v.val 1 x * z 1 x) = ∫ x : ℝ, z 1 x * deriv φ x := by
    apply integral_congr_ae
    filter_upwards [positiveBufferCompactEnergyLift_derivative_ae V hV φ hφ hc] with x hx
    change positiveBufferEnergyCoordinate V 1 v x * z 1 x = z 1 x * deriv φ x
    rw [hx]
    ring
  have h2 : (∫ x : ℝ, v.val 2 x * z 2 x) =
      ∫ x : ℝ, (sqrt (1 + |V x|) * z 2 x) * φ x := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (positiveBufferCompact_weight_memLp hV hφ hc)] with x hx
    change (positiveBufferCompact_weight_memLp hV hφ hc).toLp _ x * z 2 x = _
    rw [hx]
    ring
  rw [h0, h1, h2] at he
  have hA : Integrable (fun x : ℝ => z 0 x * φ x) volume :=
    (Lp.memLp (z 0)).integrable_mul
      (show MemLp φ 2 volume from hφ.continuous.memLp_of_hasCompactSupport hc)
  have hC : Integrable (fun x : ℝ => (sqrt (1 + |V x|) * z 2 x) * φ x) volume := by
    have hI := (Lp.memLp (z 2)).integrable_mul (positiveBufferCompact_weight_memLp hV hφ hc)
    convert hI using 1
    funext x
    change sqrt (1 + |V x|) * z 2 x * φ x =
      z 2 x * (sqrt (1 + |V x|) * φ x)
    ring
  have hsplit : (∫ x : ℝ, (z 0 x + sqrt (1 + |V x|) * z 2 x) * φ x) =
      (∫ x : ℝ, z 0 x * φ x) + ∫ x : ℝ, (sqrt (1 + |V x|) * z 2 x) * φ x := by
    rw [← integral_add hA hC]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hsplit]
  linarith

/-- The derivative of a supported global weak-energy field is supported in
the same interval. Endpoints have zero Lebesgue measure. -/
theorem buffer_supported_interval_derivative {u d : RadialL2} {l h : ℝ}
    (hud : WeakRadialDerivative u d)
    (hs : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0)) :
    (d : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0) := by
  have hu : (u : ℝ → ℝ) =ᵐ[volume.restrict (Icc l h)ᶜ] (fun _ => 0) :=
    ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.mpr Ioo_subset_Icc_self) hs
  have hd := buffer_weakDerivative_zero_on_open hud isClosed_Icc.isOpen_compl hu
  have hd' := (ae_restrict_iff' measurableSet_Icc.compl).mp hd
  change ∀ᵐ x : ℝ ∂volume.restrict (Ioo l h)ᶜ, d x = 0
  rw [ae_restrict_iff' measurableSet_Ioo.compl]
  filter_upwards [hd', volume.ae_ne l, volume.ae_ne h] with x hx hxl hxh hxi
  apply hx
  intro hxc
  exact hxi ⟨lt_of_le_of_ne hxc.1 (Ne.symm hxl), lt_of_le_of_ne hxc.2 hxh⟩

theorem buffer_supported_interval_zero_traces {u : RadialL2} {U : ℝ → ℝ} {l h : ℝ}
    (hU : Continuous U) (hu : (u : ℝ → ℝ) =ᵐ[volume] U)
    (hs : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0)) :
    U l = 0 ∧ U h = 0 := by
  have hleft : (u : ℝ → ℝ) =ᵐ[volume.restrict (Iio l)] (fun _ => 0) :=
    ae_restrict_of_ae_restrict_of_subset (by
      intro x hx hx'
      exact (not_lt_of_ge hx.le) hx'.1) hs
  have hright : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioi h)] (fun _ => 0) :=
    ae_restrict_of_ae_restrict_of_subset (by
      intro x hx hx'
      exact (not_lt_of_ge hx.le) hx'.2) hs
  have hzl := buffer_continuousRepresentative_zero_on_closure hU hu isOpen_Iio hleft
  have hzh := buffer_continuousRepresentative_zero_on_closure hU hu isOpen_Ioi hright
  exact ⟨hzl (show l ∈ closure (Iio l) by
      simpa only [closure_Iio, mem_Iic] using (le_refl l)),
    hzh (show h ∈ closure (Ioi h) by
      simpa only [closure_Ioi, mem_Ici] using (le_refl h))⟩

/-- Zero true endpoint traces make the finite-interval pairing with every
annihilator of the smooth Dirichlet core vanish. The original field need
not be supported in the interval. -/
theorem buffer_energy_interval_annihilator {V : ℝ → ℝ} (hV : Continuous V)
    {l h : ℝ} (hlh : l < h) {u d q : RadialL2}
    (he : (u, d, q) ∈ SchrodingerEnergyLift V)
    {U : ℝ → ℝ} (hU : Continuous U) (huU : (u : ℝ → ℝ) =ᵐ[volume] U)
    (hUl : U l = 0) (hUh : U h = 0)
    {z : PositiveBufferEnergyTriple} (hz : z ∈ (bufferHilbertIntervalCore V l h)ᗮ) :
    (∫ x in l..h, z 0 x * u x + z 1 x * d x + z 2 x * q x) = 0 := by
  let r (x : ℝ) := z 0 x + sqrt (1 + |V x|) * z 2 x
  have h0 : LocallyIntegrable (z 0 : ℝ → ℝ) volume :=
    (Lp.memLp (z 0)).locallyIntegrable (by norm_num)
  have h1 : LocallyIntegrable (z 1 : ℝ → ℝ) volume :=
    (Lp.memLp (z 1)).locallyIntegrable (by norm_num)
  have h2 : LocallyIntegrable (z 2 : ℝ → ℝ) volume :=
    (Lp.memLp (z 2)).locallyIntegrable (by norm_num)
  have hr : LocallyIntegrable r volume :=
    h0.add (MeasureTheory.LocallyIntegrable.continuous_mul
      (continuous_const.add hV.abs).sqrt h2)
  obtain ⟨B, hB, hzB, hBprim, hBderiv⟩ :=
    buffer_localWeakDerivative_continuousRepresentative hlh h1 hr
      (bufferIntervalCore_orthogonal_weak_derivative hV hz)
  obtain ⟨W, hW, huW, hUprim, hUderiv⟩ :=
    buffer_weakDerivative_continuousRepresentative he.1
  have hWU : W = U := buffer_continuousRepresentative_unique hW hU huW huU
  subst W
  have hd : LocallyIntegrable (d : ℝ → ℝ) volume :=
    (Lp.memLp d).locallyIntegrable (by norm_num)
  have hUac := bufferPrimitiveRepresentative_absolutelyContinuous hd hUprim l h
  have hBac := bufferPrimitiveRepresentative_absolutelyContinuous hr hBprim l h
  have hibp := hUac.integral_deriv_mul_eq_sub hBac
  rw [hUl, hUh, zero_mul, zero_mul, sub_self] at hibp
  have hzB' := (ae_restrict_iff' measurableSet_Ioo).mp hzB
  have hpoint : (∫ x in l..h, z 0 x * u x + z 1 x * d x + z 2 x * q x) =
      ∫ x in l..h, deriv U x * B x + U x * deriv B x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [huU, he.2, hUderiv, hBderiv, hzB', volume.ae_ne h]
      with x hu hq hdu hdb hzb hxh hxin
    rw [uIoc_of_le hlh.le] at hxin
    have hxoo : x ∈ Ioo l h := ⟨hxin.1, lt_of_le_of_ne hxin.2 hxh⟩
    rw [hdu.deriv, hdb.deriv, ← hu, ← hzb hxoo, hq]
    dsimp [r]
    ring
  exact hpoint.trans hibp

/-- Every supported weak-energy field annihilates the orthogonal complement
of the genuine compact smooth graph core. -/
theorem buffer_supported_energy_annihilator {V : ℝ → ℝ} (hV : Continuous V)
    {l h : ℝ} (hlh : l < h) {u d q : RadialL2}
    (he : (u, d, q) ∈ SchrodingerEnergyLift V)
    (hs : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0))
    {z : PositiveBufferEnergyTriple} (hz : z ∈ (bufferHilbertIntervalCore V l h)ᗮ) :
    inner (𝕜 := ℝ) (z 0) u + inner (𝕜 := ℝ) (z 1) d +
      inner (𝕜 := ℝ) (z 2) q = 0 := by
  obtain ⟨U, hU, huU, -⟩ := buffer_weakDerivative_continuousRepresentative he.1
  obtain ⟨hUl, hUh⟩ := buffer_supported_interval_zero_traces hU huU hs
  have hinterval := buffer_energy_interval_annihilator hV hlh he hU huU hUl hUh hz
  have hus := (ae_restrict_iff' measurableSet_Ioo.compl).mp hs
  have hds := (ae_restrict_iff' measurableSet_Ioo.compl).mp
    (buffer_supported_interval_derivative he.1 hs)
  let F (x : ℝ) := z 0 x * u x + z 1 x * d x + z 2 x * q x
  have hFzero : ∀ᵐ x : ℝ, x ∉ Ioo l h → F x = 0 := by
    filter_upwards [hus, hds, he.2] with x hu hd hq hxi
    dsimp [F]
    rw [hq, hu hxi, hd hxi]
    ring
  have hwhole : (∫ x : ℝ, F x) = ∫ x in l..h, F x := by
    rw [intervalIntegral.integral_of_le hlh.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact (setIntegral_eq_integral_of_ae_compl_eq_zero hFzero).symm
  have hI0 : Integrable (fun x : ℝ => z 0 x * u x) volume :=
    (Lp.memLp (z 0)).integrable_mul (Lp.memLp u)
  have hI1 : Integrable (fun x : ℝ => z 1 x * d x) volume :=
    (Lp.memLp (z 1)).integrable_mul (Lp.memLp d)
  have hI2 : Integrable (fun x : ℝ => z 2 x * q x) volume :=
    (Lp.memLp (z 2)).integrable_mul (Lp.memLp q)
  calc
    _ = ∫ x : ℝ, F x := by
      simp only [positiveBufferL2_inner_integral]
      exact ((integral_add (hI0.add hI1) hI2).trans
        (congrArg (fun a : ℝ => a + ∫ x : ℝ, z 2 x * q x) (integral_add hI0 hI1))).symm
    _ = 0 := hwhole.trans hinterval

/-- The closure of the actual supported smooth core contains every genuine
global weak-energy field supported in the interval. No abstract replacement
of the public form domain is made. -/
theorem intervalEnergyClosure_of_supported {V : ℝ → ℝ} (hV : Continuous V)
    {l h : ℝ} (hlh : l < h) {u d q : RadialL2}
    (he : (u, d, q) ∈ SchrodingerEnergyLift V)
    (hs : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0)) :
    (u, d, q) ∈ closure (IntervalEnergyCore V l h) := by
  let z : PositiveBufferEnergyTriple := WithLp.toLp 2 ![u, d, q]
  have hz : z ∈ (bufferHilbertIntervalCore V l h)ᗮᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    change inner (𝕜 := ℝ) (w 0) u + inner (𝕜 := ℝ) (w 1) d +
      inner (𝕜 := ℝ) (w 2) q = 0
    exact buffer_supported_energy_annihilator hV hlh he hs hw
  rw [(bufferHilbertIntervalCore V l h).orthogonal_orthogonal_eq_closure] at hz
  exact bufferHilbertIntervalCore_closure_maps V l h hz

/-- Exact characterization of the frozen interval energy domain. -/
theorem intervalEnergyClosure_iff_supported {V : ℝ → ℝ} (hV : Continuous V)
    (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (p : RadialL2 × RadialL2 × RadialL2) :
    p ∈ closure (IntervalEnergyCore V l h) ↔
      p ∈ SchrodingerEnergyLift V ∧
        (p.1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0) := by
  constructor
  · intro hp
    exact ⟨intervalEnergyClosure_subset_energy V l h hreal hp,
      intervalEnergyClosure_supported V l h hp⟩
  · rintro ⟨hp, hs⟩
    exact intervalEnergyClosure_of_supported hV hlh hp hs

end ContinuousFlexibility.Radial
