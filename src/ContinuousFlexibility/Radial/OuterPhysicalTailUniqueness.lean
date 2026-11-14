module

public import ContinuousFlexibility.Radial.OuterPhysicalInverseGauge
public import ContinuousFlexibility.Radial.OuterHomogeneousContinuation

/-!
# Classification of the actual physical L2 natural line

Every actual outward state is expanded in the already constructed
natural and Dirichlet basis by its two constant Wronskians. Its L2
condition then transports to the smooth logarithmic combination.
R06b's natural-line theorem and the nonzero basis Wronskian eliminate
the Dirichlet coefficient. No assumed endpoint classification enters.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem outer_two_wronskians_injective {u z U Z p q r s : ℝ}
    (hdet : p * s - q * r ≠ 0)
    (hP : u * q - z * p = U * q - Z * p)
    (hQ : u * s - z * r = U * s - Z * r) : u = U ∧ z = Z := by
  have hzP : (u - U) * q - (z - Z) * p = 0 := by nlinarith only [hP]
  have hzQ : (u - U) * s - (z - Z) * r = 0 := by nlinarith only [hQ]
  have hu : (u - U) * (p * s - q * r) = 0 := by
    calc
      _ = p * ((u - U) * s - (z - Z) * r) -
          r * ((u - U) * q - (z - Z) * p) := by ring
      _ = 0 := by rw [hzP, hzQ]; ring
  have hz : (z - Z) * (p * s - q * r) = 0 := by
    calc
      _ = q * ((u - U) * s - (z - Z) * r) -
          s * ((u - U) * q - (z - Z) * p) := by ring
      _ = 0 := by rw [hzP, hzQ]; ring
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hdet)⟩

/-- Two actual basis states span every actual state on the entire tail.
The proof uses their conserved Wronskians, with no global coefficient
bound or extra regularity assumption. -/
theorem outerFirstOrderSystem_basis_expansion
    {a b : ℝ} (hab : a < b) {alpha beta P ZP Q ZQ u z : ℝ → ℝ}
    (hP : OuterFirstOrderSystem alpha beta P ZP (Ico a b))
    (hQ : OuterFirstOrderSystem alpha beta Q ZQ (Ico a b))
    (hPe : P a = 1) (hQe : Q a = 0) (hZQe : ZQ a ≠ 0)
    (hu : OuterFirstOrderSystem alpha beta u z (Ico a b)) :
    ∃ A B : ℝ, ∀ x ∈ Ico a b,
      u x = A * P x + B * Q x ∧ z x = A * ZP x + B * ZQ x := by
  let A := u a
  let B := (z a - A * ZP a) / ZQ a
  let U : ℝ → ℝ := fun x => A * P x + B * Q x
  let Z : ℝ → ℝ := fun x => A * ZP x + B * ZQ x
  have hU : OuterFirstOrderSystem alpha beta U Z (Ico a b) := hP.linear_combination hQ A B
  have hUa : u a = U a := by
    dsimp only [U, A]
    rw [hPe, hQe, mul_one, mul_zero, add_zero]
  have hZa : z a = Z a := by
    dsimp only [Z, B]
    rw [div_mul_cancel₀ _ hZQe]
    ring
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  refine ⟨A, B, ?_⟩
  intro x hx
  have hdet : P x * ZQ x - ZP x * Q x ≠ 0 := by
    rw [outerFirstOrderSystem_state_determinant (convex_Ico a b) hP hQ ha hx,
      hPe, hQe, one_mul, mul_zero, sub_zero]
    exact hZQe
  have hwp : u x * ZP x - z x * P x = U x * ZP x - Z x * P x := by
    rw [outerFirstOrderSystem_state_determinant (convex_Ico a b) hu hP ha hx,
      outerFirstOrderSystem_state_determinant (convex_Ico a b) hU hP ha hx, hUa, hZa]
  have hwq : u x * ZQ x - z x * Q x = U x * ZQ x - Z x * Q x := by
    rw [outerFirstOrderSystem_state_determinant (convex_Ico a b) hu hQ ha hx,
      outerFirstOrderSystem_state_determinant (convex_Ico a b) hU hQ ha hx, hUa, hZa]
  exact outer_two_wronskians_injective hdet hwp hwq

/-- The actual physical L2 natural line consists precisely of the
constructed P state. This is a classification of every homogeneous
outward state in the original weighted space. -/
theorem MorsePhysicalTailBasis.natural_line
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K lam : ℝ}
    (hentry : 0 < entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    {u z : ℝ → ℝ}
    (hsys : OuterFirstOrderSystem
      (fun t => lam / outerTailOutwardWeight D right t)
      (fun t => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) t / (lam * t))
      u z (Ico (outerTailSign right * entrance)
        (outerTailSign right * tailPhysicalEndpoint D right)))
    (huL2 : MemLp u 2
      (outerOutwardTailMeasure D (morsePhysicalDeepTail M D right j start entrance η K) right)) :
    ∃ A : ℝ, ∀ t ∈ Ico (outerTailSign right * entrance)
        (outerTailSign right * tailPhysicalEndpoint D right),
      u t = A * F.P t ∧ z t = A * F.ZP lam t := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let c := outerTailSign right * entrance
  let b := outerTailSign right * tailPhysicalEndpoint D right
  have hcore : entrance ∈ radialCore D := by
    have hh := morsePhysicalDeepTail_radius_mem_core hD hT
      (show T.entrance ∈ Ico T.entrance T.endpoint from ⟨le_rfl, hT.1⟩)
    change tailPhysicalRadius right (tailPhysicalLog right entrance) ∈ radialCore D at hh
    rwa [tailPhysicalRadius_log right hentry] at hh
  have hcb : c < b := by
    cases right
    · change (-1 : ℝ) * entrance < (-1) * D.a
      nlinarith only [hcore.1]
    · change (1 : ℝ) * entrance < 1 * D.b
      simpa only [one_mul] using hcore.2
  have hZQe : F.ZQ lam c ≠ 0 := by
    rw [F.ZQ_entrance]
    exact div_ne_zero one_ne_zero hlam
  obtain ⟨A, B, hexpansion⟩ := outerFirstOrderSystem_basis_expansion hcb
    (F.P_system hD hentry hlam hT) (F.Q_system hD hentry hlam hT)
    F.P_entrance F.Q_entrance hZQe hsys
  let V : ℝ → ℝ := fun x => A * F.logP x + B * F.logQ x
  let VFlux : ℝ → ℝ := fun x => A * F.logPFlux x + B * F.logQFlux x
  have hVsys : TailFirstOrderSystem T.p T.Λ V VFlux (Ico T.entrance T.endpoint) := by
    intro x hx
    constructor
    · exact (((F.P_log_system x hx).1.const_mul A).add
        ((F.Q_log_system x hx).1.const_mul B)).congr_deriv (by dsimp only [VFlux]; ring)
    · exact (((F.P_log_system x hx).2.const_mul A).add
        ((F.Q_log_system x hx).2.const_mul B)).congr_deriv (by dsimp only [V]; ring)
  have hVs : ContDiffOn ℝ ∞ V (Iio T.endpoint) :=
    (contDiffOn_const.mul F.P_smooth).add (contDiffOn_const.mul F.Q_smooth)
  let f : ℝ → ℝ := u ∘ outerOutwardRadius right
  have hf : MemLp f 2
      ((radialHilbertMeasure D).restrict (radialTailInterval D right entrance)) := by
    have hh := (measurableEmbedding_outerOutwardRadius right).memLp_map_measure_iff.mp huL2
    change MemLp f 2 ((radialHilbertMeasure D).restrict
      (radialTailInterval D right (tailPhysicalRadius right (tailPhysicalLog right entrance)))) at hh
    rwa [tailPhysicalRadius_log right hentry] at hh
  have hinverse := morsePhysicalDeepTail_inverseGauge_memLp hD hentry hT hf
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hpull (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      outerPhysicalInverseGauge D right j f x = V x := by
    have hout := outerTailRadius_mem_outwardIco hD right hentry (Ioo_subset_Ico_self hx)
    have he := (hexpansion _ hout).1
    change f (tailPhysicalRadius right x) =
      A * outerTailOutwardLift D right j F.logP
          (outerOutwardRadius right (tailPhysicalRadius right x)) +
        B * outerTailOutwardLift D right j F.logQ
          (outerOutwardRadius right (tailPhysicalRadius right x)) at he
    rw [outerTailOutwardLift_reflect, outerTailOutwardLift_reflect,
      tailPhysicalLift_radius, tailPhysicalLift_radius,
      ← outerLogGauge_eq_rpow D right j x] at he
    unfold outerPhysicalInverseGauge
    rw [he]
    dsimp only [V]
    field_simp [(outerLogGauge_pos hend j x).ne'] <;> ring
  have hVlp : MemLp V 2 (deepTailMeasure T) := by
    apply (memLp_congr_ae ?_).mp hinverse
    apply (withDensity_absolutelyContinuous (volume.restrict (Ioo T.entrance T.endpoint))
      (fun x => ENNReal.ofReal (T.p x))).ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hpull x hx
  have hVnatural : TailNaturalEquation T V := by
    refine ⟨hVs.contDiffAt (isOpen_Iio.mem_nhds hT.1),
      hVs.mono (fun _ hx => hx.2), hVlp, ?_⟩
    exact tailFirstOrderSystem_equation isOpen_Ioo
      (fun x hx => (deepTail_pos hT x (Ioo_subset_Ico_self hx)).ne')
      (hVsys.mono Ioo_subset_Ico_self)
  let k := V (T.node 0) / F.logP (T.node 0)
  have heq : ∀ x ∈ Ioo T.entrance T.endpoint, V x = k * F.logP x :=
    tailNaturalEquation_eq_mul hT hη hK F.P_natural hVnatural F.P_node_ne
  have hx₁ : T.node 1 ∈ Ioo T.entrance T.endpoint :=
    ⟨deepTail_entrance_lt_succ_node hT 0, deepTail_node_lt_endpoint hT 1⟩
  have hx₁' := Ioo_subset_Ico_self hx₁
  have hevent : V =ᶠ[𝓝 (T.node 1)] fun x => k * F.logP x :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx₁) heq
  have hd := hevent.deriv_eq
  rw [(hVsys (T.node 1) hx₁').1.deriv,
    ((F.P_log_system.const_mul k) (T.node 1) hx₁').1.deriv] at hd
  change VFlux (T.node 1) / T.p (T.node 1) =
    (k * F.logPFlux (T.node 1)) / T.p (T.node 1) at hd
  have hflux : VFlux (T.node 1) = k * F.logPFlux (T.node 1) := by
    have hp : T.p (T.node 1) ≠ 0 := (deepTail_pos hT (T.node 1) hx₁').ne'
    calc
      _ = (VFlux (T.node 1) / T.p (T.node 1)) * T.p (T.node 1) :=
        (div_mul_cancel₀ _ hp).symm
      _ = ((k * F.logPFlux (T.node 1)) / T.p (T.node 1)) * T.p (T.node 1) :=
        congrArg (fun t : ℝ => t * T.p (T.node 1)) hd
      _ = _ := div_mul_cancel₀ _ hp
  have hzero : VFlux (T.node 1) * F.logP (T.node 1) -
      V (T.node 1) * F.logPFlux (T.node 1) = 0 := by
    rw [hflux, heq (T.node 1) hx₁]
    ring
  have hBzero : B = 0 := by
    have hh : B * (F.logQFlux (T.node 1) * F.logP (T.node 1) -
        F.logQ (T.node 1) * F.logPFlux (T.node 1)) = 0 := by
      calc
        _ = VFlux (T.node 1) * F.logP (T.node 1) -
            V (T.node 1) * F.logPFlux (T.node 1) := by dsimp only [V, VFlux]; ring
        _ = 0 := hzero
    simpa only [F.log_wronskian (T.node 1) hx₁', mul_one] using hh
  refine ⟨A, ?_⟩
  intro t ht
  simpa only [hBzero, zero_mul, add_zero] using hexpansion t ht

end ContinuousFlexibility.Radial
