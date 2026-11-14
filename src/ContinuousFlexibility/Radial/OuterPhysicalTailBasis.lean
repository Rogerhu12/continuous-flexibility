module

public import ContinuousFlexibility.Radial.OuterPhysicalTailOutward
public import ContinuousFlexibility.Radial.TailFundamentalStates

/-!
# The actual natural and Dirichlet physical tail basis

The logarithmic natural solution is constructed by the mass-resistance
recurrence. The independent Dirichlet state is the forward recurrence
from R06b. Their entrance gauges are reciprocal, so the physical natural
value is one and the physical outward Dirichlet flux is exactly one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- A natural state normalized at the entrance has an actual independent
Dirichlet state with entrance flux one. -/
theorem exists_tailDirichlet_unit_flux {T : DeepTailData}
    (hT : DeepTailHypotheses T) {P ZP : ℝ → ℝ}
    (hP : ContDiffOn ℝ ∞ P (Iio T.endpoint))
    (hZP : ContDiffOn ℝ ∞ ZP (Iio T.endpoint))
    (hsys : TailFirstOrderSystem T.p T.Λ P ZP (Ico T.entrance T.endpoint))
    (hPe : P T.entrance = 1) (hPnode : P (T.node 0) ≠ 0) :
    ∃ Q ZQ : ℝ → ℝ,
      ContDiffOn ℝ ∞ Q (Iio T.endpoint) ∧
      ContDiffOn ℝ ∞ ZQ (Iio T.endpoint) ∧
      TailFirstOrderSystem T.p T.Λ Q ZQ (Ico T.entrance T.endpoint) ∧
      Q T.entrance = 0 ∧ ZQ T.entrance = 1 ∧
      ∀ x ∈ Ico T.entrance T.endpoint, ZQ x * P x - Q x * ZP x = 1 := by
  let a := P (T.node 0)
  have hnode : (fun x => a⁻¹ * P x) (T.node 0) = 1 :=
    inv_mul_cancel₀ hPnode
  have he : (fun x => a⁻¹ * P x) T.entrance ≠ 0 := by
    change a⁻¹ * P T.entrance ≠ 0
    rw [hPe, mul_one]
    exact inv_ne_zero hPnode
  obtain ⟨q, z, hq, hz, hqs, hqe, hW⟩ :=
    exists_tailDirichletLeftState hT (contDiffOn_const.mul hP)
      (contDiffOn_const.mul hZP) (hsys.const_mul a⁻¹) hnode he
  let Q : ℝ → ℝ := fun x => a⁻¹ * q x
  let ZQ : ℝ → ℝ := fun x => a⁻¹ * z x
  have hQe : Q T.entrance = 0 := by
    dsimp only [Q]
    rw [hqe, mul_zero]
  have hW' (x : ℝ) (hx : x ∈ Ico T.entrance T.endpoint) :
      ZQ x * P x - Q x * ZP x = 1 := by
    calc
      _ = z x * (a⁻¹ * P x) - q x * (a⁻¹ * ZP x) := by dsimp only [Q, ZQ]; ring
      _ = 1 := hW x hx
  refine ⟨Q, ZQ, contDiffOn_const.mul hq, contDiffOn_const.mul hz,
    hqs.const_mul a⁻¹, hQe, ?_, hW'⟩
  have hh := hW' T.entrance ⟨le_rfl, hT.1⟩
  simpa only [hPe, hQe, mul_one, zero_mul, sub_zero] using hh

/-- At a zero value the gauge changes the outward physical flux by
exactly the reciprocal entrance gauge. -/
theorem morsePhysicalDeepTail_zero_lift_outward_flux
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u v : ℝ → ℝ}
    (hsys : TailFirstOrderSystem
      (morsePhysicalDeepTail M D right j start entrance η K).p
      (morsePhysicalDeepTail M D right j start entrance η K).Λ u v
      (Ico (morsePhysicalDeepTail M D right j start entrance η K).entrance
        (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    (hue : u (tailPhysicalLog right entrance) = 0) :
    outerTailSign right * tailPhysicalFlux D right j u entrance =
      ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2))⁻¹ *
        v (tailPhysicalLog right entrance) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let g : ℝ := (entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hg : 0 < g := rpow_pos_of_pos (div_pos hentry hend) _
  have hdlog := (hsys T.entrance ⟨le_rfl, hT.1⟩).1
  have hd := (hasDerivAt_tailPhysicalLift (D := D) (right := right) (j := j)
    (u := u) (r := entrance) hend hentry hdlog.differentiableAt).deriv
  have hp : T.p T.entrance = g ^ 2 * D.w entrance / entrance := by
    have hh := morsePhysicalDeepTail_density_eq M D right j start entrance η K T.entrance
    change T.p T.entrance =
      (tailPhysicalRadius right (tailPhysicalLog right entrance) / tailPhysicalEndpoint D right) ^
          (2 * (j : ℝ) ^ 2) *
        D.w (tailPhysicalRadius right (tailPhysicalLog right entrance)) /
          tailPhysicalRadius right (tailPhysicalLog right entrance) at hh
    rw [tailPhysicalRadius_log right hentry] at hh
    rw [hh, mul_comm (2 : ℝ) ((j : ℝ) ^ 2),
      rpow_mul (div_pos hentry hend).le, rpow_two]
  have hw : D.w entrance ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_div] at hp
    exact (deepTail_pos hT T.entrance ⟨le_rfl, hT.1⟩).ne' hp
  unfold tailPhysicalFlux
  rw [hd, hue, mul_zero, zero_add]
  change outerTailSign right *
      (D.w entrance * (g / entrance *
        (outerTailSign right * deriv u T.entrance))) =
    g⁻¹ * v T.entrance
  rw [hdlog.deriv, hp]
  calc
    _ = (outerTailSign right * outerTailSign right) * (g⁻¹ * v T.entrance) := by
      field_simp [hg.ne', hentry.ne', hw] <;> ring
    _ = _ := by rw [outerTailSign_mul_self, one_mul]

/-- Data constructed below, with physical entrance normalization and
the full quantitative natural norm. The growing Dirichlet state has no
square-integrability requirement. -/
structure MorsePhysicalTailBasis (M : MorseChainData) (D : ReferenceData)
    (right : Bool) (j start : ℕ) (entrance η K : ℝ) where
  logP : ℝ → ℝ
  logPFlux : ℝ → ℝ
  logQ : ℝ → ℝ
  logQFlux : ℝ → ℝ
  P_natural : TailNaturalEquation (morsePhysicalDeepTail M D right j start entrance η K) logP
  P_smooth : ContDiffOn ℝ ∞ logP
    (Iio (morsePhysicalDeepTail M D right j start entrance η K).endpoint)
  Q_smooth : ContDiffOn ℝ ∞ logQ
    (Iio (morsePhysicalDeepTail M D right j start entrance η K).endpoint)
  P_log_system : TailFirstOrderSystem
    (morsePhysicalDeepTail M D right j start entrance η K).p
    (morsePhysicalDeepTail M D right j start entrance η K).Λ logP logPFlux
    (Ico (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint)
  Q_log_system : TailFirstOrderSystem
    (morsePhysicalDeepTail M D right j start entrance η K).p
    (morsePhysicalDeepTail M D right j start entrance η K).Λ logQ logQFlux
    (Ico (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint)
  P_log_entry : logP (tailPhysicalLog right entrance) =
    ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2))⁻¹
  Q_log_entry : logQ (tailPhysicalLog right entrance) = 0
  Q_log_flux_entry : logQFlux (tailPhysicalLog right entrance) =
    (entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)
  log_wronskian : ∀ x ∈ Ico
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint,
    logQFlux x * logP x - logQ x * logPFlux x = 1
  P_entry : tailPhysicalLift D right j logP entrance = 1
  Q_entry : tailPhysicalLift D right j logQ entrance = 0
  Q_outward_flux : outerTailSign right * tailPhysicalFlux D right j logQ entrance = 1
  P_node_ne : ∀ k, logP ((morsePhysicalDeepTail M D right j start entrance η K).node k) ≠ 0
  P_node_step :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    ∀ n, |logP (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |logP (T.node n)|
  P_initial_node_bound :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    T.entrance < T.node 0 →
      |logP (T.node 0)| ≤ 8 / (T.Λ * tailMass T 0 * tailInitialResistance T) *
        |logP T.entrance|
  P_bound : 12 * (∫ x, logP x ^ 2
      ∂deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)) ≤
    396 * (tailMass (morsePhysicalDeepTail M D right j start entrance η K) 0 /
      ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2)

/-- Construction from R06b's actual recurrence, followed by the exact
physical gauge. Neither a physical solution nor a fundamental basis is
an input to this theorem. -/
theorem exists_morsePhysicalTailBasis
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) (j start : ℕ) {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) :
    Nonempty (MorsePhysicalTailBasis M D right j start entrance η K) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let g : ℝ := (entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hg : 0 < g := rpow_pos_of_pos (div_pos hentry hend) _
  obtain ⟨P, ZP, hP, hPs, hZPs, hPsys, _, hPe, hPnode, hstep, hnorm, hfirst⟩ :=
    exists_tailNaturalPoisson_norm_bound hT hη hK
  obtain ⟨Q, ZQ, hQs, _, hQsys, hQe, hZQe, hW⟩ :=
    exists_tailDirichlet_unit_flux hT hPs hZPs hPsys hPe (hPnode 0)
  let u : ℝ → ℝ := fun x => g⁻¹ * P x
  let q : ℝ → ℝ := fun x => g * Q x
  have husys := hPsys.const_mul g⁻¹
  have hqsys := hQsys.const_mul g
  have hue : tailPhysicalLift D right j u entrance = 1 := by
    change g * (g⁻¹ * P T.entrance) = 1
    rw [hPe, mul_one, mul_inv_cancel₀ hg.ne']
  have hqe : q T.entrance = 0 := by
    dsimp only [q]
    rw [hQe, mul_zero]
  have hqphys : tailPhysicalLift D right j q entrance = 0 := by
    change g * q T.entrance = 0
    rw [hqe, mul_zero]
  have hqflux : outerTailSign right * tailPhysicalFlux D right j q entrance = 1 := by
    rw [morsePhysicalDeepTail_zero_lift_outward_flux hD hentry hT hqsys hqe]
    change g⁻¹ * (g * ZQ T.entrance) = 1
    rw [hZQe, mul_one, inv_mul_cancel₀ hg.ne']
  have huLogEntry : u T.entrance = g⁻¹ := by
    change g⁻¹ * P T.entrance = g⁻¹
    rw [hPe, mul_one]
  have hqLogFluxEntry : g * ZQ T.entrance = g := by rw [hZQe, mul_one]
  have hlogW (x : ℝ) (hx : x ∈ Ico T.entrance T.endpoint) :
      (g * ZQ x) * u x - q x * (g⁻¹ * ZP x) = 1 := by
    calc
      _ = (g * g⁻¹) * (ZQ x * P x - Q x * ZP x) := by dsimp only [u, q]; ring
      _ = 1 := by rw [mul_inv_cancel₀ hg.ne', hW x hx, one_mul]
  have hustep (n : ℕ) : |u (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)| := by
    dsimp only [u]
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |g⁻¹| * (8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) *
          |P (T.node n)|) := mul_le_mul_of_nonneg_left (hstep n) (abs_nonneg _)
      _ = _ := by ring
  have huinitial (hgap : T.entrance < T.node 0) :
      |u (T.node 0)| ≤ 8 / (T.Λ * tailMass T 0 * tailInitialResistance T) *
        |u T.entrance| := by
    dsimp only [u]
    rw [hPe, mul_one, abs_mul]
    calc
      _ ≤ |g⁻¹| * (8 / (T.Λ * tailMass T 0 * tailInitialResistance T)) :=
        mul_le_mul_of_nonneg_left (hfirst hgap) (abs_nonneg _)
      _ = _ := mul_comm _ _
  refine ⟨{
    logP := u
    logPFlux := fun x => g⁻¹ * ZP x
    logQ := q
    logQFlux := fun x => g * ZQ x
    P_natural := tailNaturalEquation_const_mul hP g⁻¹
    P_smooth := contDiffOn_const.mul hPs
    Q_smooth := contDiffOn_const.mul hQs
    P_log_system := husys
    Q_log_system := hqsys
    P_log_entry := huLogEntry
    Q_log_entry := hqe
    Q_log_flux_entry := hqLogFluxEntry
    log_wronskian := hlogW
    P_entry := hue
    Q_entry := hqphys
    Q_outward_flux := hqflux
    P_node_ne := fun k => mul_ne_zero (inv_ne_zero hg.ne') (hPnode k)
    P_node_step := hustep
    P_initial_node_bound := huinitial
    P_bound := ?_
  }⟩
  have hscale : (∫ x, u x ^ 2 ∂deepTailMeasure T) =
      (∫ x, P x ^ 2 ∂deepTailMeasure T) / g ^ 2 := by
    change (∫ x, (g⁻¹ * P x) ^ 2 ∂deepTailMeasure T) = _
    simp_rw [mul_pow]
    rw [integral_const_mul, inv_pow]
    ring
  rw [hscale]
  have hdiv := div_le_div_of_nonneg_right hnorm (sq_nonneg g)
  have hmul := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 12)
  change 12 * ((∫ x, P x ^ 2 ∂deepTailMeasure T) / g ^ 2) ≤
    396 * (tailMass T 0 / g ^ 2)
  convert hmul using 1 <;> ring

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K lam : ℝ}

def P (F : MorsePhysicalTailBasis M D right j start entrance η K) : ℝ → ℝ :=
  outerTailOutwardLift D right j F.logP

def Q (F : MorsePhysicalTailBasis M D right j start entrance η K) : ℝ → ℝ :=
  outerTailOutwardLift D right j F.logQ

def ZP (F : MorsePhysicalTailBasis M D right j start entrance η K) (lam : ℝ) : ℝ → ℝ :=
  outerTailOutwardScaledFlux D right j lam F.logP

def ZQ (F : MorsePhysicalTailBasis M D right j start entrance η K) (lam : ℝ) : ℝ → ℝ :=
  outerTailOutwardScaledFlux D right j lam F.logQ

theorem P_system (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    OuterFirstOrderSystem
      (fun t => lam / outerTailOutwardWeight D right t)
      (fun t => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) t / (lam * t))
      F.P (F.ZP lam)
      (Ico (outerTailSign right * entrance)
        (outerTailSign right * tailPhysicalEndpoint D right)) :=
  morsePhysicalDeepTail_outward_firstOrder hD hentry hlam hT F.P_smooth F.P_log_system

theorem Q_system (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    OuterFirstOrderSystem
      (fun t => lam / outerTailOutwardWeight D right t)
      (fun t => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) t / (lam * t))
      F.Q (F.ZQ lam)
      (Ico (outerTailSign right * entrance)
        (outerTailSign right * tailPhysicalEndpoint D right)) :=
  morsePhysicalDeepTail_outward_firstOrder hD hentry hlam hT F.Q_smooth F.Q_log_system

@[simp] theorem P_entrance (F : MorsePhysicalTailBasis M D right j start entrance η K) :
    F.P (outerTailSign right * entrance) = 1 := by
  rw [P, outerTailOutwardLift_entrance]
  exact F.P_entry

@[simp] theorem Q_entrance (F : MorsePhysicalTailBasis M D right j start entrance η K) :
    F.Q (outerTailSign right * entrance) = 0 := by
  rw [Q, outerTailOutwardLift_entrance]
  exact F.Q_entry

theorem ZQ_entrance (F : MorsePhysicalTailBasis M D right j start entrance η K) (lam : ℝ) :
    F.ZQ lam (outerTailSign right * entrance) = 1 / lam := by
  rw [ZQ, outerTailOutwardScaledFlux_entrance, F.Q_outward_flux]

theorem P_memLp_radial (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    MemLp (tailPhysicalLift D right j F.logP) 2
      ((radialHilbertMeasure D).restrict (radialTailInterval D right entrance)) :=
  morsePhysicalDeepTail_lift_memLp_radial hD hentry hT F.P_natural

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
