import ContinuousFlexibility.Radial.InnerPoissonCutoff

/-!
# Weak Green identities for the actual inner Dirichlet graph

The forced field has only its actual L² source and closed energy lift.
Integration by parts is proved on IntervalEnergyCore and extended by
continuity. The Poisson test may have arbitrary endpoint values. Its
scalar is the same temporary border scalar as in the actual graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

/-- Integration by parts against a smooth function with arbitrary endpoint
values. Only the first argument has zero Dirichlet values. -/
theorem innerEnergyClosure_smooth_pairing {a b : ℝ} {V p : ℝ → ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {Pd Pv Pf u d q : RadialL2}
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hPv : (Pv : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (fun x => V x * p x))
    (hPf : (Pf : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => -deriv (deriv p) x + V x * p x))
    (hu : (u, d, q) ∈ closure (IntervalEnergyCore V a b)) :
    ⟪Pf, u⟫_ℝ = ⟪Pd, d⟫_ℝ + ⟪Pv, u⟫_ℝ := by
  have hcore : IntervalEnergyCore V a b ⊆
      {v : RadialL2 × RadialL2 × RadialL2 |
        ⟪Pf, v.1⟫_ℝ = ⟪Pd, v.2.1⟫_ℝ + ⟪Pv, v.1⟫_ℝ} := by
    intro v hv
    obtain ⟨φ, hφ, hcφ, hvφ, hvd, hvq⟩ := hv.1
    have hvφout : (v.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] φ :=
      ae_restrict_of_ae hvφ
    have hφout : φ =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) :=
      Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hvφout) hv.2
    have hzero : EqOn φ (fun _ => 0) ((Ioo a b)ᶜ) :=
      innerDirichlet_representative_zero_outside hab hφ.continuous hφout
    have hφa : φ a = 0 := hzero (by simp : a ∈ (Ioo a b)ᶜ)
    have hφb : φ b = 0 := hzero (by simp : b ∈ (Ioo a b)ᶜ)
    change ⟪Pf, v.1⟫_ℝ = ⟪Pd, v.2.1⟫_ℝ + ⟪Pv, v.1⟫_ℝ
    rw [innerDirichlet_pairing_indicator hab.le hPf hvφ,
      innerDirichlet_pairing_indicator hab.le hPd hvd,
      innerDirichlet_pairing_indicator hab.le hPv hvφ]
    exact innerDirichlet_classical_pairing hab hV hp hφ hφa hφb
  have hclosed : IsClosed {v : RadialL2 × RadialL2 × RadialL2 |
      ⟪Pf, v.1⟫_ℝ = ⟪Pd, v.2.1⟫_ℝ + ⟪Pv, v.1⟫_ℝ} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact closure_minimal hcore hclosed hu

theorem innerWeakGreen_potential_pairing {V : ℝ → ℝ} {P Pv : RadialL2}
    (hPv : (Pv : ℝ → ℝ) =ᵐ[volume] (fun x => V x * P x)) (u : RadialL2) :
    ⟪Pv, u⟫_ℝ = ∫ x : ℝ, V x * u x * P x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hPv] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The actual potential product of a smooth boundary lift is in L². -/
theorem innerWeakGreen_potential_class {a b : ℝ} {V p : ℝ → ℝ}
    (hV : ContinuousOn V (Icc a b)) (hp : ContinuousOn p (Icc a b))
    {P : RadialL2} (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p) :
    ∃ Pv : RadialL2, (Pv : ℝ → ℝ) =ᵐ[volume] (fun x => V x * P x) := by
  have hprod : ContinuousOn (fun x => V x * p x) (Icc a b) := by
    simpa only [Pi.mul_apply] using hV.mul hp
  have hm : MemLp ((Ioo a b).indicator (fun x => V x * p x)) 2 volume :=
    innerDirichlet_indicator_memLp hprod
  refine ⟨hm.toLp ((Ioo a b).indicator (fun x => V x * p x)), ?_⟩
  filter_upwards [MemLp.coeFn_toLp hm, hP] with x hvx hpx
  rw [hvx, hpx]
  by_cases hx : x ∈ Ioo a b
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- The Poisson equation is tested against every element of the actual
zero-endpoint energy closure, including nonsmooth forced fields. -/
theorem innerEnergyClosure_poisson_pairing {a b α : ℝ} {V column p : ℝ → ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {g P Pd u d q : RadialL2}
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (heq : ∀ x ∈ Ioo a b,
      -deriv (deriv p) x + V x * p x + α * column x = 0)
    (hu : (u, d, q) ∈ closure (IntervalEnergyCore V a b)) :
    ⟪d, Pd⟫_ℝ + (∫ x : ℝ, V x * u x * P x) = -α * ⟪g, u⟫_ℝ := by
  have hpc : ContinuousOn p (Icc a b) :=
    fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hprod : ContinuousOn (fun x => V x * p x) (Icc a b) := by
    simpa only [Pi.mul_apply] using hV.mul hpc
  have hm : MemLp ((Ioo a b).indicator (fun x => V x * p x)) 2 volume :=
    innerDirichlet_indicator_memLp hprod
  let Pv : RadialL2 := hm.toLp ((Ioo a b).indicator (fun x => V x * p x))
  have hPv : (Pv : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => V x * p x) := MemLp.coeFn_toLp hm
  have hPvGlobal : (Pv : ℝ → ℝ) =ᵐ[volume] (fun x => V x * P x) := by
    filter_upwards [hPv, hP] with x hvx hpx
    rw [hvx, hpx]
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have hPf : ((-α • g : RadialL2) : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => -deriv (deriv p) x + V x * p x) := by
    filter_upwards [Lp.coeFn_smul (-α) g, hg] with x hsmul hgx
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hgx]
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      linarith [heq x hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have hpair := innerEnergyClosure_smooth_pairing hab hV hp hPd hPv hPf hu
  rw [real_inner_smul_left, real_inner_comm d Pd,
    innerWeakGreen_potential_pairing hPvGlobal u] at hpair
  exact hpair.symm

/-- The variational outgoing boundary pairing. The source includes the
actual scalar-column term when that border is present. -/
def innerWeakBoundaryPairing (V : ℝ → ℝ) (u d f P Pd : RadialL2) : ℝ :=
  ⟪d, Pd⟫_ℝ + (∫ x : ℝ, V x * u x * P x) - ⟪f, P⟫_ℝ

/-- The weak boundary pairing depends only on the two endpoint values.
The difference of the lifts belongs to the actual energy closure, proved
using endpoint cutoffs rather than assumed as a domain condition. -/
theorem innerWeakBoundaryPairing_eq_of_endpoint_values {a b : ℝ}
    {V p h : ℝ → ℝ} (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hh : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ h x)
    (ha : h a = p a) (hb : h b = p b)
    {P Pd H Hd u d f : RadialL2}
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hH : (H : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator h)
    (hHd : (Hd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv h))
    (hpair : ∀ v ∈ closure (IntervalEnergyCore V a b),
      ⟪f, v.1⟫_ℝ = ⟪d, v.2.1⟫_ℝ + ∫ x : ℝ, V x * u x * v.1 x) :
    innerWeakBoundaryPairing V u d f H Hd =
      innerWeakBoundaryPairing V u d f P Pd := by
  let w : ℝ → ℝ := fun x => h x - p x
  have hw : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ w x :=
    fun x hx => (hh x hx).sub (hp x hx)
  have hwc : ContinuousOn w (Icc a b) :=
    fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hW : ((H - P : RadialL2) : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator w := by
    filter_upwards [Lp.coeFn_sub H P, hH, hP] with x hsub hhx hpx
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hhx, hpx]
    by_cases hx : x ∈ Ioo a b
    · simp only [Set.indicator_of_mem hx, w]
    · simp only [Set.indicator_of_notMem hx, sub_self]
  have hWd : ((Hd - Pd : RadialL2) : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (deriv w) := by
    filter_upwards [Lp.coeFn_sub Hd Pd, hHd, hPd] with x hsub hdx hpx
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hdx, hpx]
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact (deriv_sub
        ((hh x (Ioo_subset_Icc_self hx)).differentiableAt (by simp))
        ((hp x (Ioo_subset_Icc_self hx)).differentiableAt (by simp))).symm
    · simp only [Set.indicator_of_notMem hx, sub_self]
  have hqc : ContinuousOn (fun x => sqrt (1 + |V x|) * w x) (Icc a b) :=
    (continuousOn_const.add hV.abs).sqrt.mul hwc
  have hqmem := innerDirichlet_indicator_memLp hqc
  let q : RadialL2 := hqmem.toLp
    ((Ioo a b).indicator (fun x => sqrt (1 + |V x|) * w x))
  have hq : (q : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => sqrt (1 + |V x|) * w x) := MemLp.coeFn_toLp hqmem
  have hwclosure : (H - P, Hd - Pd, q) ∈ closure (IntervalEnergyCore V a b) :=
    intervalEnergyClosure_of_smooth_zero_endpoints hab hV hw
      (sub_eq_zero.mpr ha) (sub_eq_zero.mpr hb) hW hWd hq
  have htest := hpair (H - P, Hd - Pd, q) hwclosure
  obtain ⟨Pv, hPv⟩ := innerWeakGreen_potential_class hV
    (fun x hx => (hp x hx).continuousAt.continuousWithinAt) hP
  obtain ⟨Hv, hHv⟩ := innerWeakGreen_potential_class hV
    (fun x hx => (hh x hx).continuousAt.continuousWithinAt) hH
  have hdiff : ((Hv - Pv : RadialL2) : ℝ → ℝ) =ᵐ[volume]
      (fun x => V x * (H - P : RadialL2) x) := by
    filter_upwards [Lp.coeFn_sub Hv Pv, Lp.coeFn_sub H P, hHv, hPv]
      with x hvsub hsub hvx hpx
    rw [hvsub, hsub]
    simp only [Pi.sub_apply]
    rw [hvx, hpx]
    ring
  have hpotential : (∫ x : ℝ, V x * u x * (H - P : RadialL2) x) =
      (∫ x : ℝ, V x * u x * H x) - ∫ x : ℝ, V x * u x * P x := by
    rw [← innerWeakGreen_potential_pairing hdiff u, inner_sub_left,
      innerWeakGreen_potential_pairing hHv u, innerWeakGreen_potential_pairing hPv u]
  dsimp only at htest
  rw [inner_sub_right, inner_sub_right, hpotential] at htest
  dsimp only [innerWeakBoundaryPairing]
  linarith

theorem innerBorderedIntervalGraph_effectiveForm {a b : ℝ} {V : ℝ → ℝ}
    {g : RadialL2} {bordered : Bool} {U F : RadialL2 × ℝ}
    (hG : BorderedIntervalGraph V g bordered a b U F) :
    IntervalFormGraph V a b U.1 (F.1 - U.2 • g) := by
  cases bordered with
  | false =>
    simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false] at hG
    simpa only [hG.2.1, zero_smul, sub_zero] using hG.1
  | true =>
    exact hG.1

/-- The flux identity for any fixed actual energy witness. This form lets
all boundary columns use one and the same derivative coordinate. -/
theorem innerEnergyClosure_bordered_poisson_flux {a b α : ℝ}
    {V column p : ℝ → ℝ} (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {g P Pd d q : RadialL2} {bordered : Bool} {U F : RadialL2 × ℝ}
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hrow : if bordered then ⟪g, P⟫_ℝ = 0 else α = 0)
    (heq : ∀ x ∈ Ioo a b,
      -deriv (deriv p) x + V x * p x + α * column x = 0)
    (hG : BorderedIntervalGraph V g bordered a b U F)
    (hclosure : (U.1, d, q) ∈ closure (IntervalEnergyCore V a b)) :
    innerWeakBoundaryPairing V U.1 d (F.1 - U.2 • g) P Pd =
      -(⟪F.1, P⟫_ℝ + α * F.2) := by
  have henergy := innerEnergyClosure_poisson_pairing hab hV hp hg hP hPd heq hclosure
  dsimp only [innerWeakBoundaryPairing]
  rw [henergy, inner_sub_left, real_inner_smul_left]
  cases bordered with
  | false =>
    simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false] at hG
    simp only [Bool.false_eq_true, ite_false] at hrow
    rw [hrow, hG.2.1, hG.2.2]
    ring
  | true =>
    simp only [BorderedIntervalGraph, ite_true] at hG
    simp only [ite_true] at hrow
    rw [hrow, hG.2]
    ring

/-- Negative Poisson adjoint identity for an arbitrary actual L² source.
The returned energy witness still satisfies the entire original form graph. -/
theorem innerBorderedIntervalGraph_poisson_flux {a b α : ℝ}
    {V column p : ℝ → ℝ} (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {g P Pd : RadialL2} {bordered : Bool} {U F : RadialL2 × ℝ}
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hrow : if bordered then ⟪g, P⟫_ℝ = 0 else α = 0)
    (heq : ∀ x ∈ Ioo a b,
      -deriv (deriv p) x + V x * p x + α * column x = 0)
    (hG : BorderedIntervalGraph V g bordered a b U F) :
    ∃ d q : RadialL2, (U.1, d, q) ∈ closure (IntervalEnergyCore V a b) ∧
      (∀ v ∈ closure (IntervalEnergyCore V a b),
        ⟪F.1 - U.2 • g, v.1⟫_ℝ =
          ⟪d, v.2.1⟫_ℝ + ∫ x : ℝ, V x * U.1 x * v.1 x) ∧
      innerWeakBoundaryPairing V U.1 d (F.1 - U.2 • g) P Pd =
        -(⟪F.1, P⟫_ℝ + α * F.2) := by
  obtain ⟨d, q, hclosure, hpair⟩ := innerBorderedIntervalGraph_effectiveForm hG
  exact ⟨d, q, hclosure, hpair,
    innerEnergyClosure_bordered_poisson_flux hab hV hp hg hP hPd hrow heq hG hclosure⟩

end ContinuousFlexibility.Radial
