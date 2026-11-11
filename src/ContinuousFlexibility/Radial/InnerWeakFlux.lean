import ContinuousFlexibility.Radial.InnerWeakGreen

/-!
# The two actual weak outgoing fluxes

A fixed affine boundary lift defines the conormal pairing at either cut.
The lift-independence theorem identifies it with every smooth lift with
the same boundary values. Consequently the actual R09 Dirichlet inverse
has forced flux equal to the negative adjoint of its own Poisson columns,
for all supported L² sources and the original single scalar row.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

def innerIntervalAffineLift (a b : ℝ) (z : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  ((b - x) * z 0 + (x - a) * z 1) / (b - a)

theorem innerIntervalAffineLift_contDiff (a b : ℝ) (z : Fin 2 → ℝ) :
    ContDiff ℝ ∞ (innerIntervalAffineLift a b z) := by
  have hn : ContDiff ℝ ∞ (fun x : ℝ => (b - x) * z 0 + (x - a) * z 1) :=
    ((contDiff_const.sub contDiff_id).mul contDiff_const).add
      ((contDiff_id.sub contDiff_const).mul contDiff_const)
  simpa only [innerIntervalAffineLift, div_eq_mul_inv] using hn.mul contDiff_const

theorem innerIntervalAffineLift_endpoints {a b : ℝ} (hab : a < b) (z : Fin 2 → ℝ) :
    innerIntervalAffineLift a b z a = z 0 ∧ innerIntervalAffineLift a b z b = z 1 := by
  have hn : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  constructor <;> dsimp only [innerIntervalAffineLift] <;> field_simp [hn] <;> ring

def innerIntervalBoundaryLiftL2 (a b : ℝ) (z : Fin 2 → ℝ) : RadialL2 :=
  (innerDirichlet_indicator_memLp
    (innerIntervalAffineLift_contDiff a b z).continuous.continuousOn).toLp
      ((Ioo a b).indicator (innerIntervalAffineLift a b z))

def innerIntervalBoundaryDerivL2 (a b : ℝ) (z : Fin 2 → ℝ) : RadialL2 :=
  (innerDirichlet_indicator_memLp
    ((innerIntervalAffineLift_contDiff a b z).continuous_deriv (by simp)).continuousOn).toLp
      ((Ioo a b).indicator (deriv (innerIntervalAffineLift a b z)))

theorem innerIntervalBoundaryLiftL2_ae (a b : ℝ) (z : Fin 2 → ℝ) :
    (innerIntervalBoundaryLiftL2 a b z : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (innerIntervalAffineLift a b z) :=
  MemLp.coeFn_toLp (innerDirichlet_indicator_memLp
    (innerIntervalAffineLift_contDiff a b z).continuous.continuousOn)

theorem innerIntervalBoundaryDerivL2_ae (a b : ℝ) (z : Fin 2 → ℝ) :
    (innerIntervalBoundaryDerivL2 a b z : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (deriv (innerIntervalAffineLift a b z)) :=
  MemLp.coeFn_toLp (innerDirichlet_indicator_memLp
    ((innerIntervalAffineLift_contDiff a b z).continuous_deriv (by simp)).continuousOn)

/-- Actual outgoing conormal pairing against the two boundary values z.
The definition uses fixed affine lifts, not an assumed Poisson adjoint. -/
def innerIntervalWeakFluxPairing (V : ℝ → ℝ) (a b : ℝ) (u d f : RadialL2)
    (z : Fin 2 → ℝ) : ℝ :=
  innerWeakBoundaryPairing V u d f
    (innerIntervalBoundaryLiftL2 a b z) (innerIntervalBoundaryDerivL2 a b z)

theorem innerIntervalWeakFluxPairing_eq {a b : ℝ} {V p : ℝ → ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {z : Fin 2 → ℝ} (htrace : p a = z 0 ∧ p b = z 1)
    {P Pd u d f : RadialL2}
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hpair : ∀ v ∈ closure (IntervalEnergyCore V a b),
      ⟪f, v.1⟫_ℝ = ⟪d, v.2.1⟫_ℝ + ∫ x : ℝ, V x * u x * v.1 x) :
    innerIntervalWeakFluxPairing V a b u d f z =
      innerWeakBoundaryPairing V u d f P Pd := by
  have hends := innerIntervalAffineLift_endpoints hab z
  exact innerWeakBoundaryPairing_eq_of_endpoint_values hab hV hp
    (fun _ _ => (innerIntervalAffineLift_contDiff a b z).contDiffAt)
    (hends.1.trans htrace.1.symm) (hends.2.trans htrace.2.symm) hP hPd
    (innerIntervalBoundaryLiftL2_ae a b z) (innerIntervalBoundaryDerivL2_ae a b z) hpair

theorem innerBorderedIntervalGraph_poisson_boundary_flux {a b α : ℝ}
    {V column p : ℝ → ℝ} (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {z : Fin 2 → ℝ} (htrace : p a = z 0 ∧ p b = z 1)
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
      innerIntervalWeakFluxPairing V a b U.1 d (F.1 - U.2 • g) z =
        -(⟪F.1, P⟫_ℝ + α * F.2) := by
  obtain ⟨d, q, hclosure, hpair, hflux⟩ :=
    innerBorderedIntervalGraph_poisson_flux hab hV hp hg hP hPd hrow heq hG
  exact ⟨d, q, hclosure, hpair,
    (innerIntervalWeakFluxPairing_eq hab hV hp htrace hP hPd hpair).trans hflux⟩

/-- The same R09 inverse and Poisson witness give the actual outgoing flux
for every supported L² source. No regularity of the source is assumed. -/
theorem innerBufferInverse_weak_flux {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    {p : ℝ → ℝ} {P : RadialL2} {scalar : ℝ}
    (hpLeft : ContDiffAt ℝ ∞ p B.l) (hpRight : ContDiffAt ℝ ∞ p B.h)
    (hpInside : ContDiffOn ℝ ∞ p (Ioo B.l B.h))
    (hPInside : (P : ℝ → ℝ) =ᵐ[volume.restrict (Ioo B.l B.h)] p)
    (hPOutside : (P : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0))
    (hrow : if B.bordered then ⟪B.border, P⟫_ℝ = 0 else scalar = 0)
    (hpEq : ∀ x ∈ Ioo B.l B.h,
      -deriv (deriv p) x + B.potential x * p x + scalar * B.borderFunction x = 0)
    (hpTrace : ∀ j, p (bufferCut B j) = if i = j then 1 else 0)
    (hsolve : ∀ F : RadialL2 × ℝ, (B.bordered = false → F.2 = 0) →
      ((F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) →
      BorderedIntervalGraph B.potential B.border B.bordered B.l B.h (G F) F)
    (F : RadialL2 × ℝ) (hscalar : B.bordered = false → F.2 = 0)
    (hsupport : (F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) :
    ∃ d q : RadialL2, ((G F).1, d, q) ∈ closure (IntervalEnergyCore B.potential B.l B.h) ∧
      (∀ v ∈ closure (IntervalEnergyCore B.potential B.l B.h),
        ⟪F.1 - (G F).2 • B.border, v.1⟫_ℝ =
          ⟪d, v.2.1⟫_ℝ + ∫ x : ℝ, B.potential x * (G F).1 x * v.1 x) ∧
      innerIntervalWeakFluxPairing B.potential B.l B.h (G F).1 d
        (F.1 - (G F).2 • B.border) (fun j => if i = j then 1 else 0) =
          -(⟪F.1, P⟫_ℝ + scalar * F.2) := by
  have hV : ContDiff ℝ ∞ B.potential := hB.2.2.2.2.1
  have hp := innerPoisson_contDiff_closed hpLeft hpRight hpInside
  have hm := innerDirichlet_indicator_memLp (innerDirichlet_deriv_continuousOn hp)
  let Pd : RadialL2 := hm.toLp ((Ioo B.l B.h).indicator (deriv p))
  have hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator (deriv p) :=
    MemLp.coeFn_toLp hm
  have hborder : (B.border : ℝ → ℝ) =ᵐ[volume]
      (Ioo B.l B.h).indicator B.borderFunction := by
    rcases hB with ⟨_, _, _, _, _, _, _, _, hg, _, _, hout, _, _, _⟩
    exact innerPoisson_eq_indicator (ae_restrict_of_ae hg) hout
  have hleft : p B.l = if i = 0 then 1 else 0 := by
    simpa only [bufferCut, if_pos rfl, ite_true] using hpTrace 0
  have hright : p B.h = if i = 1 then 1 else 0 := by
    have hcut : bufferCut B (1 : Fin 2) = B.h := by norm_num [bufferCut]
    simpa only [hcut] using hpTrace 1
  exact innerBorderedIntervalGraph_poisson_boundary_flux
    (z := fun j => if i = j then 1 else 0) hB.1 hV.continuous.continuousOn hp
    ⟨hleft, hright⟩ hborder (innerPoisson_eq_indicator hPInside hPOutside) hPd hrow hpEq
    (hsolve F hscalar hsupport)


/-- Both outgoing fluxes use one energy derivative witness of the same
Dirichlet solution. The Poisson assumptions are the original R09 family. -/
theorem innerBufferInverse_weak_flux_family {B : BufferData} (hB : BufferHypotheses B)
    (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    {p : Fin 2 → ℝ → ℝ} {P : Fin 2 → RadialL2} {scalar : Fin 2 → ℝ}
    (hpoisson : ∀ i,
      ContDiffAt ℝ ∞ (p i) B.l ∧ ContDiffAt ℝ ∞ (p i) B.h ∧
      ContDiffOn ℝ ∞ (p i) (Ioo B.l B.h) ∧ ContinuousOn (p i) (Icc B.l B.h) ∧
      ((P i : ℝ → ℝ) =ᵐ[volume.restrict (Ioo B.l B.h)] p i) ∧
      ((P i : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) ∧
      (if B.bordered then ⟪B.border, P i⟫_ℝ = 0 else scalar i = 0) ∧
      (∀ x ∈ Ioo B.l B.h, -deriv (deriv (p i)) x + B.potential x * p i x +
        scalar i * B.borderFunction x = 0) ∧
      ∀ j, p i (bufferCut B j) = if i = j then 1 else 0)
    (hsolve : ∀ F : RadialL2 × ℝ, (B.bordered = false → F.2 = 0) →
      ((F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) →
      BorderedIntervalGraph B.potential B.border B.bordered B.l B.h (G F) F)
    (F : RadialL2 × ℝ) (hscalar : B.bordered = false → F.2 = 0)
    (hsupport : (F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) :
    ∃ d q : RadialL2, ((G F).1, d, q) ∈ closure (IntervalEnergyCore B.potential B.l B.h) ∧
      (∀ v ∈ closure (IntervalEnergyCore B.potential B.l B.h),
        ⟪F.1 - (G F).2 • B.border, v.1⟫_ℝ =
          ⟪d, v.2.1⟫_ℝ + ∫ x : ℝ, B.potential x * (G F).1 x * v.1 x) ∧
      ∀ i, innerIntervalWeakFluxPairing B.potential B.l B.h (G F).1 d
        (F.1 - (G F).2 • B.border) (fun j => if i = j then 1 else 0) =
          -(⟪F.1, P i⟫_ℝ + scalar i * F.2) := by
  have hgraph := hsolve F hscalar hsupport
  obtain ⟨d, q, hclosure, hpair⟩ := innerBorderedIntervalGraph_effectiveForm hgraph
  refine ⟨d, q, hclosure, hpair, ?_⟩
  have hV : ContDiff ℝ ∞ B.potential := hB.2.2.2.2.1
  have hborder : (B.border : ℝ → ℝ) =ᵐ[volume]
      (Ioo B.l B.h).indicator B.borderFunction := by
    rcases hB with ⟨_, _, _, _, _, _, _, _, hg, _, _, hout, _, _, _⟩
    exact innerPoisson_eq_indicator (ae_restrict_of_ae hg) hout
  intro i
  rcases hpoisson i with
    ⟨hpLeft, hpRight, hpInside, hpCont, hPInside, hPOutside, hrow, hpEq, hpTrace⟩
  have hp := innerPoisson_contDiff_closed hpLeft hpRight hpInside
  have hm := innerDirichlet_indicator_memLp (innerDirichlet_deriv_continuousOn hp)
  let Pd : RadialL2 := hm.toLp ((Ioo B.l B.h).indicator (deriv (p i)))
  have hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator (deriv (p i)) :=
    MemLp.coeFn_toLp hm
  have hP := innerPoisson_eq_indicator hPInside hPOutside
  have hleft : p i B.l = if i = 0 then 1 else 0 := by
    simpa only [bufferCut, if_pos rfl, ite_true] using hpTrace 0
  have hright : p i B.h = if i = 1 then 1 else 0 := by
    have hcut : bufferCut B (1 : Fin 2) = B.h := by norm_num [bufferCut]
    simpa only [hcut] using hpTrace 1
  have hflux := innerEnergyClosure_bordered_poisson_flux hB.1 hV.continuous.continuousOn hp
    hborder hP hPd hrow hpEq hgraph hclosure
  exact (innerIntervalWeakFluxPairing_eq (z := fun j => if i = j then 1 else 0)
    hB.1 hV.continuous.continuousOn hp ⟨hleft, hright⟩ hP hPd hpair).trans hflux

end ContinuousFlexibility.Radial
