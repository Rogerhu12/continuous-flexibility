module

public import ContinuousFlexibility.Analysis.N07bPhysicalGreen
public import ContinuousFlexibility.Analysis.N07bDivergenceTests
public import ContinuousFlexibility.Analysis.IntervalWeakPrimitive

/-!
# Green symmetry using only interior coefficient regularity

A radial test has compact radial support strictly inside the physical
annulus. The rectangle Green theorem can therefore be applied on a smaller
closed radial interval. Support then restores the original integral.
Only the coefficients on the open annulus and their angular seam values
are used. No smooth extension of the coefficients to the physical endpoints
is imposed or inferred from the frozen nonlinear data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- A smooth test supported in an open set removes all regularity demands
on the other factor outside that open set. -/
theorem n07b_contDiff_mul_of_tsupport_subset {A : Set PolarPoint}
    (hA : IsOpen A) {f φ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f A) (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ A) : ContDiff ℝ ∞ (fun p => f p * φ p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ A
  · exact ((hf p hp).contDiffAt (hA.mem_nhds hp)).mul hφ.contDiffAt
  · have hpφ : p ∉ tsupport φ := fun h => hp (hs h)
    have hz : (fun q => f q * φ q) =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hpφ] with q hq
      change f q * φ q = 0
      rw [image_eq_zero_of_notMem_tsupport hq, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- Local smoothness of all coefficients gives local smoothness of the
actual divergence expression. -/
theorem n07b_contDiffOn_divergenceOperator {A : Set PolarPoint} (hA : IsOpen A)
    {L : SymmetricCoefficients} {u : PolarPoint → ℝ}
    (ha : ContDiffOn ℝ ∞ L.a A) (hb : ContDiffOn ℝ ∞ L.b A)
    (hc : ContDiffOn ℝ ∞ L.c A) (hu : ContDiffOn ℝ ∞ u A) :
    ContDiffOn ℝ ∞ (divergenceOperator L u) A := by
  intro p hp
  have ha' := (ha p hp).contDiffAt (hA.mem_nhds hp)
  have hb' := (hb p hp).contDiffAt (hA.mem_nhds hp)
  have hc' := (hc p hp).contDiffAt (hA.mem_nhds hp)
  have hu' := (hu p hp).contDiffAt (hA.mem_nhds hp)
  exact ((contDiffAt_radialPartial
    (contDiffAt_symmetricNormalFlux ha' hb' hu') (by simp)).add
    (contDiffAt_angularPartial
      (contDiffAt_symmetricAngularFlux hb' hc' hu') (by simp))).contDiffWithinAt

/-- The closed support of a radial test stays inside the open annulus. -/
theorem n07b_radialTest_tsupport_subset {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hφ : RadialTest D φ) : tsupport φ ⊆ annularOpen D := by
  obtain ⟨K, hK, hKcore, hzero⟩ := hφ.2.2
  have hs : tsupport φ ⊆ K ×ˢ (univ : Set ℝ) := by
    apply closure_minimal _ (hK.isClosed.prod isClosed_univ)
    intro p hp
    refine ⟨?_, mem_univ _⟩
    by_contra hnot
    exact hp (hzero p.1 hnot p.2)
  exact fun p hp => ⟨hKcore (hs hp).1, mem_univ _⟩

/-- Actual Green symmetry against radial tests needs coefficient smoothness
only on the physical interior and periodicity only at interior radii. -/
theorem n07b_interior_physical_green {D : ReferenceData} (hab : D.a < D.b)
    {L : SymmetricCoefficients} {u φ : PolarPoint → ℝ}
    (ha : ContDiffOn ℝ ∞ L.a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ L.b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ L.c (annularOpen D))
    (hu : ContDiff ℝ ∞ u)
    (hBp : ∀ r ∈ radialCore D,
      Function.Periodic (fun θ => L.b (r, θ)) (2 * Real.pi))
    (hCp : ∀ r ∈ radialCore D,
      Function.Periodic (fun θ => L.c (r, θ)) (2 * Real.pi))
    (hup : Function.Periodic u (0, 2 * Real.pi)) (hφ : RadialTest D φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * divergenceOperator L φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        divergenceOperator L u (r, θ) * φ (r, θ)) := by
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  obtain ⟨K, hK, hKcore, hzero⟩ := hφ.2.2
  obtain ⟨l, r, hal, hlr, hrb, hKinner⟩ :=
    interval_compact_subset_Ioo hab hK hKcore
  have hφK : tsupport φ ⊆ K ×ˢ (univ : Set ℝ) := by
    apply closure_minimal _ (hK.isClosed.prod isClosed_univ)
    intro p hp
    refine ⟨?_, mem_univ _⟩
    by_contra hnot
    exact hp (hzero p.1 hnot p.2)
  have hrectangle (p : PolarPoint)
      (hp : p ∈ uIcc l r ×ˢ uIcc (0 : ℝ) (2 * Real.pi)) :
      p ∈ annularOpen D := by
    have hrange : p.1 ∈ Icc l r := by
      simpa only [uIcc_of_le hlr.le] using hp.1
    exact ⟨⟨hal.trans_le hrange.1, hrange.2.trans_lt hrb⟩, mem_univ _⟩
  have hflux (t : ℝ) (ht : t ∉ K) (θ : ℝ) :
      greenNormalFlux L.a L.b u φ (t, θ) = 0 := by
    have hv := hzero t ht θ
    have hrad := Radial.r11b_directionalPartial_zero_outside hK.isClosed hzero (1, 0) ht θ
    have hang := Radial.r11b_directionalPartial_zero_outside hK.isClosed hzero (0, 1) ht θ
    change radialPartial φ (t, θ) = 0 at hrad
    change angularPartial φ (t, θ) = 0 at hang
    simp only [greenNormalFlux, symmetricNormalFlux, hv, hrad, hang,
      mul_zero, zero_mul, add_zero, sub_zero]
  have hlK : l ∉ K := fun h => (lt_irrefl l) (hKinner h).1
  have hrK : r ∉ K := fun h => (lt_irrefl r) (hKinner h).2
  have hseam : ∀ t ∈ uIcc l r,
      greenAngularFlux L.b L.c u φ (t, 2 * Real.pi) =
        greenAngularFlux L.b L.c u φ (t, 0) := by
    intro t ht
    have ht' : t ∈ Icc l r := by simpa only [uIcc_of_le hlr.le] using ht
    have htcore : t ∈ radialCore D := ⟨hal.trans_le ht'.1, ht'.2.trans_lt hrb⟩
    have hB0 : L.b (t, 2 * Real.pi) = L.b (t, 0) := by
      simpa only [zero_add] using hBp t htcore 0
    have hC0 : L.c (t, 2 * Real.pi) = L.c (t, 0) := by
      simpa only [zero_add] using hCp t htcore 0
    have hu0 : u (t, 2 * Real.pi) = u (t, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using hup (t, 0)
    have hφ0 : φ (t, 2 * Real.pi) = φ (t, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using hφ.2.1 (t, 0)
    have hur : radialPartial u (t, 2 * Real.pi) = radialPartial u (t, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using periodic_radialPartial hup (t, 0)
    have huθ : angularPartial u (t, 2 * Real.pi) = angularPartial u (t, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using periodic_angularPartial hup (t, 0)
    have hφr : radialPartial φ (t, 2 * Real.pi) = radialPartial φ (t, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using periodic_radialPartial hφ.2.1 (t, 0)
    have hφθ : angularPartial φ (t, 2 * Real.pi) = angularPartial φ (t, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using periodic_angularPartial hφ.2.1 (t, 0)
    simp only [greenAngularFlux, symmetricAngularFlux,
      hB0, hC0, hu0, hφ0, hur, huθ, hφr, hφθ]
  have hgreen := integral_symmetric_green_eq_zero
    (A := L.a) (B := L.b) (C := L.c) (φ := u) (ψ := φ)
    (a := l) (b := r) (c := 0) (d := 2 * Real.pi)
    (fun p hp => (ha p (hrectangle p hp)).contDiffAt (hopen.mem_nhds (hrectangle p hp)))
    (fun p hp => (hb p (hrectangle p hp)).contDiffAt (hopen.mem_nhds (hrectangle p hp)))
    (fun p hp => (hc p (hrectangle p hp)).contDiffAt (hopen.mem_nhds (hrectangle p hp)))
    (fun _ _ => hu.contDiffAt) (fun _ _ => hφ.1.contDiffAt) hseam
    (fun θ _ => (hflux r hrK θ).trans (hflux l hlK θ).symm)
  let H : ℝ → ℝ := fun t => ∫ θ in (0 : ℝ)..2 * Real.pi,
    u (t, θ) * divergenceOperator L φ (t, θ) -
      φ (t, θ) * divergenceOperator L u (t, θ)
  change (∫ t in l..r, H t) = 0 at hgreen
  have hHzero (t : ℝ) (ht : t ∉ K) : H t = 0 := by
    have hdiv (θ : ℝ) : divergenceOperator L φ (t, θ) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h =>
        ht (hφK (n07b_tsupport_divergenceOperator_subset L φ h)).1)
    dsimp only [H]
    simp only [hdiv, hzero t ht, mul_zero, zero_mul, sub_zero,
      intervalIntegral.integral_zero]
  have hsupportInner : Function.support H ⊆ Ioc l r := by
    intro t ht
    have htK : t ∈ K := by
      by_contra h
      exact ht (hHzero t h)
    exact ⟨(hKinner htK).1, (hKinner htK).2.le⟩
  have hsupportD : Function.support H ⊆ Ioc D.a D.b := by
    intro t ht
    have htK : t ∈ K := by
      by_contra h
      exact ht (hHzero t h)
    exact ⟨(hKcore htK).1, (hKcore htK).2.le⟩
  have hfull : (∫ t in D.a..D.b, H t) = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset hsupportD,
      ← intervalIntegral.integral_eq_integral_of_support_subset hsupportInner]
    exact hgreen
  have hraw : (∫ t in D.a..D.b, ∫ θ in (0 : ℝ)..2 * Real.pi,
      u (t, θ) * divergenceOperator L φ (t, θ) -
        divergenceOperator L u (t, θ) * φ (t, θ)) = 0 := by
    calc
      _ = ∫ t in D.a..D.b, H t := by
        apply intervalIntegral.integral_congr
        intro t _
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only [H]
        ring
      _ = 0 := hfull
  have hnormalized : (∫ t in D.a..D.b, radialAngularMean (fun θ =>
      u (t, θ) * divergenceOperator L φ (t, θ) -
        divergenceOperator L u (t, θ) * φ (t, θ))) = 0 := by
    change (∫ t in D.a..D.b, (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
      u (t, θ) * divergenceOperator L φ (t, θ) -
        divergenceOperator L u (t, θ) * φ (t, θ)) = 0
    rw [intervalIntegral.integral_const_mul, hraw, mul_zero]
  have hφsupport := n07b_radialTest_tsupport_subset hφ
  have hDφ := n07b_contDiff_divergence_compact_test hopen ha hb hc hφ.1 hφsupport
  have hDu := n07b_contDiffOn_divergenceOperator hopen ha hb hc hu.contDiffOn
  have hleft : Continuous (fun p => u p * divergenceOperator L φ p) :=
    hu.continuous.mul hDφ.continuous
  have hright : Continuous (fun p => divergenceOperator L u p * φ p) :=
    (n07b_contDiff_mul_of_tsupport_subset hopen hDu hφ.1 hφsupport).continuous
  exact sub_eq_zero.mp
    ((n07b_integral_radialAngularMean_sub D hleft hright).symm.trans hnormalized)

/-- The π-periodic physical fields give the same full-period Green formula. -/
theorem n07b_interior_physical_green_of_pi_periodic
    {D : ReferenceData} (hab : D.a < D.b)
    {L : SymmetricCoefficients} {u φ : PolarPoint → ℝ}
    (ha : ContDiffOn ℝ ∞ L.a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ L.b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ L.c (annularOpen D))
    (hu : ContDiff ℝ ∞ u)
    (hBp : ∀ r ∈ radialCore D, Function.Periodic (fun θ => L.b (r, θ)) Real.pi)
    (hCp : ∀ r ∈ radialCore D, Function.Periodic (fun θ => L.c (r, θ)) Real.pi)
    (hup : Function.Periodic u (0, Real.pi)) (hφ : RadialTest D φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * divergenceOperator L φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        divergenceOperator L u (r, θ) * φ (r, θ)) := by
  apply n07b_interior_physical_green hab ha hb hc hu
  · intro r hr
    simpa only [two_mul] using (hBp r hr).add_period (hBp r hr)
  · intro r hr
    simpa only [two_mul] using (hCp r hr).add_period (hCp r hr)
  · simpa only [Prod.mk_add_mk, zero_add, two_mul] using hup.add_period hup
  · exact hφ

end ContinuousFlexibility.Analysis
