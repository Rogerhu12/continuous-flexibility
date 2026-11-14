module

public import ContinuousFlexibility.Analysis.N06WeakTraceIdentification
public import ContinuousFlexibility.Radial.RadialGreenBoundary
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The literal weak equation across finitely many interfaces

The global unknown and source remain the given L2 functions. On each
consecutive interval the unknown has a C1 representative with an AC
physical flux satisfying the actual equation almost everywhere.

The existing AC Green identity identifies each local residual with its
true endpoint Wronskian. Matching values and physical fluxes cancel every
internal boundary term. Summing the actual interval integrals gives the
full-interval distributional equation, with no global equation assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A finite chain of true boundary differences telescopes when the two
values at each internal cut agree. Neither outer value is fixed. -/
theorem n06_sum_matching_boundary_differences {n : ℕ}
    (L R : Fin (n + 1) → ℝ)
    (hmatch : ∀ i : Fin n, R i.castSucc = L i.succ) :
    (∑ i : Fin (n + 1), (R i - L i)) = R (Fin.last n) - L 0 := by
  have hsum : (∑ i : Fin n, R i.castSucc) = ∑ i : Fin n, L i.succ :=
    Finset.sum_congr rfl (fun i _ => hmatch i)
  rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc R, Fin.sum_univ_succ L, hsum]
  ring

/-- Actual interval integration over the finite chain, expressed using
the same `Fin` cuts as the physical finite-piece geometry. -/
theorem n06_sum_integral_finite_chain {n : ℕ}
    (cuts : Fin (n + 2) → ℝ) (hcuts : StrictMono cuts)
    {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (cuts 0) (cuts (Fin.last (n + 1)))) :
    (∑ i : Fin (n + 1), ∫ x in cuts i.castSucc..cuts i.succ, f x) =
      ∫ x in cuts 0..cuts (Fin.last (n + 1)), f x := by
  let P : Fin (n + 2) → ℝ := fun i => ∫ x in cuts 0..cuts i, f x
  have hmem (i : Fin (n + 2)) :
      cuts i ∈ uIcc (cuts 0) (cuts (Fin.last (n + 1))) := by
    rw [uIcc_of_le (hcuts.monotone (Fin.zero_le _))]
    exact ⟨hcuts.monotone (Fin.zero_le i), hcuts.monotone (Fin.le_last i)⟩
  have hPi (i : Fin (n + 2)) : IntervalIntegrable f volume (cuts 0) (cuts i) :=
    hf.mono_set (uIcc_subset_uIcc_left (hmem i))
  have he (i : Fin (n + 1)) :
      (∫ x in cuts i.castSucc..cuts i.succ, f x) = P i.succ - P i.castSucc :=
    (intervalIntegral.integral_interval_sub_left (hPi i.succ) (hPi i.castSucc)).symm
  have hmatch (i : Fin n) : P i.castSucc.succ = P i.succ.castSucc := by
    exact congrArg P (by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc])
  calc
    _ = ∑ i : Fin (n + 1), (P i.succ - P i.castSucc) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = P (Fin.last (n + 1)) - P 0 := by
      simpa only [Fin.succ_last, Fin.castSucc_zero] using
        n06_sum_matching_boundary_differences
          (fun i : Fin (n + 1) => P i.castSucc) (fun i => P i.succ) hmatch
    _ = _ := by simp only [P, intervalIntegral.integral_same, sub_zero]

/-- A local actual AE equation and its AC flux give the transposed test
identity with genuine endpoint values. This is a direct application of
the pre-existing AC Green identity. -/
theorem n06_ac_modal_green {l r : ℝ} (hlr : l < r)
    {a V v F φ : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hv : ContDiff ℝ 1 v)
    (hflux : AbsolutelyContinuousOnInterval (fun x => a x * deriv v x) l r)
    (hφ : ContDiff ℝ 2 φ)
    (hode : ∀ᵐ x ∂volume.restrict (Ioo l r),
      -deriv (fun y => a y * deriv v y) x + V x * v x = F x) :
    (∫ x in l..r, v x * (-deriv (fun y => a y * deriv φ y) x + V x * φ x) -
        F x * φ x) =
      radialWronskian a φ v r - radialWronskian a φ v l := by
  have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hφd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have htestFlux : ContDiff ℝ 1 (fun x => a x * deriv φ x) := ha.mul hφd
  have hder : ∀ᵐ x ∂volume, x ∈ uIcc l r →
      deriv (fun y => a y * deriv v y) x = V x * v x - F x := by
    rw [restrict_Ioo_eq_restrict_Icc] at hode
    have he := (ae_restrict_iff' measurableSet_Icc).mp hode
    filter_upwards [he] with x hx hxi
    have hxcc : x ∈ Icc l r := by simpa only [uIcc_of_le hlr.le] using hxi
    linarith only [hx hxcc]
  have hg := integral_green_of_absolutelyContinuous_flux
    (w := a) (u := φ) (v := v)
    (p := fun x => a x * deriv φ x) (q := fun x => a x * deriv v x)
    (f := deriv (fun x => a x * deriv φ x)) (g := fun x => V x * v x - F x)
    hφ₁.contDiffOn.absolutelyContinuousOnInterval
    hv.contDiffOn.absolutelyContinuousOnInterval
    htestFlux.contDiffOn.absolutelyContinuousOnInterval hflux
    (Eventually.of_forall (fun _ _ => rfl))
    (Eventually.of_forall (fun _ _ => rfl))
    (Eventually.of_forall (fun _ _ => rfl)) hder
  calc
    _ = ∫ x in l..r,
        φ x * (V x * v x - F x) - v x * deriv (fun y => a y * deriv φ y) x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := hg.trans (by simp only [radialWronskian]; ring)

/-- Matching value and actual physical flux determine the same boundary
Wronskian against a common test, without a nonzero coefficient assumption. -/
theorem n06_radialWronskian_eq_of_value_flux
    {a v w φ : ℝ → ℝ} {x : ℝ}
    (hvalue : v x = w x) (hflux : a x * deriv v x = a x * deriv w x) :
    radialWronskian a φ v x = radialWronskian a φ w x := by
  calc
    _ = φ x * (a x * deriv v x) - v x * (a x * deriv φ x) := by
      simp only [radialWronskian]
      ring
    _ = φ x * (a x * deriv w x) - w x * (a x * deriv φ x) := by rw [hvalue, hflux]
    _ = _ := by simp only [radialWronskian]; ring

private theorem finiteChain_testResidual_integrable {l r : ℝ} (hlr : l ≤ r)
    {a V u F φ : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hV : ContinuousOn V (Icc l r))
    (hu : MemLp u 2 (volume.restrict (Ioo l r)))
    (hF : MemLp F 2 (volume.restrict (Ioo l r))) (hφ : ContDiff ℝ 2 φ) :
    IntervalIntegrable
      (fun x => u x * (-deriv (fun y => a y * deriv φ y) x + V x * φ x)) volume l r ∧
      IntervalIntegrable (fun x => F x * φ x) volume l r := by
  have hui : IntervalIntegrable u volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mpr (interval_memLp_integrable hu)
  have hFi : IntervalIntegrable F volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mpr (interval_memLp_integrable hF)
  have hφd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have htc : Continuous (deriv (fun x => a x * deriv φ x)) :=
    (ha.mul hφd).continuous_deriv le_rfl
  have ht : ContinuousOn
      (fun x => -deriv (fun y => a y * deriv φ y) x + V x * φ x) (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact htc.neg.continuousOn.add (hV.mul hφ.continuous.continuousOn)
  exact ⟨hui.mul_continuousOn ht, hFi.mul_continuousOn hφ.continuous.continuousOn⟩

/-- Piecewise C1 representatives with true matching values and AC fluxes
give the full interval Green identity for the original L2 unknown/source.
Only local almost-everywhere equations are inputs. -/
theorem n06_finiteChain_transposed_boundary_pairing {n : ℕ}
    (cuts : Fin (n + 2) → ℝ) (hcuts : StrictMono cuts)
    {a V u F : ℝ → ℝ} (v : Fin (n + 1) → ℝ → ℝ)
    (ha : ContDiff ℝ 1 a)
    (hV : ContinuousOn V (Icc (cuts 0) (cuts (Fin.last (n + 1)))))
    (hu : MemLp u 2 (volume.restrict (Ioo (cuts 0) (cuts (Fin.last (n + 1))))))
    (hF : MemLp F 2 (volume.restrict (Ioo (cuts 0) (cuts (Fin.last (n + 1))))))
    (hv : ∀ i, ContDiff ℝ 1 (v i))
    (hflux : ∀ i, AbsolutelyContinuousOnInterval
      (fun x => a x * deriv (v i) x) (cuts i.castSucc) (cuts i.succ))
    (hrep : ∀ i, u =ᵐ[volume.restrict (Ioo (cuts i.castSucc) (cuts i.succ))] v i)
    (hode : ∀ i, ∀ᵐ x ∂volume.restrict (Ioo (cuts i.castSucc) (cuts i.succ)),
      -deriv (fun y => a y * deriv (v i) y) x + V x * v i x = F x)
    (hvalue : ∀ i : Fin n,
      v i.castSucc (cuts i.succ.castSucc) = v i.succ (cuts i.succ.castSucc))
    (hnormal : ∀ i : Fin n,
      a (cuts i.succ.castSucc) * deriv (v i.castSucc) (cuts i.succ.castSucc) =
        a (cuts i.succ.castSucc) * deriv (v i.succ) (cuts i.succ.castSucc))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    (∫ x in cuts 0..cuts (Fin.last (n + 1)),
        u x * (-deriv (fun y => a y * deriv φ y) x + V x * φ x) - F x * φ x) =
      radialWronskian a φ (v (Fin.last n)) (cuts (Fin.last (n + 1))) -
        radialWronskian a φ (v 0) (cuts 0) := by
  have hle : cuts 0 ≤ cuts (Fin.last (n + 1)) := hcuts.monotone (Fin.zero_le _)
  have hI := finiteChain_testResidual_integrable hle ha hV hu hF hφ
  have hlocal (i : Fin (n + 1)) :
      (∫ x in cuts i.castSucc..cuts i.succ,
        u x * (-deriv (fun y => a y * deriv φ y) x + V x * φ x) - F x * φ x) =
      radialWronskian a φ (v i) (cuts i.succ) -
        radialWronskian a φ (v i) (cuts i.castSucc) := by
    have hi : cuts i.castSucc < cuts i.succ := hcuts i.castSucc_lt_succ
    calc
      _ = ∫ x in cuts i.castSucc..cuts i.succ,
          v i x * (-deriv (fun y => a y * deriv φ y) x + V x * φ x) - F x * φ x := by
        simp only [intervalIntegral.integral_of_le hi.le, integral_Ioc_eq_integral_Ioo]
        apply integral_congr_ae
        filter_upwards [hrep i] with x hx
        rw [hx]
      _ = _ := n06_ac_modal_green hi ha (hv i) (hflux i) hφ (hode i)
  have hmatch (i : Fin n) :
      radialWronskian a φ (v i.castSucc) (cuts i.castSucc.succ) =
        radialWronskian a φ (v i.succ) (cuts i.succ.castSucc) := by
    have he : i.castSucc.succ = i.succ.castSucc := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
    rw [he]
    exact n06_radialWronskian_eq_of_value_flux (hvalue i) (hnormal i)
  calc
    _ = ∑ i : Fin (n + 1), ∫ x in cuts i.castSucc..cuts i.succ,
        u x * (-deriv (fun y => a y * deriv φ y) x + V x * φ x) - F x * φ x :=
      (n06_sum_integral_finite_chain cuts hcuts (hI.1.sub hI.2)).symm
    _ = ∑ i : Fin (n + 1),
        (radialWronskian a φ (v i) (cuts i.succ) -
          radialWronskian a φ (v i) (cuts i.castSucc)) :=
      Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = _ := by
      simpa only [Fin.succ_last, Fin.castSucc_zero] using
        n06_sum_matching_boundary_differences
          (fun i : Fin (n + 1) => radialWronskian a φ (v i) (cuts i.castSucc))
          (fun i => radialWronskian a φ (v i) (cuts i.succ)) hmatch

theorem n06_radialWronskian_zero_of_test_tsupport
    (a v φ : ℝ → ℝ) {x : ℝ} (hx : x ∉ tsupport φ) :
    radialWronskian a φ v x = 0 := by
  simp only [radialWronskian, image_eq_zero_of_notMem_tsupport hx,
    deriv_of_notMem_tsupport hx, zero_mul, sub_zero, mul_zero]

/-- Compact tests erase the two outer terms, yielding the literal weak
modal equation on the whole interval from local equations and true traces. -/
theorem n06_finiteChain_weak_modal_equation {n : ℕ}
    (cuts : Fin (n + 2) → ℝ) (hcuts : StrictMono cuts)
    {a V u F : ℝ → ℝ} (v : Fin (n + 1) → ℝ → ℝ)
    (ha : ContDiff ℝ 1 a)
    (hV : ContinuousOn V (Icc (cuts 0) (cuts (Fin.last (n + 1)))))
    (hu : MemLp u 2 (volume.restrict (Ioo (cuts 0) (cuts (Fin.last (n + 1))))))
    (hF : MemLp F 2 (volume.restrict (Ioo (cuts 0) (cuts (Fin.last (n + 1))))))
    (hv : ∀ i, ContDiff ℝ 1 (v i))
    (hflux : ∀ i, AbsolutelyContinuousOnInterval
      (fun x => a x * deriv (v i) x) (cuts i.castSucc) (cuts i.succ))
    (hrep : ∀ i, u =ᵐ[volume.restrict (Ioo (cuts i.castSucc) (cuts i.succ))] v i)
    (hode : ∀ i, ∀ᵐ x ∂volume.restrict (Ioo (cuts i.castSucc) (cuts i.succ)),
      -deriv (fun y => a y * deriv (v i) y) x + V x * v i x = F x)
    (hvalue : ∀ i : Fin n,
      v i.castSucc (cuts i.succ.castSucc) = v i.succ (cuts i.succ.castSucc))
    (hnormal : ∀ i : Fin n,
      a (cuts i.succ.castSucc) * deriv (v i.castSucc) (cuts i.succ.castSucc) =
        a (cuts i.succ.castSucc) * deriv (v i.succ) (cuts i.succ.castSucc)) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (cuts 0) (cuts (Fin.last (n + 1))) →
        (∫ x in cuts 0..cuts (Fin.last (n + 1)),
          u x * (-deriv (fun y => a y * deriv φ y) x + V x * φ x)) =
          ∫ x in cuts 0..cuts (Fin.last (n + 1)), F x * φ x := by
  intro φ hφ _ hφs
  have hφ₂ : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have he := n06_finiteChain_transposed_boundary_pairing cuts hcuts v ha hV hu hF
    hv hflux hrep hode hvalue hnormal hφ₂
  have hl : cuts 0 ∉ tsupport φ := fun h => (lt_irrefl _) (hφs h).1
  have hr : cuts (Fin.last (n + 1)) ∉ tsupport φ := fun h => (lt_irrefl _) (hφs h).2
  rw [n06_radialWronskian_zero_of_test_tsupport a (v (Fin.last n)) φ hr,
    n06_radialWronskian_zero_of_test_tsupport a (v 0) φ hl, sub_self] at he
  have hI := finiteChain_testResidual_integrable
    (hcuts.monotone (Fin.zero_le _)) ha hV hu hF hφ₂
  rw [intervalIntegral.integral_sub hI.1 hI.2] at he
  exact sub_eq_zero.mp he

end ContinuousFlexibility.Analysis
