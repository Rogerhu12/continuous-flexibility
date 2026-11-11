import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The actual interval form used in positive-buffer compression

The Dirichlet energy domain is the closure of the supported smooth core.
This module records its support, weak derivative, symmetry, and invariance
under changing a source outside the retained interval. No interval operator
or trace is supplied as an extra assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

/-- Restriction followed by zero extension, as an actual Lebesgue `L²` class. -/
def bufferL2Indicator (s : Set ℝ) (hs : MeasurableSet s) (u : RadialL2) : RadialL2 :=
  ((Lp.memLp u).indicator hs).toLp (s.indicator u)

theorem bufferL2Indicator_coeFn (s : Set ℝ) (hs : MeasurableSet s) (u : RadialL2) :
    (bufferL2Indicator s hs u : ℝ → ℝ) =ᵐ[volume] s.indicator u :=
  MemLp.coeFn_toLp _

theorem bufferL2Indicator_norm_le (s : Set ℝ) (hs : MeasurableSet s) (u : RadialL2) :
    ‖bufferL2Indicator s hs u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [bufferL2Indicator_coeFn s hs u] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
  · rw [Set.indicator_of_notMem hxs, norm_zero]
    exact norm_nonneg _

def bufferL2IndicatorCLM (s : Set ℝ) (hs : MeasurableSet s) : RadialL2 →L[ℝ] RadialL2 := by
  let L : RadialL2 →ₗ[ℝ] RadialL2 :=
    { toFun := bufferL2Indicator s hs
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [bufferL2Indicator_coeFn s hs (u + v),
          bufferL2Indicator_coeFn s hs u, bufferL2Indicator_coeFn s hs v,
          Lp.coeFn_add u v,
          Lp.coeFn_add (bufferL2Indicator s hs u) (bufferL2Indicator s hs v)]
          with x hsum hu hv h0 h1
        rw [hsum, h1, hu, hv]
        by_cases hxs : x ∈ s
        · simp only [Set.indicator_of_mem hxs]
          exact h0
        · simp only [Set.indicator_of_notMem hxs, add_zero]
      map_smul' := by
        intro a u
        apply Lp.ext
        filter_upwards [bufferL2Indicator_coeFn s hs (a • u),
          bufferL2Indicator_coeFn s hs u, Lp.coeFn_smul a u,
          Lp.coeFn_smul a (bufferL2Indicator s hs u)] with x hmul hu h0 h1
        change bufferL2Indicator s hs (a • u) x = (a • bufferL2Indicator s hs u) x
        rw [hmul, h1]
        simp only [Pi.smul_apply]
        rw [hu]
        by_cases hxs : x ∈ s
        · simp only [Set.indicator_of_mem hxs]
          exact h0
        · simp only [Set.indicator_of_notMem hxs, smul_zero] }
  exact L.mkContinuous 1 (fun u => by simpa only [one_mul] using bufferL2Indicator_norm_le s hs u)

@[simp] theorem bufferL2IndicatorCLM_apply (s : Set ℝ) (hs : MeasurableSet s) (u : RadialL2) :
    bufferL2IndicatorCLM s hs u = bufferL2Indicator s hs u := rfl

theorem bufferL2Indicator_eq_zero_iff (s : Set ℝ) (hs : MeasurableSet s) (u : RadialL2) :
    bufferL2Indicator s hs u = 0 ↔
      (u : ℝ → ℝ) =ᵐ[volume.restrict s] (fun _ => 0) := by
  constructor
  · intro hz
    have he := (Lp.eq_zero_iff_ae_eq_zero).mp hz
    apply (ae_restrict_iff' hs).mpr
    filter_upwards [bufferL2Indicator_coeFn s hs u, he] with x hx hx0
    intro hxs
    rw [Set.indicator_of_mem hxs] at hx
    exact hx.symm.trans hx0
  · intro hz
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have he := (ae_restrict_iff' hs).mp hz
    filter_upwards [bufferL2Indicator_coeFn s hs u, he] with x hx hx0
    rw [hx]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      exact hx0 hxs
    · exact Set.indicator_of_notMem hxs _

theorem bufferL2_supported_isClosed (s : Set ℝ) (hs : MeasurableSet s) :
    IsClosed {u : RadialL2 | (u : ℝ → ℝ) =ᵐ[volume.restrict s] (fun _ => 0)} := by
  have hset : {u : RadialL2 | (u : ℝ → ℝ) =ᵐ[volume.restrict s] (fun _ => 0)} =
      {u : RadialL2 | bufferL2IndicatorCLM s hs u = 0} := by
    ext u
    exact (bufferL2Indicator_eq_zero_iff s hs u).symm
  rw [hset]
  exact isClosed_eq (bufferL2IndicatorCLM s hs).continuous continuous_const

theorem intervalEnergyClosure_supported (V : ℝ → ℝ) (l h : ℝ)
    {p : RadialL2 × RadialL2 × RadialL2}
    (hp : p ∈ closure (IntervalEnergyCore V l h)) :
    (p.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo l h)ᶜ)] (fun _ => 0) := by
  have hc : IsClosed {p : RadialL2 × RadialL2 × RadialL2 |
      (p.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo l h)ᶜ)] (fun _ => 0)} :=
    (bufferL2_supported_isClosed _ measurableSet_Ioo.compl).preimage continuous_fst
  exact closure_minimal (fun _ hp => hp.2) hc hp

theorem intervalEnergyClosure_subset_energy (V : ℝ → ℝ) (l h : ℝ)
    (hV : ActualClosedFormRealization V) :
    closure (IntervalEnergyCore V l h) ⊆ SchrodingerEnergyLift V := by
  rw [← hV.2.2.1]
  exact closure_mono (fun _ hp => hp.1)

theorem weakRadialDerivative_unique {u d e : RadialL2}
    (hd : WeakRadialDerivative u d) (he : WeakRadialDerivative u e) : d = e := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp d).locallyIntegrable (by norm_num))
    ((Lp.memLp e).locallyIntegrable (by norm_num))
  intro φ hφ hc
  have hdφ := hd φ hφ hc
  have heφ := he φ hφ hc
  simp only [smul_eq_mul, mul_comm]
  linarith

theorem schrodingerEnergyLift_coordinates_unique {V : ℝ → ℝ}
    {u d e q r : RadialL2} (hu : (u, d, q) ∈ SchrodingerEnergyLift V)
    (hv : (u, e, r) ∈ SchrodingerEnergyLift V) : d = e ∧ q = r := by
  refine ⟨weakRadialDerivative_unique hu.1 hv.1, ?_⟩
  apply Lp.ext
  exact hu.2.trans hv.2.symm

theorem intervalFormGraph_supported {V : ℝ → ℝ} {l h : ℝ} {u f : RadialL2}
    (hu : IntervalFormGraph V l h u f) :
    (u : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo l h)ᶜ)] (fun _ => 0) := by
  obtain ⟨d, q, hmem, -⟩ := hu
  exact intervalEnergyClosure_supported V l h hmem

/-- The closed Dirichlet form is symmetric before invertibility is used. -/
theorem intervalFormGraph_pairing_symm {V : ℝ → ℝ} {l h : ℝ}
    {u v f g : RadialL2} (hu : IntervalFormGraph V l h u f)
    (hv : IntervalFormGraph V l h v g) : ⟪f, v⟫_ℝ = ⟪g, u⟫_ℝ := by
  obtain ⟨d, q, hmemu, hequ⟩ := hu
  obtain ⟨e, r, hmemv, heqv⟩ := hv
  rw [hequ _ hmemv, heqv _ hmemu, real_inner_comm e d]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem buffer_inner_eq_of_agree_on_support {s : Set ℝ} (hs : MeasurableSet s)
    {f g u : RadialL2} (hfg : (f : ℝ → ℝ) =ᵐ[volume.restrict s] g)
    (hu : (u : ℝ → ℝ) =ᵐ[volume.restrict sᶜ] (fun _ => 0)) :
    ⟪f, u⟫_ℝ = ⟪g, u⟫_ℝ := by
  have hfg' := (ae_restrict_iff' hs).mp hfg
  have hu' := (ae_restrict_iff' hs.compl).mp hu
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hfg', hu'] with x hfx hux
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hx : x ∈ s
  · rw [hfx hx]
  · rw [hux hx]
    simp only [zero_mul]

/-- An interval source is an `L²` class modulo its values outside the interval. -/
theorem intervalFormGraph_source_congr {V : ℝ → ℝ} {l h : ℝ}
    {u f g : RadialL2} (hfg : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)] g)
    (hu : IntervalFormGraph V l h u f) : IntervalFormGraph V l h u g := by
  obtain ⟨d, q, hmem, heq⟩ := hu
  refine ⟨d, q, hmem, ?_⟩
  intro p hp
  rw [← buffer_inner_eq_of_agree_on_support measurableSet_Ioo hfg
    (intervalEnergyClosure_supported V l h hp)]
  exact heq p hp

theorem schrodingerFormGraph_to_interval {V : ℝ → ℝ} {l h : ℝ}
    (hV : ActualClosedFormRealization V) {u d q f : RadialL2}
    (hmem : (u, d, q) ∈ closure (IntervalEnergyCore V l h))
    (hu : SchrodingerFormGraph V u f) : IntervalFormGraph V l h u f := by
  obtain ⟨e, r, he, heq⟩ := hu
  have hdu := schrodingerEnergyLift_coordinates_unique
    (intervalEnergyClosure_subset_energy V l h hV hmem) he
  refine ⟨d, q, hmem, ?_⟩
  intro p hp
  have hp' := intervalEnergyClosure_subset_energy V l h hV hp
  rw [hdu.1]
  exact (heq p hp').2

/-- Symmetry includes the scalar row and column with their actual signs. -/
theorem borderedIntervalGraph_pairing_symm {V : ℝ → ℝ} {g : RadialL2}
    {bordered : Bool} {l h : ℝ} {U F W K : RadialL2 × ℝ}
    (hU : BorderedIntervalGraph V g bordered l h U F)
    (hW : BorderedIntervalGraph V g bordered l h W K) :
    ⟪F.1, W.1⟫_ℝ + F.2 * W.2 = ⟪K.1, U.1⟫_ℝ + K.2 * U.2 := by
  cases bordered with
  | false =>
    simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false] at hU hW
    rw [hU.2.2, hW.2.2, zero_mul, zero_mul, add_zero, add_zero]
    exact intervalFormGraph_pairing_symm hU.1 hW.1
  | true =>
    simp only [BorderedIntervalGraph, ite_true] at hU hW
    have hs := intervalFormGraph_pairing_symm hU.1 hW.1
    simp only [inner_sub_left, inner_smul_left, conj_trivial] at hs
    rw [hU.2, hW.2] at hs
    linarith

theorem intervalEnergyCore_of_compactSmooth {V φ : ℝ → ℝ} {l h : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : Function.support φ ⊆ Ioo l h) {u d q : RadialL2}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] φ)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] deriv φ)
    (hq : (q : ℝ → ℝ) =ᵐ[volume] fun x => sqrt (1 + |V x|) * φ x) :
    (u, d, q) ∈ IntervalEnergyCore V l h := by
  refine ⟨⟨φ, hφ, hc, hu, hd, hq⟩, ?_⟩
  filter_upwards [ae_restrict_of_ae hu, ae_restrict_mem measurableSet_Ioo.compl] with x hx hxout
  rw [hx]
  by_contra hne
  exact hxout (hs hne)

/-- The second derivatives can be exchanged under genuine compact smooth tests. -/
theorem bufferCompactSmooth_second_pairing {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x : ℝ, φ x * deriv (deriv ψ) x) =
      ∫ x : ℝ, ψ x * deriv (deriv φ) x := by
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hψ' := (contDiff_infty_iff_deriv.mp hψ).2
  have hφ'' := (contDiff_infty_iff_deriv.mp hφ').2
  have hψ'' := (contDiff_infty_iff_deriv.mp hψ').2
  have hI := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hψ'.differentiable (by simp) x).hasDerivAt)
    ((hφ.continuous.mul hψ''.continuous).integrable_of_hasCompactSupport hcφ.mul_right)
    ((hφ'.continuous.mul hψ'.continuous).integrable_of_hasCompactSupport hcφ.deriv.mul_right)
    ((hφ.continuous.mul hψ'.continuous).integrable_of_hasCompactSupport hcφ.mul_right)
  have hJ := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hψ.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hφ'.differentiable (by simp) x).hasDerivAt)
    ((hψ.continuous.mul hφ''.continuous).integrable_of_hasCompactSupport hcψ.mul_right)
    ((hψ'.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport hcψ.deriv.mul_right)
    ((hψ.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport hcψ.mul_right)
  rw [hI, hJ]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem weakSchrodingerGraph_of_compactSmooth {V φ : ℝ → ℝ}
    (hV : Continuous V) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    {u f : RadialL2} (hu : (u : ℝ → ℝ) =ᵐ[volume] φ)
    (hf : (f : ℝ → ℝ) =ᵐ[volume] fun x => -deriv (deriv φ) x + V x * φ x) :
    WeakSchrodingerGraph V u f := by
  intro ψ hψ hcψ
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hψ' := (contDiff_infty_iff_deriv.mp hψ).2
  have hφ'' := (contDiff_infty_iff_deriv.mp hφ').2
  have hψ'' := (contDiff_infty_iff_deriv.mp hψ').2
  have hsec := bufferCompactSmooth_second_pairing hφ hcφ hψ hcψ
  have hA : Integrable (fun x => φ x * deriv (deriv ψ) x) volume :=
    (hφ.continuous.mul hψ''.continuous).integrable_of_hasCompactSupport hcφ.mul_right
  have hB : Integrable (fun x => ψ x * deriv (deriv φ) x) volume :=
    (hψ.continuous.mul hφ''.continuous).integrable_of_hasCompactSupport hcψ.mul_right
  have hC : Integrable (fun x => V x * φ x * ψ x) volume :=
    ((hV.mul hφ.continuous).mul hψ.continuous).integrable_of_hasCompactSupport
      (hcφ.mul_left.mul_right)
  calc
    (∫ x : ℝ, f x * ψ x) =
        ∫ x : ℝ, V x * φ x * ψ x - ψ x * deriv (deriv φ) x := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
      ring
    _ = (∫ x : ℝ, V x * φ x * ψ x) - ∫ x : ℝ, ψ x * deriv (deriv φ) x :=
      integral_sub hC hB
    _ = (∫ x : ℝ, V x * φ x * ψ x) - ∫ x : ℝ, φ x * deriv (deriv ψ) x := by
      rw [hsec]
    _ = ∫ x : ℝ, V x * φ x * ψ x - φ x * deriv (deriv ψ) x :=
      (integral_sub hC hA).symm
    _ = ∫ x : ℝ, u x * (-deriv (deriv ψ) x + V x * ψ x) := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
      ring

/-- A supported classical field lies in the exact frozen Dirichlet form graph. -/
theorem intervalFormGraph_of_compactSmooth {V φ : ℝ → ℝ} {l h : ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hs : Function.support φ ⊆ Ioo l h) {u d q f : RadialL2}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] φ)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] deriv φ)
    (hq : (q : ℝ → ℝ) =ᵐ[volume] fun x => sqrt (1 + |V x|) * φ x)
    (hf : (f : ℝ → ℝ) =ᵐ[volume] fun x => -deriv (deriv φ) x + V x * φ x) :
    IntervalFormGraph V l h u f := by
  apply schrodingerFormGraph_to_interval hreal
    (subset_closure (intervalEnergyCore_of_compactSmooth hφ hcφ hs hu hd hq))
  exact (hreal.2.2.2 u f).mp (weakSchrodingerGraph_of_compactSmooth hV hφ hcφ hu hf)

end ContinuousFlexibility.Radial
