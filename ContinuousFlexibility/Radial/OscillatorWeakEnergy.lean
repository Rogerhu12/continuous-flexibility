import ContinuousFlexibility.Radial.CentralEnergyIdentity
import ContinuousFlexibility.Radial.OscillatorCompactCore
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The actual weak-derivative physical energy space

This file defines the Hilbert subspace of actual L2 triples (u, d, jXu).
Weak differentiation uses genuine smooth compact tests, and multiplication
by jX is an almost-everywhere identity of actual L2 representatives.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

/-- The actual physical energy coordinates `(u, ∂u, jXu)`, with their
Hilbert product norm rather than the max norm on an ordinary product. -/
abbrev PhysicalEnergyTriple := PiLp 2 (fun _ : Fin 3 => HermiteL2)

/-- A genuine first weak derivative, tested only against actual smooth
compactly supported functions on the real line. -/
def HasWeakDerivativeL2 (u d : HermiteL2) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x : ℝ, d x * φ x) = -(∫ x : ℝ, u x * deriv φ x)

/-- The integral pairing with an actual square-integrable test function. -/
def physicalTestPairing (φ : ℝ → ℝ) (hφ : MemLp φ 2 volume) :
    HermiteL2 →L[ℝ] ℝ :=
  innerSL ℝ (hφ.toLp φ)

theorem physicalTestPairing_apply (φ : ℝ → ℝ) (hφ : MemLp φ 2 volume)
    (u : HermiteL2) :
    physicalTestPairing φ hφ u = ∫ x : ℝ, u x * φ x := by
  change ⟪hφ.toLp φ, u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]

theorem hasWeakDerivativeL2_iff_pairings (u d : HermiteL2) :
    HasWeakDerivativeL2 u d ↔
      ∀ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        physicalTestPairing φ (compactSmooth_energyDomain hφ hc).2.1 d =
          -physicalTestPairing (deriv φ) (compactSmooth_energyDomain hφ hc).2.2.1 u := by
  constructor <;> intro h φ hφ hc
  · rw [physicalTestPairing_apply, physicalTestPairing_apply]
    exact h φ hφ hc
  · have hh := h φ hφ hc
    rwa [physicalTestPairing_apply, physicalTestPairing_apply] at hh

theorem hasWeakDerivativeL2_zero : HasWeakDerivativeL2 0 0 := by
  apply (hasWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  simp only [map_zero, neg_zero]

theorem HasWeakDerivativeL2.add {u d v e : HermiteL2}
    (hu : HasWeakDerivativeL2 u d) (hv : HasWeakDerivativeL2 v e) :
    HasWeakDerivativeL2 (u + v) (d + e) := by
  apply (hasWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  rw [map_add, map_add,
    (hasWeakDerivativeL2_iff_pairings _ _).mp hu φ hφ hc,
    (hasWeakDerivativeL2_iff_pairings _ _).mp hv φ hφ hc]
  ring

theorem HasWeakDerivativeL2.smul {u d : HermiteL2}
    (hu : HasWeakDerivativeL2 u d) (a : ℝ) :
    HasWeakDerivativeL2 (a • u) (a • d) := by
  apply (hasWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  rw [map_smul, map_smul,
    (hasWeakDerivativeL2_iff_pairings _ _).mp hu φ hφ hc]
  simp only [smul_eq_mul]
  ring

/-- The physical energy graph uses the actual weak derivative and the
actual almost-everywhere multiplication by `jX`, without spectral data. -/
def physicalEnergyGraph (j : ℝ) : Submodule ℝ PhysicalEnergyTriple where
  carrier := {z | HasWeakDerivativeL2 (z 0) (z 1) ∧
    (z 2 : ℝ → ℝ) =ᵐ[volume] (fun x => j * x * z 0 x)}
  zero_mem' := by
    refine ⟨hasWeakDerivativeL2_zero, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
    change (0 : HermiteL2) x = j * x * (0 : HermiteL2) x
    rw [hx]
    simp
  add_mem' := by
    intro z w hz hw
    refine ⟨hz.1.add hw.1, ?_⟩
    filter_upwards [hz.2, hw.2, Lp.coeFn_add (z 2) (w 2),
      Lp.coeFn_add (z 0) (w 0)] with x hzx hwx h2 h0
    change (z 2 + w 2) x = j * x * (z 0 + w 0) x
    rw [h2, h0]
    simp only [Pi.add_apply]
    rw [hzx, hwx]
    ring
  smul_mem' := by
    intro a z hz
    refine ⟨hz.1.smul a, ?_⟩
    filter_upwards [hz.2, Lp.coeFn_smul a (z 2), Lp.coeFn_smul a (z 0)] with x hzx h2 h0
    change (a • z 2) x = j * x * (a • z 0) x
    rw [h2, h0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hzx]
    ring

private theorem physical_weak_derivative_closed :
    IsClosed {z : PhysicalEnergyTriple | HasWeakDerivativeL2 (z 0) (z 1)} := by
  have hset : {z : PhysicalEnergyTriple | HasWeakDerivativeL2 (z 0) (z 1)} =
      ⋂ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        {z : PhysicalEnergyTriple |
          physicalTestPairing φ (compactSmooth_energyDomain hφ hc).2.1 (z 1) =
            -physicalTestPairing (deriv φ) (compactSmooth_energyDomain hφ hc).2.2.1 (z 0)} := by
    ext z
    change HasWeakDerivativeL2 (z 0) (z 1) ↔ _
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using
      hasWeakDerivativeL2_iff_pairings (z 0) (z 1)
  rw [hset]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro hφ
  apply isClosed_iInter
  intro hc
  exact isClosed_eq
    ((physicalTestPairing φ (compactSmooth_energyDomain hφ hc).2.1).continuous.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) 1).continuous)
    (((physicalTestPairing (deriv φ) (compactSmooth_energyDomain hφ hc).2.2.1).continuous.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) 0).continuous).neg)

private theorem physical_weighted_position_closed (j : ℝ) :
    IsClosed {z : PhysicalEnergyTriple |
      (z 2 : ℝ → ℝ) =ᵐ[volume] (fun x => j * x * z 0 x)} := by
  apply IsSeqClosed.isClosed
  intro f z hf hlim
  have h0 : Tendsto (fun n => f n 0) atTop (𝓝 (z 0)) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) 0).continuous.tendsto z).comp hlim
  have h2 : Tendsto (fun n => f n 2) atTop (𝓝 (z 2)) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) 2).continuous.tendsto z).comp hlim
  obtain ⟨s, hs, hs0⟩ := (tendstoInMeasure_of_tendsto_Lp h0).exists_seq_tendsto_ae
  obtain ⟨t, ht, ht2⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (h2.comp hs.tendsto_atTop)).exists_seq_tendsto_ae
  have hrel : ∀ᵐ x : ℝ, ∀ n : ℕ,
      f (s (t n)) 2 x = j * x * f (s (t n)) 0 x :=
    ae_all_iff.mpr fun n => hf (s (t n))
  filter_upwards [hs0, ht2, hrel] with x hx0 hx2 hxeq
  have hprod : Tendsto (fun n => j * x * f (s (t n)) 0 x) atTop
      (𝓝 (j * x * z 0 x)) := (hx0.comp ht.tendsto_atTop).const_mul (j * x)
  exact tendsto_nhds_unique hx2
    (hprod.congr' (Eventually.of_forall fun n => (hxeq n).symm))

/-- The actual physical energy graph is closed in the Hilbert triple. -/
theorem physicalEnergyGraph_isClosed (j : ℝ) :
    IsClosed (physicalEnergyGraph j : Set PhysicalEnergyTriple) := by
  change IsClosed ({z : PhysicalEnergyTriple | HasWeakDerivativeL2 (z 0) (z 1)} ∩
    {z : PhysicalEnergyTriple | (z 2 : ℝ → ℝ) =ᵐ[volume] (fun x => j * x * z 0 x)})
  exact physical_weak_derivative_closed.inter (physical_weighted_position_closed j)

abbrev PhysicalEnergySpace (j : ℝ) := physicalEnergyGraph j

instance physicalEnergySpace_completeSpace (j : ℝ) : CompleteSpace (PhysicalEnergySpace j) :=
  (physicalEnergyGraph_isClosed j).isComplete.completeSpace_coe

def physicalEnergyCoordinate (j : ℝ) (i : Fin 3) :
    PhysicalEnergySpace j →L[ℝ] HermiteL2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => HermiteL2) i).comp
    (physicalEnergyGraph j).subtypeL

def physicalEnergyBase (j : ℝ) : PhysicalEnergySpace j →L[ℝ] HermiteL2 :=
  physicalEnergyCoordinate j 0

def physicalEnergyDerivative (j : ℝ) : PhysicalEnergySpace j →L[ℝ] HermiteL2 :=
  physicalEnergyCoordinate j 1

def physicalEnergyPosition (j : ℝ) : PhysicalEnergySpace j →L[ℝ] HermiteL2 :=
  physicalEnergyCoordinate j 2

@[simp] theorem physicalEnergyCoordinate_apply (j : ℝ) (i : Fin 3)
    (z : PhysicalEnergySpace j) : physicalEnergyCoordinate j i z = z.val i := rfl

theorem physicalEnergyCoordinate_norm_le (j : ℝ) (i : Fin 3) (z : PhysicalEnergySpace j) :
    ‖physicalEnergyCoordinate j i z‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z.val i

theorem physicalEnergyTriple_norm_sq (z : PhysicalEnergyTriple) :
    ‖z‖ ^ 2 = ‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_three]

@[simp] theorem physicalEnergyBase_apply (j : ℝ) (z : PhysicalEnergySpace j) :
    physicalEnergyBase j z = z.val 0 := rfl

@[simp] theorem physicalEnergyDerivative_apply (j : ℝ) (z : PhysicalEnergySpace j) :
    physicalEnergyDerivative j z = z.val 1 := rfl

@[simp] theorem physicalEnergyPosition_apply (j : ℝ) (z : PhysicalEnergySpace j) :
    physicalEnergyPosition j z = z.val 2 := rfl

theorem physicalEnergySpace_norm_sq (j : ℝ) (z : PhysicalEnergySpace j) :
    ‖z‖ ^ 2 = ‖physicalEnergyBase j z‖ ^ 2 +
      ‖physicalEnergyDerivative j z‖ ^ 2 + ‖physicalEnergyPosition j z‖ ^ 2 :=
  physicalEnergyTriple_norm_sq z.val

/-- A zero underlying L² function has zero first weak derivative. The
test separation is supplied by the proved compact-test graph theorem. -/
theorem HasWeakDerivativeL2.zero_left {d : HermiteL2}
    (hd : HasWeakDerivativeL2 0 d) : d = 0 := by
  have hweak : CentralCompactWeakEquation 2 0 d := by
    intro φ hφ hc
    have hφ' := (compactSmooth_energyDomain hφ hc).2.2.1
    have hHφ := compactSmooth_centralImage_memLp hφ hc 2
    calc
      (∫ x : ℝ, d x * φ x) = -(∫ x : ℝ, (0 : HermiteL2) x * deriv φ x) := hd φ hφ hc
      _ = 0 := by rw [← physicalTestPairing_apply (deriv φ) hφ' 0, map_zero, neg_zero]
      _ = ∫ x : ℝ, (0 : HermiteL2) x *
          liouvilleSchrodinger (2 ^ 2) centralRadius centralDensityRoot φ x := by
        rw [← physicalTestPairing_apply _ hHφ 0, map_zero]
  have hg := (centralClosedGraph_iff_compact_weak (by norm_num : (0 : ℝ) < 2) 0 d).mpr hweak
  exact centralClosedGraph_unique (by norm_num : (0 : ℝ) < 2) 0 d 0 hg
    (centralClosedGraph (by norm_num : (0 : ℝ) < 2)).zero_mem

theorem physicalEnergySpace_zero_base {j : ℝ} (z : PhysicalEnergySpace j)
    (hz : physicalEnergyBase j z = 0) : z = 0 := by
  have h0 : z.val 0 = 0 := hz
  have h1 : z.val 1 = 0 := by
    have hd := z.property.1
    rw [h0] at hd
    exact hd.zero_left
  have h2 : z.val 2 = 0 := by
    apply Lp.ext
    have hw := z.property.2
    rw [h0] at hw
    filter_upwards [hw, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx hzero
    rw [hx, hzero]
    simp
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem physicalEnergyBase_injective (j : ℝ) : Function.Injective (physicalEnergyBase j) := by
  intro z w hzw
  have hz : physicalEnergyBase j (z - w) = 0 := by rw [map_sub, hzw, sub_self]
  exact sub_eq_zero.mp (physicalEnergySpace_zero_base (z - w) hz)

theorem physicalTestPairing_toLp (φ : ℝ → ℝ) (hφ : MemLp φ 2 volume)
    (ψ : ℝ → ℝ) (hψ : MemLp ψ 2 volume) :
    physicalTestPairing φ hφ (hψ.toLp ψ) = ∫ x : ℝ, ψ x * φ x := by
  rw [physicalTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hψ] with x hx
  rw [hx]

/-- The actual classical derivative of an energy-domain function is also
its first weak derivative, by genuine whole-line integration by parts. -/
theorem hasWeakDerivativeL2_of_energyDomain {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ) :
    HasWeakDerivativeL2 (hψ.2.1.toLp ψ) (hψ.2.2.1.toLp (deriv ψ)) := by
  apply (hasWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  rw [physicalTestPairing_toLp, physicalTestPairing_toLp]
  have ht := compactSmooth_energyDomain hφ hc
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hψ.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (ht.1.differentiable (by norm_num) x).hasDerivAt)
    (hψ.2.1.integrable_mul ht.2.2.1)
    (hψ.2.2.1.integrable_mul ht.2.1)
    (hψ.2.1.integrable_mul ht.2.1)
  linarith

theorem physicalEnergy_weighted_memLp (j : ℝ) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ) :
    MemLp (fun x : ℝ => j * x * ψ x) 2 volume := by
  convert hψ.2.2.2.const_mul j using 1
  funext x
  ring

/-- The actual physical lift of a classical energy-domain function. -/
def physicalEnergyLift (j : ℝ) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ) : PhysicalEnergySpace j := by
  refine ⟨WithLp.toLp 2 ![hψ.2.1.toLp ψ, hψ.2.2.1.toLp (deriv ψ),
    (physicalEnergy_weighted_memLp j hψ).toLp (fun x : ℝ => j * x * ψ x)], ?_⟩
  refine ⟨hasWeakDerivativeL2_of_energyDomain hψ, ?_⟩
  filter_upwards [MemLp.coeFn_toLp hψ.2.1,
    MemLp.coeFn_toLp (physicalEnergy_weighted_memLp j hψ)] with x hu hw
  change ((physicalEnergy_weighted_memLp j hψ).toLp (fun x : ℝ => j * x * ψ x)) x =
    j * x * (hψ.2.1.toLp ψ) x
  rw [hu, hw]

@[simp] theorem physicalEnergyLift_base (j : ℝ) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ) :
    physicalEnergyBase j (physicalEnergyLift j hψ) = hψ.2.1.toLp ψ := rfl

@[simp] theorem physicalEnergyLift_derivative (j : ℝ) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ) :
    physicalEnergyDerivative j (physicalEnergyLift j hψ) = hψ.2.2.1.toLp (deriv ψ) := rfl

@[simp] theorem physicalEnergyLift_position (j : ℝ) {ψ : ℝ → ℝ}
    (hψ : OscillatorEnergyDomain ψ) :
    physicalEnergyPosition j (physicalEnergyLift j hψ) =
      (physicalEnergy_weighted_memLp j hψ).toLp (fun x : ℝ => j * x * ψ x) := rfl

end ContinuousFlexibility.Radial
