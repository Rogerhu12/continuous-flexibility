import ContinuousFlexibility.Radial.MorsePotentialEnergy
import ContinuousFlexibility.Radial.BufferIntervalForm
import ContinuousFlexibility.Radial.PositiveBufferEnergyVariational

/-!
# The actual Hilbert energy space for a positive-buffer problem

The three coordinates are the field, its distributional derivative, and its
absolute-potential weight. The defining relation is exactly the frozen
`SchrodingerEnergyLift`; only its Hilbert product norm differs from the public
product's max norm. Completeness therefore follows from the supplied actual
closed-form realization. Supported zero-boundary fields form a closed subspace.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

abbrev PositiveBufferEnergyTriple : Type := PiLp 2 (fun _ : Fin 3 => RadialL2)

/-- The genuine weak derivative and weighted field, in a Hilbert product. -/
def positiveBufferEnergyGraph (V : ℝ → ℝ) : Submodule ℝ PositiveBufferEnergyTriple where
  carrier := {z | WeakRadialDerivative (z 0) (z 1) ∧
    (z 2 : ℝ → ℝ) =ᵐ[volume] (fun x => sqrt (1 + |V x|) * z 0 x)}
  zero_mem' := by
    refine ⟨(morseWeakDerivative_iff_public _ _).mp morseWeakDerivativeL2_zero, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
    change (0 : RadialL2) x = sqrt (1 + |V x|) * (0 : RadialL2) x
    rw [hx]
    simp
  add_mem' := by
    intro z w hz hw
    refine ⟨(morseWeakDerivative_iff_public _ _).mp
      (((morseWeakDerivative_iff_public _ _).mpr hz.1).add
        ((morseWeakDerivative_iff_public _ _).mpr hw.1)), ?_⟩
    filter_upwards [hz.2, hw.2, Lp.coeFn_add (z 2) (w 2),
      Lp.coeFn_add (z 0) (w 0)] with x hx hy h2 h0
    change (z 2 + w 2) x = sqrt (1 + |V x|) * (z 0 + w 0) x
    rw [h2, h0]
    simp only [Pi.add_apply]
    rw [hx, hy]
    ring
  smul_mem' := by
    intro c z hz
    refine ⟨(morseWeakDerivative_iff_public _ _).mp
      (((morseWeakDerivative_iff_public _ _).mpr hz.1).smul c), ?_⟩
    filter_upwards [hz.2, Lp.coeFn_smul c (z 2), Lp.coeFn_smul c (z 0)] with x hx h2 h0
    change (c • z 2) x = sqrt (1 + |V x|) * (c • z 0) x
    rw [h2, h0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx]
    ring

theorem positiveBufferEnergyGraph_isClosed {V : ℝ → ℝ}
    (hV : ActualClosedFormRealization V) :
    IsClosed (positiveBufferEnergyGraph V : Set PositiveBufferEnergyTriple) := by
  let F : PositiveBufferEnergyTriple → RadialL2 × RadialL2 × RadialL2 :=
    fun z => (z 0, z 1, z 2)
  have hF : Continuous F :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RadialL2) 0).continuous.prodMk
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RadialL2) 1).continuous.prodMk
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RadialL2) 2).continuous)
  exact hV.2.1.preimage hF

abbrev PositiveBufferEnergy (V : ℝ → ℝ) : Type := positiveBufferEnergyGraph V

theorem positiveBufferEnergy_completeSpace {V : ℝ → ℝ}
    (hV : ActualClosedFormRealization V) : CompleteSpace (PositiveBufferEnergy V) :=
  (positiveBufferEnergyGraph_isClosed hV).isComplete.completeSpace_coe

def positiveBufferEnergyCoordinate (V : ℝ → ℝ) (i : Fin 3) :
    PositiveBufferEnergy V →L[ℝ] RadialL2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RadialL2) i).comp
    (positiveBufferEnergyGraph V).subtypeL

@[simp] theorem positiveBufferEnergyCoordinate_apply (V : ℝ → ℝ) (i : Fin 3)
    (z : PositiveBufferEnergy V) : positiveBufferEnergyCoordinate V i z = z.val i := rfl

theorem positiveBufferEnergyCoordinate_norm_le (V : ℝ → ℝ) (i : Fin 3)
    (z : PositiveBufferEnergy V) : ‖positiveBufferEnergyCoordinate V i z‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z.val i

theorem positiveBufferEnergy_norm_sq (V : ℝ → ℝ) (z : PositiveBufferEnergy V) :
    ‖z‖ ^ 2 = ‖positiveBufferEnergyCoordinate V 0 z‖ ^ 2 +
      ‖positiveBufferEnergyCoordinate V 1 z‖ ^ 2 +
      ‖positiveBufferEnergyCoordinate V 2 z‖ ^ 2 := by
  change ‖z.val‖ ^ 2 = ‖z.val 0‖ ^ 2 + ‖z.val 1‖ ^ 2 + ‖z.val 2‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_three]

theorem positiveBufferEnergy_derivative_weak (V : ℝ → ℝ) (z : PositiveBufferEnergy V) :
    WeakRadialDerivative (positiveBufferEnergyCoordinate V 0 z)
      (positiveBufferEnergyCoordinate V 1 z) := z.property.1

theorem positiveBufferEnergy_weight_ae (V : ℝ → ℝ) (z : PositiveBufferEnergy V) :
    (positiveBufferEnergyCoordinate V 2 z : ℝ → ℝ) =ᵐ[volume]
      (fun x => sqrt (1 + |V x|) * positiveBufferEnergyCoordinate V 0 z x) := z.property.2

theorem positiveBufferEnergy_base_injective (V : ℝ → ℝ) :
    Function.Injective (positiveBufferEnergyCoordinate V 0) := by
  suffices hz : ∀ z : PositiveBufferEnergy V,
      positiveBufferEnergyCoordinate V 0 z = 0 → z = 0 by
    intro z w hzw
    exact sub_eq_zero.mp (hz (z - w) (by rw [map_sub, hzw, sub_self]))
  intro z h0
  have h1 : z.val 1 = 0 := by
    have hd := (morseWeakDerivative_iff_public _ _).mpr
      (positiveBufferEnergy_derivative_weak V z)
    rw [h0] at hd
    exact hd.unique morseWeakDerivativeL2_zero
  have h2 : z.val 2 = 0 := by
    apply Lp.ext
    have hw := positiveBufferEnergy_weight_ae V z
    rw [h0] at hw
    filter_upwards [hw, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx hzero
    change positiveBufferEnergyCoordinate V 2 z x = (0 : RadialL2) x
    rw [hx, hzero]
    simp
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Zero-boundary variations are genuine global energy fields whose base
vanishes outside the region. Their boundary traces vanish by the trace theorem. -/
def positiveBufferSupportedEnergyGraph (V : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    Submodule ℝ (PositiveBufferEnergy V) :=
  ((bufferL2IndicatorCLM sᶜ hs.compl).comp (positiveBufferEnergyCoordinate V 0)).ker

theorem mem_positiveBufferSupportedEnergyGraph_iff (V : ℝ → ℝ)
    (s : Set ℝ) (hs : MeasurableSet s) (z : PositiveBufferEnergy V) :
    z ∈ positiveBufferSupportedEnergyGraph V s hs ↔
      (positiveBufferEnergyCoordinate V 0 z : ℝ → ℝ) =ᵐ[volume.restrict sᶜ] (fun _ => 0) := by
  rw [positiveBufferSupportedEnergyGraph, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    bufferL2IndicatorCLM_apply, bufferL2Indicator_eq_zero_iff]

theorem positiveBufferSupportedEnergyGraph_isClosed (V : ℝ → ℝ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    IsClosed (positiveBufferSupportedEnergyGraph V s hs : Set (PositiveBufferEnergy V)) :=
  ContinuousLinearMap.isClosed_ker _

theorem positiveBufferSupportedEnergy_completeSpace {V : ℝ → ℝ}
    (hV : ActualClosedFormRealization V) (s : Set ℝ) (hs : MeasurableSet s) :
    CompleteSpace (positiveBufferSupportedEnergyGraph V s hs) := by
  letI := positiveBufferEnergy_completeSpace hV
  exact (positiveBufferSupportedEnergyGraph_isClosed V s hs).isComplete.completeSpace_coe

/-- The signed potential coefficient acts boundedly on the absolute weighted
coordinate, even when the potential is unbounded. -/
def positiveBufferPotentialCoefficient (V : ℝ → ℝ) (x : ℝ) : ℝ := V x / (1 + |V x|)

theorem continuous_positiveBufferPotentialCoefficient {V : ℝ → ℝ} (hV : Continuous V) :
    Continuous (positiveBufferPotentialCoefficient V) :=
  hV.div (continuous_const.add hV.abs) (fun x => (by positivity : (1 + |V x|) ≠ 0))

theorem positiveBufferPotentialCoefficient_abs_le_one (V : ℝ → ℝ) (x : ℝ) :
    |positiveBufferPotentialCoefficient V x| ≤ 1 := by
  unfold positiveBufferPotentialCoefficient
  rw [abs_div, abs_of_pos (by positivity : 0 < 1 + |V x|)]
  exact (div_le_one (by positivity : 0 < 1 + |V x|)).mpr (by linarith [abs_nonneg (V x)])

def positiveBufferPotentialMultiplier (V : ℝ → ℝ) (hV : Continuous V) :
    RadialL2 →L[ℝ] RadialL2 :=
  morseL2Multiplier (positiveBufferPotentialCoefficient V)
    (continuous_positiveBufferPotentialCoefficient hV) 1
    (positiveBufferPotentialCoefficient_abs_le_one V)

local instance (V : ℝ → ℝ) : SeminormedAddCommGroup (PositiveBufferEnergy V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance (V : ℝ → ℝ) : NormedSpace ℝ (PositiveBufferEnergy V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The physical energy form uses the real derivative and real potential;
the bounded coefficient is only its continuous-operator representation. -/
def positiveBufferEnergyForm (V : ℝ → ℝ) (hV : Continuous V) :
    PositiveBufferEnergy V →L[ℝ] PositiveBufferEnergy V →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (positiveBufferEnergyCoordinate V 1)
      (positiveBufferEnergyCoordinate V 1) +
    (innerSL ℝ).bilinearComp
      ((positiveBufferPotentialMultiplier V hV).comp (positiveBufferEnergyCoordinate V 2))
      (positiveBufferEnergyCoordinate V 2)

theorem positiveBufferEnergyForm_apply (V : ℝ → ℝ) (hV : Continuous V)
    (u v : PositiveBufferEnergy V) :
    positiveBufferEnergyForm V hV u v =
      ⟪positiveBufferEnergyCoordinate V 1 u, positiveBufferEnergyCoordinate V 1 v⟫_ℝ +
      ⟪positiveBufferPotentialMultiplier V hV (positiveBufferEnergyCoordinate V 2 u),
        positiveBufferEnergyCoordinate V 2 v⟫_ℝ := rfl

end ContinuousFlexibility.Radial
