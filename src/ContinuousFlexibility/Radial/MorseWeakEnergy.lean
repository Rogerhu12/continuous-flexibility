import ContinuousFlexibility.Radial.MorseModel
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The actual weak physical Morse energy space

The energy coordinates are genuine Lebesgue `L²` classes. Weak differentiation
and multiplication by `exp (-x)` are characterized by actual smooth compact
tests. Their graph is proved closed; no closed-operator or spectral hypothesis
is part of the construction. The physical Morse form is built on this graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

abbrev MorseL2 : Type := Lp ℝ 2 (volume : Measure ℝ)
abbrev MorseEnergyTriple : Type := PiLp 2 (fun _ : Fin 3 => MorseL2)

theorem compactSmooth_morseEnergyDomain {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : MorseEnergyDomain φ := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  refine ⟨hφ.of_le (by simp), hφ.continuous.memLp_of_hasCompactSupport hc,
    hd.continuous.memLp_of_hasCompactSupport hc.deriv, ?_⟩
  exact (continuous_id.neg.rexp.mul hφ.continuous).memLp_of_hasCompactSupport hc.mul_left

def morseTestPairing (φ : ℝ → ℝ) (hφ : MemLp φ 2 volume) : MorseL2 →L[ℝ] ℝ :=
  innerSL ℝ (hφ.toLp φ)

theorem morseTestPairing_apply (φ : ℝ → ℝ) (hφ : MemLp φ 2 volume) (u : MorseL2) :
    morseTestPairing φ hφ u = ∫ x : ℝ, u x * φ x := by
  change ⟪hφ.toLp φ, u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]

theorem morseTestPairing_toLp (φ : ℝ → ℝ) (hφ : MemLp φ 2 volume)
    (ψ : ℝ → ℝ) (hψ : MemLp ψ 2 volume) :
    morseTestPairing φ hφ (hψ.toLp ψ) = ∫ x : ℝ, ψ x * φ x := by
  rw [morseTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hψ] with x hx
  rw [hx]

/-- The first distributional derivative, expressed using actual compact tests. -/
def MorseWeakDerivativeL2 (u d : MorseL2) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x : ℝ, d x * φ x) = -(∫ x : ℝ, u x * deriv φ x)

theorem morseWeakDerivativeL2_iff_pairings (u d : MorseL2) :
    MorseWeakDerivativeL2 u d ↔
      ∀ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        morseTestPairing φ (compactSmooth_morseEnergyDomain hφ hc).2.1 d =
          -morseTestPairing (deriv φ) (compactSmooth_morseEnergyDomain hφ hc).2.2.1 u := by
  constructor <;> intro h φ hφ hc
  · rw [morseTestPairing_apply, morseTestPairing_apply]
    exact h φ hφ hc
  · have hh := h φ hφ hc
    rwa [morseTestPairing_apply, morseTestPairing_apply] at hh

theorem morseWeakDerivativeL2_zero : MorseWeakDerivativeL2 0 0 := by
  apply (morseWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  simp only [map_zero, neg_zero]

theorem MorseWeakDerivativeL2.add {u d v e : MorseL2}
    (hu : MorseWeakDerivativeL2 u d) (hv : MorseWeakDerivativeL2 v e) :
    MorseWeakDerivativeL2 (u + v) (d + e) := by
  apply (morseWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  rw [map_add, map_add,
    (morseWeakDerivativeL2_iff_pairings _ _).mp hu φ hφ hc,
    (morseWeakDerivativeL2_iff_pairings _ _).mp hv φ hφ hc]
  ring

theorem MorseWeakDerivativeL2.smul {u d : MorseL2}
    (hu : MorseWeakDerivativeL2 u d) (a : ℝ) :
    MorseWeakDerivativeL2 (a • u) (a • d) := by
  apply (morseWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  rw [map_smul, map_smul, (morseWeakDerivativeL2_iff_pairings _ _).mp hu φ hφ hc]
  simp only [smul_eq_mul]
  ring

/-- Uniqueness follows from the fundamental lemma for actual locally
integrable functions, without any Hermite or spectral argument. -/
theorem MorseWeakDerivativeL2.unique {u d e : MorseL2}
    (hd : MorseWeakDerivativeL2 u d) (he : MorseWeakDerivativeL2 u e) : d = e := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp d).locallyIntegrable (by norm_num))
    ((Lp.memLp e).locallyIntegrable (by norm_num))
  intro φ hφ hc
  simpa only [smul_eq_mul, mul_comm] using (hd φ hφ hc).trans (he φ hφ hc).symm

/-- Compact testing detects the actual unbounded multiplier `exp (-x)`. -/
theorem morseWeightRelation_iff_pairings (u z : MorseL2) :
    ((z : ℝ → ℝ) =ᵐ[volume] (fun x => exp (-x) * u x)) ↔
      ∀ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        morseTestPairing φ (compactSmooth_morseEnergyDomain hφ hc).2.1 z =
          morseTestPairing (fun x => exp (-x) * φ x)
            (compactSmooth_morseEnergyDomain hφ hc).2.2.2 u := by
  constructor
  · intro hz φ hφ hc
    rw [morseTestPairing_apply, morseTestPairing_apply]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    rw [hx]
    ring
  · intro hz
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp z).locallyIntegrable (by norm_num))
      (LocallyIntegrable.continuous_mul continuous_id.neg.rexp
        ((Lp.memLp u).locallyIntegrable (by norm_num)))
    intro φ hφ hc
    have hh := hz φ hφ hc
    rw [morseTestPairing_apply, morseTestPairing_apply] at hh
    simpa only [smul_eq_mul, Pi.neg_apply, id_eq, mul_assoc, mul_left_comm, mul_comm] using hh

/-- Actual weak differentiation and exponential weighting as a linear graph. -/
def morseEnergyGraph : Submodule ℝ MorseEnergyTriple where
  carrier := {z | MorseWeakDerivativeL2 (z 0) (z 1) ∧
    ∀ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      morseTestPairing φ (compactSmooth_morseEnergyDomain hφ hc).2.1 (z 2) =
        morseTestPairing (fun x => exp (-x) * φ x)
          (compactSmooth_morseEnergyDomain hφ hc).2.2.2 (z 0)}
  zero_mem' := ⟨morseWeakDerivativeL2_zero, by intros; simp⟩
  add_mem' := by
    intro z w hz hw
    refine ⟨hz.1.add hw.1, ?_⟩
    intro φ hφ hc
    change morseTestPairing φ _ (z 2 + w 2) = morseTestPairing _ _ (z 0 + w 0)
    rw [map_add, map_add, hz.2 φ hφ hc, hw.2 φ hφ hc]
  smul_mem' := by
    intro a z hz
    refine ⟨hz.1.smul a, ?_⟩
    intro φ hφ hc
    change morseTestPairing φ _ (a • z 2) = morseTestPairing _ _ (a • z 0)
    rw [map_smul, map_smul, hz.2 φ hφ hc]

theorem mem_morseEnergyGraph_iff (z : MorseEnergyTriple) :
    z ∈ morseEnergyGraph ↔ MorseWeakDerivativeL2 (z 0) (z 1) ∧
      (z 2 : ℝ → ℝ) =ᵐ[volume] (fun x => exp (-x) * z 0 x) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr_right (fun _ => (morseWeightRelation_iff_pairings _ _).symm)

/-- The graph is an intersection of kernels of actual continuous integral
functionals, so both differential coordinates persist under `L²` limits. -/
theorem morseEnergyGraph_isClosed : IsClosed (morseEnergyGraph : Set MorseEnergyTriple) := by
  have hD : IsClosed {z : MorseEnergyTriple | MorseWeakDerivativeL2 (z 0) (z 1)} := by
    have heq : {z : MorseEnergyTriple | MorseWeakDerivativeL2 (z 0) (z 1)} =
        ⋂ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
          {z : MorseEnergyTriple |
            morseTestPairing φ (compactSmooth_morseEnergyDomain hφ hc).2.1 (z 1) =
              -morseTestPairing (deriv φ) (compactSmooth_morseEnergyDomain hφ hc).2.2.1 (z 0)} := by
      ext z
      simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using
        morseWeakDerivativeL2_iff_pairings (z 0) (z 1)
    rw [heq]
    apply isClosed_iInter
    intro φ
    apply isClosed_iInter
    intro hφ
    apply isClosed_iInter
    intro hc
    exact isClosed_eq
      ((morseTestPairing φ (compactSmooth_morseEnergyDomain hφ hc).2.1).continuous.comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => MorseL2) 1).continuous)
      (((morseTestPairing (deriv φ) (compactSmooth_morseEnergyDomain hφ hc).2.2.1).continuous.comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => MorseL2) 0).continuous).neg)
  have hW : IsClosed {z : MorseEnergyTriple |
      ∀ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        morseTestPairing φ (compactSmooth_morseEnergyDomain hφ hc).2.1 (z 2) =
          morseTestPairing (fun x => exp (-x) * φ x)
            (compactSmooth_morseEnergyDomain hφ hc).2.2.2 (z 0)} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro φ
    apply isClosed_iInter
    intro hφ
    apply isClosed_iInter
    intro hc
    exact isClosed_eq
      ((morseTestPairing φ (compactSmooth_morseEnergyDomain hφ hc).2.1).continuous.comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => MorseL2) 2).continuous)
      ((morseTestPairing (fun x => exp (-x) * φ x)
        (compactSmooth_morseEnergyDomain hφ hc).2.2.2).continuous.comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => MorseL2) 0).continuous)
  exact hD.inter hW

abbrev MorseWeakEnergy : Type := morseEnergyGraph

instance morseWeakEnergy_completeSpace : CompleteSpace MorseWeakEnergy :=
  morseEnergyGraph_isClosed.isComplete.completeSpace_coe

def morseEnergyCoordinate (i : Fin 3) : MorseWeakEnergy →L[ℝ] MorseL2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => MorseL2) i).comp morseEnergyGraph.subtypeL

def morseEnergyBase : MorseWeakEnergy →L[ℝ] MorseL2 := morseEnergyCoordinate 0
def morseEnergyDerivative : MorseWeakEnergy →L[ℝ] MorseL2 := morseEnergyCoordinate 1
def morseEnergyWeight : MorseWeakEnergy →L[ℝ] MorseL2 := morseEnergyCoordinate 2

@[simp] theorem morseEnergyCoordinate_apply (i : Fin 3) (z : MorseWeakEnergy) :
    morseEnergyCoordinate i z = z.val i := rfl

theorem morseEnergyCoordinate_norm_le (i : Fin 3) (z : MorseWeakEnergy) :
    ‖morseEnergyCoordinate i z‖ ≤ ‖z‖ := PiLp.norm_apply_le z.val i

theorem morseWeakEnergy_norm_sq (z : MorseWeakEnergy) :
    ‖z‖ ^ 2 = ‖morseEnergyBase z‖ ^ 2 +
      ‖morseEnergyDerivative z‖ ^ 2 + ‖morseEnergyWeight z‖ ^ 2 := by
  change ‖z.val‖ ^ 2 = ‖z.val 0‖ ^ 2 + ‖z.val 1‖ ^ 2 + ‖z.val 2‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_three]

theorem morseEnergyDerivative_weak (z : MorseWeakEnergy) :
    MorseWeakDerivativeL2 (morseEnergyBase z) (morseEnergyDerivative z) := z.property.1

theorem morseEnergyWeight_ae (z : MorseWeakEnergy) :
    (morseEnergyWeight z : ℝ → ℝ) =ᵐ[volume]
      (fun x => exp (-x) * morseEnergyBase z x) :=
  (mem_morseEnergyGraph_iff z.val).mp z.property |>.2

theorem morseEnergyBase_injective : Function.Injective morseEnergyBase := by
  suffices hz : ∀ z : MorseWeakEnergy, morseEnergyBase z = 0 → z = 0 by
    intro z w hzw
    exact sub_eq_zero.mp (hz (z - w) (by rw [map_sub, hzw, sub_self]))
  intro z h0
  have h1 : z.val 1 = 0 := by
    have hd := morseEnergyDerivative_weak z
    rw [h0] at hd
    exact hd.unique morseWeakDerivativeL2_zero
  have h2 : z.val 2 = 0 := by
    apply Lp.ext
    have hw := morseEnergyWeight_ae z
    rw [h0] at hw
    filter_upwards [hw, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx hzero
    change morseEnergyWeight z x = (0 : MorseL2) x
    rw [hx, hzero]
    simp
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem morseWeakDerivativeL2_of_energyDomain {ψ : ℝ → ℝ} (hψ : MorseEnergyDomain ψ) :
    MorseWeakDerivativeL2 (hψ.2.1.toLp ψ) (hψ.2.2.1.toLp (deriv ψ)) := by
  apply (morseWeakDerivativeL2_iff_pairings _ _).mpr
  intro φ hφ hc
  rw [morseTestPairing_toLp, morseTestPairing_toLp]
  have ht := compactSmooth_morseEnergyDomain hφ hc
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (hψ.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (ht.1.differentiable (by norm_num) x).hasDerivAt)
    (hψ.2.1.integrable_mul ht.2.2.1)
    (hψ.2.2.1.integrable_mul ht.2.1) (hψ.2.1.integrable_mul ht.2.1)
  linarith

def morseEnergyLift {ψ : ℝ → ℝ} (hψ : MorseEnergyDomain ψ) : MorseWeakEnergy := by
  refine ⟨WithLp.toLp 2 ![hψ.2.1.toLp ψ, hψ.2.2.1.toLp (deriv ψ),
    hψ.2.2.2.toLp (fun x => exp (-x) * ψ x)], ?_⟩
  apply (mem_morseEnergyGraph_iff _).mpr
  refine ⟨morseWeakDerivativeL2_of_energyDomain hψ, ?_⟩
  filter_upwards [MemLp.coeFn_toLp hψ.2.1, MemLp.coeFn_toLp hψ.2.2.2] with x hu hw
  change (hψ.2.2.2.toLp (fun x => exp (-x) * ψ x)) x = exp (-x) * (hψ.2.1.toLp ψ) x
  rw [hu, hw]

@[simp] theorem morseEnergyLift_base {ψ : ℝ → ℝ} (hψ : MorseEnergyDomain ψ) :
    morseEnergyBase (morseEnergyLift hψ) = hψ.2.1.toLp ψ := rfl

@[simp] theorem morseEnergyLift_derivative {ψ : ℝ → ℝ} (hψ : MorseEnergyDomain ψ) :
    morseEnergyDerivative (morseEnergyLift hψ) = hψ.2.2.1.toLp (deriv ψ) := rfl

@[simp] theorem morseEnergyLift_weight {ψ : ℝ → ℝ} (hψ : MorseEnergyDomain ψ) :
    morseEnergyWeight (morseEnergyLift hψ) =
      hψ.2.2.2.toLp (fun x => exp (-x) * ψ x) := rfl

def morseGroundEnergy {α w : ℝ} (hα : 0 < α) (hw : 0 < w) : MorseWeakEnergy :=
  morseEnergyLift (morseGround_energyDomain hα hw)

/-- Only `L²` density is asserted here. Density of compact tests in the
full energy norm is a separate cutoff-and-regularization obligation. -/
theorem morseEnergyBase_denseRange : DenseRange morseEnergyBase := by
  let K : Submodule ℝ MorseL2 := morseEnergyBase.range
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    rw [Submodule.mem_bot]
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp u).locallyIntegrable (by norm_num))
    intro φ hφ hc
    let ht := compactSmooth_morseEnergyDomain hφ hc
    have hmem : morseEnergyBase (morseEnergyLift ht) ∈ K :=
      ⟨morseEnergyLift ht, rfl⟩
    have hh := (Submodule.mem_orthogonal K u).mp hu _ hmem
    rw [morseEnergyLift_base] at hh
    change morseTestPairing φ ht.2.1 u = 0 at hh
    rw [morseTestPairing_apply] at hh
    simpa only [smul_eq_mul, mul_comm] using hh
  have hd : Dense (K : Set MorseL2) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (K.topologicalClosure_eq_top_iff.mpr horth)
  exact hd

local instance : SeminormedAddCommGroup (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance : NormedSpace ℝ (MorseWeakEnergy →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def morseCoordinatePairing (i k : Fin 3) :
    MorseWeakEnergy →L[ℝ] MorseWeakEnergy →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (morseEnergyCoordinate i) (morseEnergyCoordinate k)

/-- The physical Morse form, before introducing an associated operator. -/
def morsePhysicalForm (α w V : ℝ) :
    MorseWeakEnergy →L[ℝ] MorseWeakEnergy →L[ℝ] ℝ :=
  morseCoordinatePairing 1 1 + w ^ 2 • morseCoordinatePairing 2 2 -
    (w * (2 * α + 1)) • morseCoordinatePairing 2 0 + V • morseCoordinatePairing 0 0

theorem morsePhysicalForm_apply (α w V : ℝ) (u v : MorseWeakEnergy) :
    morsePhysicalForm α w V u v =
      ⟪morseEnergyDerivative u, morseEnergyDerivative v⟫_ℝ +
      w ^ 2 * ⟪morseEnergyWeight u, morseEnergyWeight v⟫_ℝ -
      w * (2 * α + 1) * ⟪morseEnergyWeight u, morseEnergyBase v⟫_ℝ +
      V * ⟪morseEnergyBase u, morseEnergyBase v⟫_ℝ := rfl

theorem morsePhysicalForm_bound (α w V : ℝ) (u v : MorseWeakEnergy) :
    ‖morsePhysicalForm α w V u v‖ ≤ ‖morsePhysicalForm α w V‖ * ‖u‖ * ‖v‖ :=
  (morsePhysicalForm α w V).le_opNorm₂ u v

theorem morseWeight_pairing_symm (u v : MorseWeakEnergy) :
    ⟪morseEnergyWeight u, morseEnergyBase v⟫_ℝ =
      ⟪morseEnergyWeight v, morseEnergyBase u⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [morseEnergyWeight_ae u, morseEnergyWeight_ae v] with x hu hv
  rw [hu, hv]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem morsePhysicalForm_symm (α w V : ℝ) (u v : MorseWeakEnergy) :
    morsePhysicalForm α w V u v = morsePhysicalForm α w V v u := by
  rw [morsePhysicalForm_apply, morsePhysicalForm_apply,
    real_inner_comm (morseEnergyDerivative v) (morseEnergyDerivative u),
    real_inner_comm (morseEnergyWeight v) (morseEnergyWeight u),
    morseWeight_pairing_symm u v,
    real_inner_comm (morseEnergyBase v) (morseEnergyBase u)]

/-- An actual square in `L²` controls the negative mixed potential term. -/
theorem morsePhysicalForm_lower_bound (α w V : ℝ) (u : MorseWeakEnergy) :
    ‖morseEnergyDerivative u‖ ^ 2 + (w ^ 2 / 2) * ‖morseEnergyWeight u‖ ^ 2 +
      (V - (2 * α + 1) ^ 2 / 2) * ‖morseEnergyBase u‖ ^ 2 ≤
        morsePhysicalForm α w V u u := by
  have hs : 0 ≤ ⟪w • morseEnergyWeight u - (2 * α + 1) • morseEnergyBase u,
      w • morseEnergyWeight u - (2 * α + 1) • morseEnergyBase u⟫_ℝ :=
    real_inner_self_nonneg
  rw [real_inner_sub_sub_self] at hs
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hs
  simp only [morsePhysicalForm_apply, real_inner_self_eq_norm_sq]
  nlinarith [hs]

def morseFormShift (α V : ℝ) : ℝ := 1 + (2 * α + 1) ^ 2 / 2 + |V|
def morseCoercivityConstant (w : ℝ) : ℝ := min 1 (w ^ 2 / 2)

def morseShiftedForm (α w V : ℝ) :
    MorseWeakEnergy →L[ℝ] MorseWeakEnergy →L[ℝ] ℝ :=
  morsePhysicalForm α w V + morseFormShift α V • morseCoordinatePairing 0 0

theorem morseShiftedForm_apply (α w V : ℝ) (u v : MorseWeakEnergy) :
    morseShiftedForm α w V u v = morsePhysicalForm α w V u v +
      morseFormShift α V * ⟪morseEnergyBase u, morseEnergyBase v⟫_ℝ := rfl

theorem morseCoercivityConstant_pos {w : ℝ} (hw : 0 < w) :
    0 < morseCoercivityConstant w :=
  lt_min (by norm_num) (div_pos (sq_pos_of_pos hw) (by norm_num))

theorem morseShiftedForm_coercive_bound (α w V : ℝ) (u : MorseWeakEnergy) :
    morseCoercivityConstant w * ‖u‖ ^ 2 ≤ morseShiftedForm α w V u u := by
  have hb := morsePhysicalForm_lower_bound α w V u
  have hc0 : morseCoercivityConstant w ≤ 1 := min_le_left _ _
  have hc2 : morseCoercivityConstant w ≤ w ^ 2 / 2 := min_le_right _ _
  have h0 := mul_le_mul_of_nonneg_right hc0 (sq_nonneg ‖morseEnergyBase u‖)
  have h1 := mul_le_mul_of_nonneg_right hc0 (sq_nonneg ‖morseEnergyDerivative u‖)
  have h2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖morseEnergyWeight u‖)
  have hV : 0 ≤ V + |V| := by linarith [neg_le_abs V]
  have hVu := mul_nonneg hV (sq_nonneg ‖morseEnergyBase u‖)
  rw [morseWeakEnergy_norm_sq, morseShiftedForm_apply, real_inner_self_eq_norm_sq]
  unfold morseFormShift
  nlinarith

theorem morseShiftedForm_isCoercive (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    IsCoercive (morseShiftedForm α w V) := by
  refine ⟨morseCoercivityConstant w, morseCoercivityConstant_pos hw, ?_⟩
  intro u
  simpa only [pow_two, mul_assoc] using morseShiftedForm_coercive_bound α w V u

theorem morseShiftedForm_norm_equivalence (α V : ℝ) {w : ℝ} (hw : 0 < w) :
    0 < morseCoercivityConstant w ∧ ∀ u : MorseWeakEnergy,
      morseCoercivityConstant w * ‖u‖ ^ 2 ≤ morseShiftedForm α w V u u ∧
      morseShiftedForm α w V u u ≤ ‖morseShiftedForm α w V‖ * ‖u‖ ^ 2 := by
  refine ⟨morseCoercivityConstant_pos hw, fun u => ⟨morseShiftedForm_coercive_bound α w V u, ?_⟩⟩
  calc
    _ ≤ ‖morseShiftedForm α w V u u‖ := le_abs_self _
    _ ≤ _ := by simpa only [pow_two, mul_assoc] using (morseShiftedForm α w V).le_opNorm₂ u u

theorem morseL2_inner_toLp {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x : ℝ, f x * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hfx hgx
  rw [hfx, hgx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem morsePhysicalForm_lift_apply {φ ψ : ℝ → ℝ}
    (hφ : MorseEnergyDomain φ) (hψ : MorseEnergyDomain ψ) (α w V : ℝ) :
    morsePhysicalForm α w V (morseEnergyLift hφ) (morseEnergyLift hψ) =
      (∫ x : ℝ, deriv φ x * deriv ψ x) +
      w ^ 2 * (∫ x : ℝ, (exp (-x) * φ x) * (exp (-x) * ψ x)) -
      w * (2 * α + 1) * (∫ x : ℝ, (exp (-x) * φ x) * ψ x) +
      V * (∫ x : ℝ, φ x * ψ x) := by
  rw [morsePhysicalForm_apply]
  simp only [morseEnergyLift_base, morseEnergyLift_derivative, morseEnergyLift_weight,
    morseL2_inner_toLp]

/-- The closed form agrees with the actual Morse differential expression
against every smooth compact test. No image-integrability premise is needed. -/
theorem morsePhysicalForm_compact_test {ψ φ : ℝ → ℝ} (hψ : MorseEnergyDomain ψ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (α w V : ℝ) :
    morsePhysicalForm α w V (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc))
      (morseEnergyLift hψ) = ∫ x : ℝ, φ x * morseExpression α w V ψ x := by
  let ht := compactSmooth_morseEnergyDomain hφ hc
  have hdd : Continuous (deriv (deriv ψ)) :=
    ((contDiff_succ_iff_deriv (n := (1 : ℕ∞ω))).mp hψ.1).2.2.continuous_deriv_one
  have hsecond : Integrable (fun x : ℝ => φ x * deriv (deriv ψ) x) volume :=
    (hφ.continuous.mul hdd).integrable_of_hasCompactSupport hc.mul_right
  have hww := ht.2.2.2.integrable_mul hψ.2.2.2
  have hwu := ht.2.2.2.integrable_mul hψ.2.1
  have huu := ht.2.1.integrable_mul hψ.2.1
  have hp := ((hww.const_mul (w ^ 2)).sub (hwu.const_mul (w * (2 * α + 1)))).add
    (huu.const_mul V)
  have hI := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => (ht.1.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hψ.1.differentiable_deriv_two x).hasDerivAt)
    hsecond (ht.2.2.1.integrable_mul hψ.2.2.1) (ht.2.1.integrable_mul hψ.2.2.1)
  have hsplit := integral_add hsecond.neg hp
  have hpsplit := integral_add ((hww.const_mul (w ^ 2)).sub
    (hwu.const_mul (w * (2 * α + 1)))) (huu.const_mul V)
  have hpdiff := integral_sub (hww.const_mul (w ^ 2)) (hwu.const_mul (w * (2 * α + 1)))
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hsplit hpsplit hpdiff
  symm
  calc
    _ = ∫ x : ℝ, -(φ x * deriv (deriv ψ) x) +
        (w ^ 2 * ((exp (-x) * φ x) * (exp (-x) * ψ x)) -
          w * (2 * α + 1) * ((exp (-x) * φ x) * ψ x) + V * (φ x * ψ x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold morseExpression
      ring
    _ = _ := by
      rw [hsplit, integral_neg, hpsplit, hpdiff]
      simp only [integral_const_mul]
      rw [hI, morsePhysicalForm_lift_apply]
      ring

theorem morseGroundEnergy_compact_pairing {α w : ℝ} (hα : 0 < α) (hw : 0 < w)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (V : ℝ) :
    morsePhysicalForm α w V (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc))
      (morseGroundEnergy hα hw) =
        (V - α ^ 2) * (∫ x : ℝ, φ x * morseGround α w x) := by
  unfold morseGroundEnergy
  rw [morsePhysicalForm_compact_test (morseGround_energyDomain hα hw) hφ hc]
  simp_rw [morseGround_equation]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end ContinuousFlexibility.Radial
