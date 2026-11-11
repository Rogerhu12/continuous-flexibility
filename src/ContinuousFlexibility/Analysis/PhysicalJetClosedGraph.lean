import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# The actual weighted physical jet graph is closed

Each material weight is at least one. Its reciprocal is therefore a bounded
multiplier on the cylinder `L²` space and recovers the unweighted derivative
from the weighted coordinate. The graph is an intersection of closed
preimages of the weak derivative graph and the angular reflection condition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff

private theorem cylinderMemLp_bounded_mul {χ f : PolarPoint → ℝ}
    (hχ : Continuous χ) {C : ℝ} (hC : ∀ p, |χ p| ≤ C)
    (hf : MemLp f 2 materialCylinderMeasure) :
    MemLp (fun p => χ p * f p) 2 materialCylinderMeasure := by
  apply hf.of_le_mul (c := C) (hχ.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with p
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC p) (abs_nonneg _)

private def cylinderMul (χ : PolarPoint → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ p, |χ p| ≤ C) (u : CylinderL2) : CylinderL2 :=
  (cylinderMemLp_bounded_mul hχ hC (Lp.memLp u)).toLp (fun p => χ p * u p)

private theorem cylinderMul_ae (χ : PolarPoint → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ p, |χ p| ≤ C) (u : CylinderL2) :
    (cylinderMul χ hχ C hC u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (fun p => χ p * u p) := MemLp.coeFn_toLp _

private def cylinderBoundedMultiplier (χ : PolarPoint → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ p, |χ p| ≤ C) : CylinderL2 →L[ℝ] CylinderL2 := by
  let L : CylinderL2 →ₗ[ℝ] CylinderL2 :=
    { toFun := cylinderMul χ hχ C hC
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [cylinderMul_ae χ hχ C hC (u + v), cylinderMul_ae χ hχ C hC u,
          cylinderMul_ae χ hχ C hC v, Lp.coeFn_add u v,
          Lp.coeFn_add (cylinderMul χ hχ C hC u) (cylinderMul χ hχ C hC v)] with p hsum hu hv h₀ h₁
        rw [hsum, h₁, h₀]
        simp only [Pi.add_apply]
        rw [hu, hv]
        ring
      map_smul' := by
        intro a u
        apply Lp.ext
        filter_upwards [cylinderMul_ae χ hχ C hC (a • u), cylinderMul_ae χ hχ C hC u,
          Lp.coeFn_smul a u, Lp.coeFn_smul a (cylinderMul χ hχ C hC u)] with p hmul hu h₀ h₁
        change cylinderMul χ hχ C hC (a • u) p = (a • cylinderMul χ hχ C hC u) p
        rw [hmul, h₁, h₀]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hu]
        ring }
  refine L.mkContinuous C (fun u => ?_)
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cylinderMul_ae χ hχ C hC u] with p hp
  change ‖cylinderMul χ hχ C hC u p‖ ≤ C * ‖u p‖
  rw [hp]
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC p) (abs_nonneg _)

private theorem cylinderBoundedMultiplier_ae (χ : PolarPoint → ℝ) (hχ : Continuous χ) (C : ℝ)
    (hC : ∀ p, |χ p| ≤ C) (u : CylinderL2) :
    (cylinderBoundedMultiplier χ hχ C hC u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (fun p => χ p * u p) := cylinderMul_ae χ hχ C hC u

def physicalJetCoordinate (s : ℕ) (j : JetIndex s) : PhysicalJetHilbert s →L[ℝ] CylinderL2 :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex s => CylinderL2) j

@[simp] theorem physicalJetCoordinate_apply (s : ℕ) (j : JetIndex s) (z : PhysicalJetHilbert s) :
    physicalJetCoordinate s j z = z j := rfl

def physicalJetWeight (T : MaterialData) {s : ℕ} (j : JetIndex s) (p : PolarPoint) : ℝ :=
  T.M (T.radius p.1) ^ (j.val 2).val

theorem physicalJetWeight_one_le {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {s : ℕ} (j : JetIndex s) (p : PolarPoint) : 1 ≤ physicalJetWeight T j p := by
  obtain ⟨_, hpos, _, _, _, _, _, hInv, _⟩ := hT
  exact one_le_pow₀ (hpos (T.radius p.1) (hInv p.1).1).2.2.2

theorem continuous_physicalJetWeight {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {s : ℕ} (j : JetIndex s) : Continuous (physicalJetWeight T j) := by
  obtain ⟨hsmooth, _, _, _, _, _, hrad, hInv, _⟩ := hT
  have hM : ContDiffOn ℝ ∞ T.M (Ioo D.a D.b) := hsmooth T.M (by simp)
  have hcoord : Continuous (fun p : PolarPoint => T.radius p.1) := hrad.continuous.comp continuous_fst
  exact (hM.continuousOn.comp_continuous hcoord (fun p => (hInv p.1).1)).pow _

private theorem physicalJetWeight_ne_zero {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {s : ℕ} (j : JetIndex s) (p : PolarPoint) : physicalJetWeight T j p ≠ 0 :=
  (zero_lt_one.trans_le (physicalJetWeight_one_le hT j p)).ne'

private theorem physicalJetWeight_inv_abs_le_one {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s : ℕ} (j : JetIndex s) (p : PolarPoint) :
    |(physicalJetWeight T j p)⁻¹| ≤ 1 := by
  have hW := physicalJetWeight_one_le hT j p
  rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hW))]
  exact inv_le_one_of_one_le₀ hW

/-- Recover the unweighted derivative by bounded reciprocal multiplication in the actual L² space. -/
def physicalJetNormalizedDerivative {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {s : ℕ} (j : JetIndex s) : PhysicalJetHilbert s →L[ℝ] CylinderL2 :=
  (cylinderBoundedMultiplier (fun p => (physicalJetWeight T j p)⁻¹)
      ((continuous_physicalJetWeight hT j).inv₀ (physicalJetWeight_ne_zero hT j)) 1
      (physicalJetWeight_inv_abs_le_one hT j)).comp (physicalJetCoordinate s j)

theorem physicalJetNormalizedDerivative_ae {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s : ℕ} (j : JetIndex s) (z : PhysicalJetHilbert s) :
    (physicalJetNormalizedDerivative hT j z : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (fun p => (physicalJetWeight T j p)⁻¹ * z j p) :=
  cylinderBoundedMultiplier_ae (fun p => (physicalJetWeight T j p)⁻¹)
    ((continuous_physicalJetWeight hT j).inv₀ (physicalJetWeight_ne_zero hT j)) 1
    (physicalJetWeight_inv_abs_le_one hT j) (z j)

theorem mem_physicalJetGraph_iff_normalized {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s : ℕ} (z : PhysicalJetHilbert s) :
    z ∈ physicalJetGraph T s ↔
      cylinderReflectionL2 (z (zeroJetIndex s)) = z (zeroJetIndex s) ∧ ∀ j : JetIndex s,
        HasWeakMixedDerivative (z (zeroJetIndex s)) (physicalJetNormalizedDerivative hT j z)
          (j.val 0).val (j.val 1).val := by
  change ((fun p : PolarPoint => z (zeroJetIndex s) (p.1, Real.pi - p.2))
    =ᵐ[materialCylinderMeasure] (z (zeroJetIndex s) : PolarPoint → ℝ)) ∧
    (∀ j : JetIndex s, ∃ d : CylinderL2,
      HasWeakMixedDerivative (z (zeroJetIndex s)) d (j.val 0).val (j.val 1).val ∧
      (z j : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
        (fun p => physicalJetWeight T j p * d p)) ↔ _
  rw [← cylinderReflectionL2_fixed_iff]
  constructor
  · rintro ⟨href, hweak⟩
    refine ⟨href, fun j => ?_⟩
    obtain ⟨d, hd, hw⟩ := hweak j
    have he : physicalJetNormalizedDerivative hT j z = d := by
      apply Lp.ext
      filter_upwards [physicalJetNormalizedDerivative_ae hT j z, hw] with p hp hwp
      change z j p = physicalJetWeight T j p * d p at hwp
      rw [hp, hwp, ← mul_assoc, inv_mul_cancel₀ (physicalJetWeight_ne_zero hT j p), one_mul]
    rw [he]
    exact hd
  · rintro ⟨href, hweak⟩
    refine ⟨href, fun j => ⟨physicalJetNormalizedDerivative hT j z, hweak j, ?_⟩⟩
    filter_upwards [physicalJetNormalizedDerivative_ae hT j z] with p hp
    change z j p = physicalJetWeight T j p * physicalJetNormalizedDerivative hT j z p
    rw [hp, ← mul_assoc, mul_inv_cancel₀ (physicalJetWeight_ne_zero hT j p), one_mul]

private def physicalJetReflectionResidual (s : ℕ) : PhysicalJetHilbert s →L[ℝ] CylinderL2 :=
  (cylinderReflectionL2.toContinuousLinearMap - ContinuousLinearMap.id ℝ CylinderL2).comp
    (physicalJetCoordinate s (zeroJetIndex s))

private theorem physicalJetReflectionResidual_apply (s : ℕ) (z : PhysicalJetHilbert s) :
    physicalJetReflectionResidual s z = cylinderReflectionL2 (z (zeroJetIndex s)) - z (zeroJetIndex s) := rfl

private def physicalJetWeakPair {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {s : ℕ} (j : JetIndex s) : PhysicalJetHilbert s →L[ℝ] (CylinderL2 × CylinderL2) :=
  (physicalJetCoordinate s (zeroJetIndex s)).prod (physicalJetNormalizedDerivative hT j)

private theorem physicalJetWeakPair_apply {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {s : ℕ} (j : JetIndex s) (z : PhysicalJetHilbert s) :
    physicalJetWeakPair hT j z = (z (zeroJetIndex s), physicalJetNormalizedDerivative hT j z) := rfl

/-- The actual Hilbert subspace associated with the weighted physical jet graph. -/
def physicalJetClosedSubmodule {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (s : ℕ) : Submodule ℝ (PhysicalJetHilbert s) :=
  (physicalJetReflectionResidual s).toLinearMap.ker ⊓
    (⨅ j : JetIndex s, (weakMixedDerivativeGraph (j.val 0).val (j.val 1).val).comap
      (physicalJetWeakPair hT j).toLinearMap)

theorem physicalJetClosedSubmodule_carrier {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (s : ℕ) :
    (physicalJetClosedSubmodule hT s : Set (PhysicalJetHilbert s)) = physicalJetGraph T s := by
  ext z
  rw [mem_physicalJetGraph_iff_normalized hT z]
  simp only [SetLike.mem_coe, physicalJetClosedSubmodule, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    physicalJetReflectionResidual_apply, physicalJetWeakPair_apply, sub_eq_zero,
    mem_weakMixedDerivativeGraph]

theorem isClosed_physicalJetClosedSubmodule {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (s : ℕ) : IsClosed (physicalJetClosedSubmodule hT s : Set (PhysicalJetHilbert s)) := by
  rw [physicalJetClosedSubmodule, Submodule.coe_inf, Submodule.coe_iInf]
  refine (physicalJetReflectionResidual s).isClosed_ker.inter (isClosed_iInter (fun j => ?_))
  exact (isClosed_weakMixedDerivativeGraph (j.val 0).val (j.val 1).val).preimage
    (physicalJetWeakPair hT j).continuous

instance physicalJetClosedSubmodule_completeSpace {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (s : ℕ) : CompleteSpace (physicalJetClosedSubmodule hT s) :=
  (isClosed_physicalJetClosedSubmodule hT s).isComplete.completeSpace_coe

theorem isClosed_physicalJetGraph {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (s : ℕ) : IsClosed (physicalJetGraph T s) := by
  rw [← physicalJetClosedSubmodule_carrier hT s]
  exact isClosed_physicalJetClosedSubmodule hT s

end ContinuousFlexibility.Statements
