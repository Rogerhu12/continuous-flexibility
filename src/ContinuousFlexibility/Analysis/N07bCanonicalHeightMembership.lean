import ContinuousFlexibility.Analysis.N07bCanonicalHeightEnergy
import ContinuousFlexibility.Analysis.N07bCanonicalSourceIntegrability
import ContinuousFlexibility.Analysis.N07bCanonicalSourceSymmetry
import ContinuousFlexibility.Analysis.N07bVolumeUnknownSequence

/-!
# Actual canonical height classes and their zeroth-order volume lift

Local L² membership on each dynamic domain and reflection follow from
the actual chart formulas and a continuous even periodic physical height. The lift then uses the
prescribed volume model and the exact physical square-energy series. The
series remains an explicit analytic input, to be proved from geometric
bounds; this module does not assert fixed-domain membership.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hK hz hs

/-- Each actual height coordinate is locally L² on its canonical piece. -/
theorem n07b_canonicalHeight_memLp (m : ℕ) {u : PolarPoint → ℝ}
    (hu : ContinuousOn u (physicalPieceClosed S K z m)) :
    MemLp (canonicalHeight S K z m u) 2 (canonicalMeasure S K m) := by
  let f : PolarPoint → ℝ := fun p =>
    |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p
  have hf : ContinuousOn f
      (physicalPieceClosed S K z m) := by
    intro p hp
    have hc := (hK.boundary z hz hs m).2.2.2.2.1 p hp
    exact (((contDiffAt_planeJacobian hc.1).continuousAt.abs.continuousWithinAt).div
      ((hc.2.1.continuousAt.continuousWithinAt).pow 2)
      (pow_ne_zero 2 hc.2.2.2.ne')).mul (hu p hp)
  have hsrc := n07b_canonicalSource_memLp hK hz hs m hf
  have heq : canonicalSource S K z m f =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m u := by
    have hm : ∀ᵐ p ∂canonicalMeasure S K m,
        p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hm] with p hp
    exact n07b_canonicalSource_inverseDensity_mul hK hz hs m u
      ⟨hp.1, mem_univ _⟩
  exact (memLp_congr_ae heq).mp hsrc

theorem n07b_canonicalHeight_add (u : PolarPoint → ℝ)
    (hu : Function.Periodic u (0, Real.pi)) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m u (p + (0, Real.pi)) = canonicalHeight S K z m u p := by
  have hc := hK.charts z hz hs m
  have hx := hc.2.1 hp
  have hh := (hc.2.2.2.2.2.2.2 (K.inverseChart z m p) hx).2.2.2
  simp only [canonicalHeight]
  rw [n07b_canonicalInverse_add hK hz hs m hp, hu, hh]

theorem n07b_canonicalHeight_neg (u : PolarPoint → ℝ)
    (hu : ∀ r θ, u (r, -θ) = u (r, θ)) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m u (p.1, -p.2) = canonicalHeight S K z m u p := by
  have hc := hK.charts z hz hs m
  have hx := hc.2.1 hp
  have hh := hK.reflection z hz hs m (K.inverseChart z m p) hx
  have hi := hK.inverseReflection z hz hs m p hp
  simp only [canonicalHeight]
  rw [hi, hh.2.1, hu]

/-- Reflection is obtained for the actual height formula, without imposing
symmetry on the totalized inverse outside its canonical interval. -/
theorem n07b_canonicalHeight_reflection_ae (u : PolarPoint → ℝ)
    (heven : ∀ r θ, u (r, -θ) = u (r, θ))
    (hperiod : Function.Periodic u (0, Real.pi)) (m : ℕ) :
    (fun p : PolarPoint => canonicalHeight S K z m u (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] canonicalHeight S K z m u := by
  have hm : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hm] with p hp
  have hneg : (p.1, -p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  calc
    _ = canonicalHeight S K z m u ((p.1, -p.2) + (0, Real.pi)) := by
      congr 1
      ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
    _ = canonicalHeight S K z m u (p.1, -p.2) :=
      n07b_canonicalHeight_add hK hz hs u hperiod m hneg
    _ = _ := n07b_canonicalHeight_neg hK hz hs u heven m ⟨hp.1, mem_univ _⟩

/-- The height lift's weighted energy, written entirely in physical
coordinates. -/
def n07bPhysicalHeightEnergy {T : MaterialData} (γ t : ℝ)
    (z : AnnularState S × ℝ) (u : PolarPoint → ℝ) (m : ℕ) : ℝ :=
  (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
    ∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
      |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p ^ 2

/-- Exact identification of the zeroth-jet Hilbert energy. -/
theorem n07b_canonicalHeight_jetEnergy {T : MaterialData} (γ t : ℝ)
    (u : PolarPoint → ℝ) (hu : Continuous u) (m : ℕ) :
    n07bCanonicalJetEnergy (T := T) (K := K) (s := 0)
      (g := fun m (_ : Fin 1) => canonicalHeight S K z m u)
      (fun m _ => n07b_canonicalHeight_memLp hK hz hs m hu.continuousOn) γ t m =
        n07bPhysicalHeightEnergy (T := T) (K := K) γ t z u m := by
  change (∑ _j : Fin 1,
    ‖(n07bCanonicalSourceFactor T K γ t m)⁻¹ •
      (n07b_canonicalHeight_memLp hK hz hs m hu.continuousOn).toLp
        (canonicalHeight S K z m u)‖ ^ 2) = _
  rw [Fin.sum_univ_one, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    n07b_canonicalHeight_toLp_norm_sq hK hz hs m u
      (n07b_canonicalHeight_memLp hK hz hs m hu.continuousOn)]
  rfl

/-- A genuine physical energy series supplies the prescribed zeroth-order
volume element and its actual a.e. height representation. -/
theorem n07b_exists_canonicalHeightLevel
    {T : MaterialData} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (u : PolarPoint → ℝ) (hu : Continuous u)
    (heven : ∀ r θ, u (r, -θ) = u (r, θ))
    (hperiod : Function.Periodic u (0, Real.pi))
    (hsum : Summable (n07bPhysicalHeightEnergy (T := T) (K := K) γ t z u)) :
    ∃ W : V.level γ t 0, ∀ m,
      (V.forget γ t 0 W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K z m u := by
  let g : ∀ m : ℕ, Fin 1 → PolarPoint → ℝ :=
    fun m _ => canonicalHeight S K z m u
  have hg : ∀ m j, MemLp (g m j) 2 (canonicalMeasure S K m) :=
    fun m _ => n07b_canonicalHeight_memLp hK hz hs m hu.continuousOn
  have href : ∀ m, (fun p : PolarPoint => g m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m 0 :=
    n07b_canonicalHeight_reflection_ae hK hz hs u heven hperiod
  have hweak : ∀ m (j : Fin 1) φ, CanonicalTest S K m φ →
      (∫ p, g m j p * φ p ∂canonicalMeasure S K m) =
        (-1 : ℝ) ^ j.val * ∫ p, g m 0 p * mixedDerivative 0 j.val φ p
          ∂canonicalMeasure S K m := by
    intro m j φ _
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simp only [Fin.val_zero, pow_zero, one_mul, mixedDerivative, iteratedDeriv_zero, g]
  have henergy : Summable (n07bCanonicalJetEnergy (T := T) (K := K)
      (s := 0) (g := g) hg γ t) := by
    have he : n07bCanonicalJetEnergy (T := T) (K := K) (s := 0) (g := g) hg γ t =
        n07bPhysicalHeightEnergy (T := T) (K := K) γ t z u :=
      funext fun m => n07b_canonicalHeight_jetEnergy hK hz hs γ t u hu m
    rw [he]
    exact hsum
  refine ⟨n07bCanonicalSourceLift (s := 0) (g := g) hg hV href hweak henergy, fun m => ?_⟩
  apply n07bCanonicalSourceLift_forget_ae (s := 0) (g := g) hg hV href hweak henergy
  intro k
  have hsample := spaces_trace_sample_mem hD hT (K.cell k)
  exact (mul_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hT.2.1 _ hsample).2.2.2) _)
    (Real.rpow_pos_of_pos (hT.2.1 _ hsample).2.1 _)).ne'

end ContinuousFlexibility.Analysis
