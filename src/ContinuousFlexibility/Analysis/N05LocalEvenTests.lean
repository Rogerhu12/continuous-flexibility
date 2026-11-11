import ContinuousFlexibility.Analysis.N05ReferenceTests
import ContinuousFlexibility.Analysis.CylinderTestPeriodization
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Local even periodic height tests away from reflection circles

A compact planar cutoff is periodized and added to its angular reflection.
A half-period chamber separates the cutoff from every nontrivial translate
and from every reflected translate.  Thus the resulting global even periodic
test agrees with the prescribed smooth germ, not merely with a chosen jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def n05EvenPeriodization (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  cylinderTestPeriodization f p + cylinderTestPeriodization f (p.1, -p.2)

theorem n05EvenPeriodization_even (f : PolarPoint → ℝ) (r θ : ℝ) :
    n05EvenPeriodization f (r, -θ) = n05EvenPeriodization f (r, θ) := by
  simp only [n05EvenPeriodization, neg_neg]
  ring

theorem n05EvenPeriodization_periodic (f : PolarPoint → ℝ) :
    Function.Periodic (n05EvenPeriodization f) (0, Real.pi) := by
  intro p
  have hp := cylinderTestPeriodization_periodic f
  have hminus : cylinderTestPeriodization f (p.1, -p.2 - Real.pi) =
      cylinderTestPeriodization f (p.1, -p.2) := by
    simpa only [Prod.mk_sub_mk, sub_zero] using hp.sub_eq (p.1, -p.2)
  have href : cylinderTestPeriodization f (p.1, -(p.2 + Real.pi)) =
      cylinderTestPeriodization f (p.1, -p.2) := by
    simpa only [neg_add, sub_eq_add_neg] using hminus
  simp only [n05EvenPeriodization, Prod.fst_add, Prod.snd_add, add_zero, hp p, href]

theorem n05EvenPeriodization_contDiff {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (n05EvenPeriodization f) := by
  have h := (isCylinderTest_cylinderTestPeriodization hf hc).1
  exact h.add (h.comp (contDiff_fst.prodMk contDiff_snd.neg))

/-- A chamber between successive reflection circles has no overlap with
its nontrivial periodic translates or any of its reflected translates. -/
theorem n05EvenPeriodization_eq_of_chamber
    {f : PolarPoint → ℝ} (n : ℤ)
    (hs : ∀ q : PolarPoint, f q ≠ 0 →
      q.2 ∈ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2)))
    (p : PolarPoint)
    (hp : p.2 ∈ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2))) :
    n05EvenPeriodization f p = f p := by
  have hz (k : ℤ) (hk : k ≠ 0) : f (cylinderAngularShift k p) = 0 := by
    by_contra hn
    have hθ := hs _ hn
    change (n : ℝ) * (Real.pi / 2) < p.2 + k • Real.pi ∧
      p.2 + k • Real.pi < ((n : ℝ) + 1) * (Real.pi / 2) at hθ
    simp only [zsmul_eq_mul] at hθ
    have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hk' with hneg | hpos
    · have hneg' : (k : ℝ) ≤ -1 := by exact_mod_cast hneg
      have hm := mul_le_mul_of_nonneg_right hneg' Real.pi_pos.le
      linarith only [hθ.1, hp.2, hm, Real.pi_pos]
    · have hpos' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
      have hm := mul_le_mul_of_nonneg_right hpos' Real.pi_pos.le
      linarith only [hθ.2, hp.1, hm, Real.pi_pos]
  have hperiod : cylinderTestPeriodization f p = f p := by
    calc
      _ = f (cylinderAngularShift 0 p) := tsum_eq_single 0 hz
      _ = _ := by
        change f (p.1, p.2 + (0 : ℤ) • Real.pi) = f p
        simp only [zero_zsmul, add_zero, Prod.mk.eta]
  have href (k : ℤ) : f (cylinderAngularShift k (p.1, -p.2)) = 0 := by
    by_contra hn
    have hθ := hs _ hn
    change (n : ℝ) * (Real.pi / 2) < -p.2 + k • Real.pi ∧
      -p.2 + k • Real.pi < ((n : ℝ) + 1) * (Real.pi / 2) at hθ
    simp only [zsmul_eq_mul] at hθ
    have hlo : (n : ℝ) * Real.pi < (k : ℝ) * Real.pi := by
      linarith only [hθ.1, hp.1]
    have hhi : (k : ℝ) * Real.pi < ((n : ℝ) + 1) * Real.pi := by
      linarith only [hθ.2, hp.2]
    have hlo' : (n : ℝ) < (k : ℝ) := lt_of_mul_lt_mul_right hlo Real.pi_pos.le
    have hhi' : (k : ℝ) < (n : ℝ) + 1 := lt_of_mul_lt_mul_right hhi Real.pi_pos.le
    have hnk : n < k := by exact_mod_cast hlo'
    have hkn : k < n + 1 := by exact_mod_cast hhi'
    omega
  have hreflection : cylinderTestPeriodization f (p.1, -p.2) = 0 := by
    unfold cylinderTestPeriodization
    simp only [href, tsum_zero]
  simp only [n05EvenPeriodization, hperiod, hreflection, add_zero]

/-- The only excluded angles are the fixed circles of angular reflection
on the circle of period pi. -/
theorem n05_exists_angular_chamber {θ : ℝ}
    (hθ : θ ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    ∃ n : ℤ, θ ∈ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2)) := by
  let n : ℤ := ⌊θ / (Real.pi / 2)⌋
  have hπ : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hlo : (n : ℝ) * (Real.pi / 2) ≤ θ :=
    (le_div_iff₀ hπ).mp (Int.floor_le _)
  have hne : (n : ℝ) * (Real.pi / 2) ≠ θ := fun he => hθ ⟨n, he⟩
  refine ⟨n, lt_of_le_of_ne hlo hne, ?_⟩
  exact (div_lt_iff₀ hπ).mp (Int.lt_floor_add_one _)

/-- An arbitrary smooth germ in a non-reflection chamber has a genuine
global even periodic compact-radial extension agreeing on a neighborhood. -/
theorem n05_exists_even_compact_germ
    {D : ReferenceData} {f : PolarPoint → ℝ} {U : Set PolarPoint} {p : PolarPoint}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hpU : p ∈ U)
    (hp : p ∈ annularOpen D)
    (hθ : p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    ∃ g : PolarPoint → ℝ,
      ContDiff ℝ ∞ g ∧ (∀ r θ, g (r, -θ) = g (r, θ)) ∧
      Function.Periodic g (0, Real.pi) ∧ HasCompactRadialSupport D g ∧
      g =ᶠ[𝓝 p] f := by
  obtain ⟨n, hn⟩ := n05_exists_angular_chamber hθ
  let V : Set PolarPoint := U ∩
    (Ioo D.a D.b ×ˢ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2)))
  have hV : IsOpen V := hU.inter (isOpen_Ioo.prod isOpen_Ioo)
  have hpV : p ∈ V := ⟨hpU, hp.1, hn⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let χ : ContDiffBump p := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hχsupport : tsupport (χ : PolarPoint → ℝ) ⊆ V := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  let ψ : PolarPoint → ℝ := fun q => χ q * f q
  have hψ : ContDiff ℝ ∞ ψ := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q ∈ tsupport (χ : PolarPoint → ℝ)
    · exact χ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hχsupport hq).1))
    · have hz : (χ : PolarPoint → ℝ) =ᶠ[𝓝 q] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hq
      have hψzero : ψ =ᶠ[𝓝 q] 0 := by
        filter_upwards [hz] with y hy
        change χ y = 0 at hy
        simp only [ψ, hy, zero_mul, Pi.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq hψzero
  have hψcompact : HasCompactSupport ψ := χ.hasCompactSupport.mul_right
  have hψangle (q : PolarPoint) (hq : ψ q ≠ 0) :
      q.2 ∈ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2)) := by
    have hχq : χ q ≠ 0 := fun hzero => hq (by simp only [ψ, hzero, zero_mul])
    exact (hχsupport (subset_tsupport χ hχq)).2.2
  let K : Set ℝ := Prod.fst '' tsupport (χ : PolarPoint → ℝ)
  have hK : IsCompact K := χ.hasCompactSupport.image continuous_fst
  have hKD : K ⊆ Ioo D.a D.b := by
    rintro r ⟨q, hq, rfl⟩
    exact (hχsupport hq).2.1
  have hψzero (r : ℝ) (hr : r ∉ K) (θ : ℝ) : ψ (r, θ) = 0 := by
    have hχzero : χ (r, θ) = 0 := by
      by_contra hne
      exact hr ⟨(r, θ), subset_tsupport χ hne, rfl⟩
    simp only [ψ, hχzero, zero_mul]
  have hsupport : HasCompactRadialSupport D (n05EvenPeriodization ψ) := by
    refine ⟨K, hK, hKD, ?_⟩
    intro r hr θ
    have hP (φ : ℝ) : cylinderTestPeriodization ψ (r, φ) = 0 := by
      unfold cylinderTestPeriodization
      have hz (k : ℤ) : ψ (cylinderAngularShift k (r, φ)) = 0 :=
        hψzero r hr (φ + k • Real.pi)
      simp only [hz, tsum_zero]
    simp only [n05EvenPeriodization, hP, add_zero]
  refine ⟨n05EvenPeriodization ψ, n05EvenPeriodization_contDiff hψ hψcompact,
    n05EvenPeriodization_even ψ, n05EvenPeriodization_periodic ψ, hsupport, ?_⟩
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p,
      q.2 ∈ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2)) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hn
  filter_upwards [χ.eventuallyEq_one, hnear] with q hχq hq
  rw [n05EvenPeriodization_eq_of_chamber n hψangle q hq]
  change χ q = 1 at hχq
  simp only [ψ, hχq, one_mul]

/-- The local extension is an actual element of the prescribed height model. -/
theorem n05_exists_heightPair_local_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {f : PolarPoint → ℝ} {U : Set PolarPoint} {p : PolarPoint}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hpU : p ∈ U)
    (hp : p ∈ annularOpen D)
    (hθ : p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    ∃ η : HeightPair S, heightPairField S η =ᶠ[𝓝 p] f := by
  obtain ⟨g, hg, heven, hperiodic, hsupport, hgerm⟩ :=
    n05_exists_even_compact_germ hU hf hpU hp hθ
  obtain ⟨η, hη⟩ :=
    n05_exists_heightPair_of_compact_test hT hS hg heven hperiodic hsupport
  have hηg : heightPairField S η =ᶠ[𝓝 p] g :=
    Filter.Eventually.of_forall (congrFun hη)
  exact ⟨η, hηg.trans hgerm⟩

/-- Away from the reflection circles, the frozen reference identity acts on
every actual smooth germ, without any regularity assumption on L. -/
theorem n05_reference_correctionOperator_eq_local
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {f : PolarPoint → ℝ} {U : Set PolarPoint} {p : PolarPoint}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hpU : p ∈ U)
    (hp : p ∈ annularOpen D)
    (hθ : p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0)) f p =
      divergenceOperator (L.coefficients (C.referenceState, 0)) f p := by
  obtain ⟨η, hη⟩ := n05_exists_heightPair_local_germ hT hS hU hf hpU hp hθ
  exact n05_reference_correctionOperator_eq_germ h hp η hη

end ContinuousFlexibility.Statements

