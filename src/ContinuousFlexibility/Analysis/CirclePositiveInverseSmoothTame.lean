import ContinuousFlexibility.Analysis.CirclePositiveInverseModel
import ContinuousFlexibility.Analysis.CircleInverseSmoothTame
import ContinuousFlexibility.Analysis.SmoothDirectionsGluing

/-!
# Actual inverse composition is smooth tame on every positive lift

Each point has one positive derivative lower bound and a low-seminorm
neighborhood on which the same bound holds. The local inverse theorem
therefore applies. Its decoded operator is independent of the bound,
so the resulting genuine towers glue on the full open positive domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance circlePositiveInverseSmoothTamePairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

private theorem smoothTameOn_positiveFamily_of_local_bounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (p : ℕ → Seminorm ℝ E) (hm : Monotone p) (ht : WithSeminorms p)
    (U : Set E) (hU : IsOpen U)
    (slope localSlope : E → ℕ → ℝ → ℝ)
    (hslope : ∀ e m θ, slope e m θ = localSlope e m θ)
    (hmem : ∀ e, (∀ m θ, 0 < localSlope e m θ) → e ∈ U)
    (F : E → E →ₗ[ℝ] E) (Fa : (a : ℝ) → 0 < a → E → E →ₗ[ℝ] E)
    (hlocal : ∃ base : ℕ, 2 ≤ base ∧
      ∀ K : ℝ, 0 ≤ K → ∀ a : ℝ, ∀ ha : 0 < a,
      ∀ V : Set E, IsOpen V →
      (∀ e ∈ V, p base e ≤ K) →
      (∀ e ∈ V, ∀ m θ, a ≤ slope e m θ) →
      SmoothTameOn (pairGrading p p) p (V ×ˢ univ)
        (fun z : E × E => Fa a ha z.1 z.2))
    (hlower : ∀ e₀ ∈ U, ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ ∀ e : E,
      p 2 (e - e₀) < δ → ∀ m θ, a ≤ localSlope e m θ)
    (hagree : ∀ a (ha : 0 < a) e,
      (∀ m θ, a ≤ slope e m θ) → F e = Fa a ha e) :
    SmoothTameOn (pairGrading p p) p (U ×ˢ univ)
      (fun z : E × E => F z.1 z.2) := by
  obtain ⟨base, hbase, hlocal⟩ := hlocal
  apply smoothTameOn_of_local_neighborhoods (pairGrading p p) p
    (tamePairGrading_monotone hm hm) (hU.prod isOpen_univ)
  intro z₀ hz₀
  obtain ⟨a, δ, ha, hδ, hpositive⟩ := hlower z₀.1 hz₀.1
  let W : Set E := {e | p base (e - z₀.1) < δ}
  have hW : IsOpen W := isOpen_lt
    ((ht.continuous_seminorm base).comp (continuous_id.sub continuous_const)) continuous_const
  have hzW : z₀.1 ∈ W := by
    have hzero : p base (0 : E) = 0 := map_zero (p base)
    exact ((congrArg (fun y : E => p base y) (sub_self z₀.1)).trans hzero).trans_lt hδ
  have hlower' (e : E) (he : e ∈ W) (m : ℕ) (θ : ℝ) :
      a ≤ localSlope e m θ :=
    hpositive e ((hm hbase (e - z₀.1)).trans_lt he) m θ
  have hWsub : W ⊆ U :=
    fun e he => hmem e (fun m θ => ha.trans_le (hlower' e he m θ))
  let K : ℝ := p base z₀.1 + δ
  have hK : 0 ≤ K := add_nonneg (apply_nonneg _ _) hδ.le
  have hlow : ∀ e ∈ W, p base e ≤ K := by
    intro e he
    calc
      p base e = p base ((e - z₀.1) + z₀.1) := by rw [sub_add_cancel]
      _ ≤ p base (e - z₀.1) + p base z₀.1 := map_add_le_add (p base) _ _
      _ ≤ δ + p base z₀.1 := add_le_add he.le le_rfl
      _ = K := add_comm _ _
  have hpos : ∀ e ∈ W, ∀ m θ, a ≤ slope e m θ :=
    fun e he m θ => (hlower' e he m θ).trans_eq (hslope e m θ).symm
  have htame := hlocal K hK a ha W hW hlow hpos
  have hactual : SmoothTameOn (pairGrading p p) p (W ×ˢ univ)
      (fun z : E × E => F z.1 z.2) :=
    smoothTameOn_congr htame (fun z hz =>
      congrArg (fun L : E →ₗ[ℝ] E => L z.2) (hagree a ha z.1 (hpos z.1 hz.1)).symm)
  refine ⟨base, δ, W ×ˢ univ, hδ, hW.prod isOpen_univ,
    ⟨hzW, mem_univ _⟩, ?_, ?_, hactual⟩
  · exact fun z hz => ⟨hWsub hz.1, hz.2⟩
  · intro z hz hnear
    refine ⟨?_, mem_univ _⟩
    change p base (z.1 - z₀.1) < δ
    change p base (z.1 - z₀.1) + p base (z.2 - z₀.2) < δ at hnear
    exact (le_add_of_nonneg_right (apply_nonneg _ _)).trans_lt hnear

theorem smoothTameOn_circlePositiveInverseComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading
      (circlePositiveLiftDomain S ×ˢ univ)
      (fun z : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ travel z.1 z.2) := by
  exact smoothTameOn_positiveFamily_of_local_bounds (E := S.Space) S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond)
    (withSeminorms_graded (fun j => S.level j) S.bond)
    (circlePositiveLiftDomain S)
    (circlePositiveLiftDomain_isOpen
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ)
    (fun e m θ => deriv (circleAffineLift travel (S.decode e) 1 m) θ)
    (fun e m θ => 1 + deriv (S.decode e m) θ)
    (circleAffineLift_deriv (T := T) (γ := γ) (S := S) hS travel)
    (fun e he => he)
    (circlePositiveInverseComposeLinear hS hT hD hγ travel)
    (fun a ha => circleInverseComposeLinear hS hT hD hγ travel a ha)
    (smoothTameOn_circleInverseComposeLinear
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel 2)
    (fun e he => circlePositiveLiftDomain_local_lower
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ he)
    (fun a ha e hpos => circlePositiveInverseComposeLinear_eq_fixed
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel a ha e hpos)

end ContinuousFlexibility.Statements
