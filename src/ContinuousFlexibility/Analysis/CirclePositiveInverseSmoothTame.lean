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

theorem smoothTameOn_circlePositiveInverseComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading
      (circlePositiveLiftDomain S ×ˢ univ)
      (fun z : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ travel z.1 z.2) := by
  classical
  have hm : Monotone S.grading :=
    gradedSeminorm_monotone (fun j => S.level j) S.bond
  have hp : Monotone (pairGrading S.grading S.grading) :=
    tamePairGrading_monotone hm hm
  have hU : IsOpen (circlePositiveLiftDomain S ×ˢ (univ : Set S.Space)) :=
    (circlePositiveLiftDomain_isOpen hS hT hD hγ).prod isOpen_univ
  apply smoothTameOn_of_local_neighborhoods
    (pairGrading S.grading S.grading) S.grading hp hU
  intro z₀ hz₀
  obtain ⟨base, hbase, hlocal⟩ :=
    smoothTameOn_circleInverseComposeLinear hS hT hD hγ hinterp travel 2
  obtain ⟨a, δ, ha, hδ, hpositive⟩ :=
    circlePositiveLiftDomain_local_lower hS hT hD hγ hz₀.1
  let W : Set S.Space := {e | S.grading base (e - z₀.1) < δ}
  have hW : IsOpen W :=
    isOpen_lt
      (((withSeminorms_graded (fun j => S.level j) S.bond).continuous_seminorm base).comp
        (continuous_id.sub continuous_const)) continuous_const
  have hzW : z₀.1 ∈ W := by
    change S.grading base (z₀.1 - z₀.1) < δ
    simpa only [sub_self, (S.grading base).map_zero'] using hδ
  have hlower (e : S.Space) (he : e ∈ W) (m : ℕ) (θ : ℝ) :
      a ≤ 1 + deriv (S.decode e m) θ :=
    hpositive e ((hm hbase (e - z₀.1)).trans_lt he) m θ
  have hWsub : W ⊆ circlePositiveLiftDomain S :=
    fun e he m θ => ha.trans_le (hlower e he m θ)
  let K : ℝ := S.grading base z₀.1 + δ
  have hK : 0 ≤ K := add_nonneg (apply_nonneg _ _) hδ.le
  have hlow : ∀ e ∈ W, S.grading base e ≤ K := by
    intro e he
    have h := map_add_le_add (S.grading base) (e - z₀.1) z₀.1
    rw [sub_add_cancel] at h
    change S.grading base (e - z₀.1) < δ at he
    dsimp only [K]
    linarith only [h, he]
  have hpos : ∀ e ∈ W, ∀ m θ,
      a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ := by
    intro e he m θ
    rw [circleAffineLift_deriv hS]
    exact hlower e he m θ
  have htame := hlocal K hK a ha W hW hlow hpos
  have hactual : SmoothTameOn (pairGrading S.grading S.grading) S.grading (W ×ˢ univ)
      (fun z : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ travel z.1 z.2) := by
    apply smoothTameOn_congr htame
    intro z hz
    exact congrArg (fun L : S.Space →ₗ[ℝ] S.Space => L z.2)
      (circlePositiveInverseComposeLinear_eq_fixed hS hT hD hγ travel a ha z.1
        (hpos z.1 hz.1)).symm
  refine ⟨base, δ, W ×ˢ univ, hδ, hW.prod isOpen_univ,
    ⟨hzW, mem_univ _⟩, ?_, ?_, hactual⟩
  · intro z hz
    exact ⟨hWsub hz.1, hz.2⟩
  · intro z hz hnear
    refine ⟨?_, mem_univ _⟩
    change S.grading base (z.1 - z₀.1) < δ
    change S.grading base (z.1 - z₀.1) + S.grading base (z.2 - z₀.2) < δ at hnear
    exact (le_add_of_nonneg_right (apply_nonneg _ _)).trans_lt hnear

end ContinuousFlexibility.Statements
