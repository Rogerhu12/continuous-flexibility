import ContinuousFlexibility.Analysis.N07aNuParameterTame
import ContinuousFlexibility.Analysis.N07aFixedDirection
import ContinuousFlexibility.Analysis.SolveTameSubspace
import ContinuousFlexibility.Scalar.WeightedRealization
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The distinguished scalar column as an actual source-valued family

The existing scalar realization is evaluated on the literal compact border
profile. Its genuine directional tower supplies the fixed border derivative.
The same physical conservation functional annihilates this derivative, so
the codomain is the prescribed Source kernel without changing its decoder.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n07a_exists_nuReducedResidual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (v₀ : ScalarHeightSpace S) :
    ∃ U : Set (N07aNuParameter S), IsOpen U ∧ n07aNuParameterCenter S v₀ ∈ U ∧
      ∃ f : N07aNuParameter S → ScalarHeightSpace S,
        SmoothTameOn (n07aNuParameterGrading S) (scalarHeightGrading S) U f ∧
        (∀ x ∈ U, S.Q (f x) = 0) ∧
        (∀ x ∈ U, ∀ p, (S.height scalarBeta).decode (f x) p =
          scalarStateResidual D S (n07aNuParameterState hT hS hb x) p) := by
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).continuousSMul
  letI : LocallyConvexSpace ℝ (ScalarWeightedState S) :=
    (weighted_scalarStateGrading_withSeminorms S).toLocallyConvexSpace
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  let construction := scalarWeightedS05 D T S hD hT hS v₀
  let W : WeightedScalarData S := construction.choose
  have h03 : IsWeightedS03 D S v₀ W := construction.choose_spec.1
  have h04 : IsWeightedS04 D S v₀ W := construction.choose_spec.2.1
  let V := scalarStateBall S v₀ W.base W.epsilon
  let J : SmoothDirections V W.residual := h04.2.2.choose
  have hJ : UniformScalarTowerEstimate (scalarStateGrading S) (scalarHeightGrading S)
      V W.base W.loss W.residual J := h04.2.2.choose_spec.1
  have hQ : ∀ y ∈ V, S.Q (W.residual y) = 0 := by
    intro y hy
    rw [← J.zero y hy]
    exact (h04.2.2.choose_spec.2.1 0 y hy Fin.elim0).1
  have hI := n07aNuParameterState_uniformTameGerm hT hS hb v₀
  have hR : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S)
      (n07aNuParameterState hT hS hb (n07aNuParameterCenter S v₀)) W.residual := by
    rw [n07aNuParameterState_center]
    exact (fixedNeighborhoodSmoothTame_of_uniform J hJ).uniformTameGerm
      (weighted_scalarStateGrading_monotone S)
      (weighted_scalarStateGrading_withSeminorms S) h03.2.2.2.1
  have hcomp := hI.comp hR (n07aNuParameterGrading_monotone S)
    (n07aNuParameterGrading_withSeminorms S) (weighted_scalarStateGrading_monotone S)
  obtain ⟨b, l, δ, hδ, hf⟩ := hcomp
  let U₀ : Set (N07aNuParameter S) :=
    {x | n07aNuParameterGrading S b (x - n07aNuParameterCenter S v₀) < δ}
  have hU₀ : IsOpen U₀ := isOpen_uniformTameBall
    (n07aNuParameterGrading_withSeminorms S) b _ δ
  have hc₀ : n07aNuParameterCenter S v₀ ∈ U₀ := by
    have hz : n07aNuParameterGrading S b (0 : N07aNuParameter S) = 0 :=
      (n07aNuParameterGrading S b).map_zero'
    simpa only [U₀, Set.mem_ofPred_eq, sub_self, hz] using hδ
  have hIV : n07aNuParameterState hT hS hb ⁻¹' V ∈
      𝓝 (n07aNuParameterCenter S v₀) := by
    apply hI.continuousAt.preimage_mem_nhds
    rw [n07aNuParameterState_center]
    exact h03.2.2.1.mem_nhds h03.2.2.2.1
  obtain ⟨c, η, _, hη, _, hsub⟩ := exists_small_uniformTameBall
    (n07aNuParameterGrading_monotone S) (n07aNuParameterGrading_withSeminorms S)
    (inter_mem (hU₀.mem_nhds hc₀) hIV) b
  let U : Set (N07aNuParameter S) :=
    {x | n07aNuParameterGrading S c (x - n07aNuParameterCenter S v₀) < η}
  have hU : IsOpen U := isOpen_uniformTameBall
    (n07aNuParameterGrading_withSeminorms S) c _ η
  refine ⟨U, hU, ?_, W.residual ∘ n07aNuParameterState hT hS hb,
    (hf.restrict hU (fun x hx => (hsub hx).1)).1, ?_, ?_⟩
  · have hz : n07aNuParameterGrading S c (0 : N07aNuParameter S) = 0 :=
      (n07aNuParameterGrading S c).map_zero'
    simpa only [U, Set.mem_ofPred_eq, sub_self, hz] using hη
  · intro x hx
    exact hQ _ (hsub hx).2
  · intro x hx p
    exact h04.1 _ (hsub hx).2 p

def n07aNuParameterDirection (S : PhysicalSpacesData) : N07aNuParameter S :=
  (((0, 0), 1), 0)

theorem n07aNuParameter_add_direction (S : PhysicalSpacesData)
    (x : N07aNuParameter S) (t : ℝ) :
    x + t • n07aNuParameterDirection S = ((x.1.1, x.1.2 + t), x.2) := by
  rcases x with ⟨⟨⟨v, l⟩, ν⟩, q⟩
  simp only [n07aNuParameterDirection, Prod.smul_mk, smul_zero,
    smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero]

theorem n07a_exists_nuReducedSource
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (v₀ : ScalarHeightSpace S) :
    ∃ U : Set (N07aNuParameter S), IsOpen U ∧ n07aNuParameterCenter S v₀ ∈ U ∧
      ∃ N : N07aNuParameter S → S.Source,
        SmoothTameOn (n07aNuParameterGrading S) S.sourceGrading U N ∧
        (∀ x ∈ U, ∀ p, (S.height (3 / 4 : ℝ)).decode (N x).val p =
          deriv (fun ν => scalarStateResidual D S
            (n07aNuParameterState hT hS hb ((x.1.1, ν), x.2)) p) x.1.2) := by
  classical
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).continuousSMul
  obtain ⟨U, hU, hcenter, f, hf, hQ, hdecode⟩ :=
    n07a_exists_nuReducedResidual hD hT hS hb v₀
  let J : SmoothDirections U f := hf.choose
  let w : N07aNuParameter S := n07aNuParameterDirection S
  let d : N07aNuParameter S → ScalarHeightSpace S :=
    fun x => J.D 1 x (Fin.snoc Fin.elim0 w)
  have hdQ (x : N07aNuParameter S) (hx : x ∈ U) : S.Q (d x) = 0 :=
    J.linear_conservation S.Q hQ 1 x hx _
  let N : N07aNuParameter S → S.Source := fun x =>
    if hx : x ∈ U then ⟨d x, hdQ x hx⟩ else 0
  have hN (x : N07aNuParameter S) (hx : x ∈ U) : (N x).val = d x := by
    simp only [N, dif_pos hx]
  refine ⟨U, hU, hcenter, N,
    solve_smoothTameOn_codRestrict S.Q.toLinearMap.ker S.Q.isClosed_ker
      (n07a_smoothTame_fixedDirection hf w) N hN, ?_⟩
  intro x hx p
  apply (congrArg (fun v : ScalarHeightSpace S => (S.height scalarBeta).decode v p)
    (hN x hx)).trans
  have hd := scalarHeightTower_decode_derivative hS J 0 x hx Fin.elim0 w p
  have hv : (Fin.cons w Fin.elim0 : Fin 1 → N07aNuParameter S) =
      Fin.snoc (α := fun _ : Fin 1 => N07aNuParameter S) Fin.elim0 w := by
    funext i
    have hi : i = 0 := by
      apply Fin.ext
      omega
    subst i
    simp only [Fin.cons_zero, Fin.snoc_zero]
  rw [hv] at hd
  have hline : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • w ∈ U := by
    have he := (hline.tendsto 0).eventually (hU.mem_nhds (by simpa using hx))
    exact he
  have hd' : HasDerivAt
      (fun t : ℝ => scalarStateResidual D S
        (n07aNuParameterState hT hS hb ((x.1.1, t + x.1.2), x.2)) p)
      ((S.height scalarBeta).decode (d x) p) 0 := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [hevent] with t ht
    rw [J.zero (x + t • w) ht, hdecode _ ht,
      show x + t • w = ((x.1.1, t + x.1.2), x.2) by
        rw [show w = n07aNuParameterDirection S from rfl,
          n07aNuParameter_add_direction, add_comm x.1.2 t]]
  let Rν : ℝ → ℝ := fun ν => scalarStateResidual D S
    (n07aNuParameterState hT hS hb ((x.1.1, ν), x.2)) p
  have hshift : deriv (fun t : ℝ => Rν (t + x.1.2)) 0 = deriv Rν x.1.2 := by
    simpa only [zero_add] using deriv_comp_add_const Rν x.1.2 (0 : ℝ)
  exact hd'.deriv.symm.trans hshift

end ContinuousFlexibility.Analysis
