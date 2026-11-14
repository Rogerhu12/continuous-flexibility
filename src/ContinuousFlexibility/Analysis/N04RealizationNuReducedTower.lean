module

public import ContinuousFlexibility.Analysis.N04RealizationNuResidualTower

/-!
# A uniform tower for the actual distinguished physical column

The fixed border derivative of the retained residual tower is a height
field on its original open neighborhood. Decoding commutes with that
derivative, so this is the actual scalar column, with its uniform bounds
still attached before any source-kernel wrapper is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The fixed-direction construction retains one neighborhood and one
loss for all derivatives of the actual reduced distinguished column. -/
theorem n04Realization_exists_uniformNuReducedColumn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (v₀ : ScalarHeightSpace S) :
    ∃ U : Set (N07aNuParameter S), IsOpen U ∧ n07aNuParameterCenter S v₀ ∈ U ∧
      ∃ base loss : ℕ, ∃ N : N07aNuParameter S → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aNuParameterGrading S)
          (scalarHeightGrading S) U base loss N ∧
        (∀ x ∈ U, ∀ p, (S.height scalarBeta).decode (N x) p =
          deriv (fun ν => scalarStateResidual D S
            (n07aNuParameterState hT hS hb ((x.1.1, ν), x.2)) p) x.1.2) := by
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).continuousSMul
  obtain ⟨U, hU, hcenter, base, loss, f, hf, hdecode⟩ :=
    n04Realization_exists_uniformNuReducedResidual hD hT hS hb v₀
  let J : SmoothDirections U f := hf.2.choose
  have hJ : UniformScalarTowerEstimate (n07aNuParameterGrading S)
      (scalarHeightGrading S) U base loss f J := hf.2.choose_spec
  let w : N07aNuParameter S := n07aNuParameterDirection S
  let d : N07aNuParameter S → ScalarHeightSpace S :=
    fun x => J.D 1 x (Fin.snoc Fin.elim0 w)
  refine ⟨U, hU, hcenter, base, loss, d,
    n04Realization_fixedNeighborhood_fixedDirection J hJ w, ?_⟩
  intro x hx p
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
    exact (hline.tendsto 0).eventually (hU.mem_nhds (by simpa using hx))
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
