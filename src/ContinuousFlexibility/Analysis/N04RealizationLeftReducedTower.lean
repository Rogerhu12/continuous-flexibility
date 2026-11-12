import ContinuousFlexibility.Analysis.N04RealizationNuResidualTower
import ContinuousFlexibility.Analysis.N04RealizationLeftColumnIdentities
import ContinuousFlexibility.Scalar.WeightedGeometry

/-!
# A uniform tower for the reduced left-height column

The supplied residual tower is restricted once to the actual scalar
geometry neighborhood. Its fixed left-height derivative has the same
uniform base and loss. The decoder is identified by a genuine derivative
of the same scalar residual, with the angular correction exactly zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The existing reduced parameter respects every common-height
direction, including the fixed left-height direction. -/
theorem n04Realization_nuParameter_heightDirection
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) (u : ScalarCommonHeight S)
    (x : N07aNuParameter S) (t : ℝ) :
    n07aNuParameterState hT hS hb (x + t • ((u, 0), 0)) =
      n07aNuParameterState hT hS hb x + t • scalarHeightDirection S u := by
  rcases x with ⟨⟨⟨v, l⟩, ν⟩, q⟩
  rcases u with ⟨a, c⟩
  simp only [n07aNuParameterState, scalarHeightDirection, Prod.mk_add_mk,
    Prod.smul_mk, smul_zero, add_zero]

/-- One geometric neighborhood precedes every derivative order. The
returned function is the actual reduced left column at all interior
physical points; its scalar geometry is retained for the actual-state
comparison. -/
theorem n04Realization_exists_uniformLeftReducedColumn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (v₀ : ScalarHeightSpace S) :
    ∃ U : Set (N07aNuParameter S), IsOpen U ∧ n07aNuParameterCenter S v₀ ∈ U ∧
      ∃ base loss : ℕ, ∃ N : N07aNuParameter S → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aNuParameterGrading S)
          (scalarHeightGrading S) U base loss N ∧
        (∀ x ∈ U, ScalarStateGeometry D S (n07aNuParameterState hT hS hb x)) ∧
        (∀ x ∈ U, ∀ p ∈ annularOpen D,
          (S.height scalarBeta).decode (N x) p =
            scalarStateOperator D S (n07aNuParameterState hT hS hb x) (0, 1) p) := by
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).continuousSMul
  obtain ⟨U, hU, hcenter, base, loss, f, hf, hdecode⟩ :=
    n04Realization_exists_uniformNuReducedResidual hD hT hS hb v₀
  obtain ⟨δ, hδ, _, hgeometry⟩ := exists_scalarStateBall_geometry hD hT hS v₀
  have hpre : n07aNuParameterState hT hS hb ⁻¹' scalarStateBall S v₀ 4 δ ∈
      𝓝 (n07aNuParameterCenter S v₀) := by
    apply (n07aNuParameterState_uniformTameGerm hT hS hb v₀).continuousAt.preimage_mem_nhds
    rw [n07aNuParameterState_center]
    exact (isOpen_scalarStateBall S v₀ 4 δ).mem_nhds
      (scalarStateCenter_mem_ball S v₀ 4 hδ)
  obtain ⟨W, hWsub, hWopen, hWcenter⟩ := mem_nhds_iff.mp hpre
  let V : Set (N07aNuParameter S) := U ∩ W
  have hV : IsOpen V := hU.inter hWopen
  have hfV : FixedNeighborhoodSmoothTame (n07aNuParameterGrading S)
      (scalarHeightGrading S) V base loss f :=
    hf.restrict hV (fun _ hx => hx.1)
  have hg : ∀ x ∈ V, ScalarStateGeometry D S (n07aNuParameterState hT hS hb x) :=
    fun x hx => hgeometry _ (hWsub hx.2)
  let J : SmoothDirections V f := hfV.2.choose
  have hJ : UniformScalarTowerEstimate (n07aNuParameterGrading S)
      (scalarHeightGrading S) V base loss f J := hfV.2.choose_spec
  let w : N07aNuParameter S := (((0, 1), 0), 0)
  let d : N07aNuParameter S → ScalarHeightSpace S :=
    fun x => J.D 1 x (Fin.snoc Fin.elim0 w)
  refine ⟨V, hV, ⟨hcenter, hWcenter⟩, base, loss, d,
    n04Realization_fixedNeighborhood_fixedDirection J hJ w, hg, ?_⟩
  intro x hx p hp
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
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • w ∈ V :=
    (hline.tendsto 0).eventually (hV.mem_nhds (by simpa using hx))
  have hd' : HasDerivAt
      (fun t : ℝ => scalarStateResidual D S
        (n07aNuParameterState hT hS hb x + t • scalarHeightDirection S (0, 1)) p)
      ((S.height scalarBeta).decode (d x) p) 0 := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [hevent] with t ht
    rw [J.zero (x + t • w) ht, hdecode _ ht.1,
      show n07aNuParameterState hT hS hb (x + t • w) =
        n07aNuParameterState hT hS hb x + t • scalarHeightDirection S (0, 1) from
          n04Realization_nuParameter_heightDirection hT hS hb (0, 1) x t]
  exact hd'.unique (n04Realization_scalarLeft_hasDerivAt hD hT hS (hg x hx) hp)

end ContinuousFlexibility.Analysis
