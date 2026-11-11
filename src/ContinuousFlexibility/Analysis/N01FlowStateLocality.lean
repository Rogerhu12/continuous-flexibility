import ContinuousFlexibility.Analysis.N01FlowConstantDirections
import ContinuousFlexibility.Analysis.N01SingletonControl

/-!
# The exact physical directions seen by one characteristic component

On a negative component the border control vanishes and every other
component control vanishes. The actual profile sees only its own kappa
value. Together with height locality modulo constants this removes the
border, chart and trace directions from the actual flow tower.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01FlowStateLocalityStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

theorem controlGeometryConditions.control_zero_other
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) {m n : ℕ} (hmn : n ≠ m)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) : C.control n r = 0 := by
  by_contra hn
  have hnr : r ∈ Ioo (C.left n) (C.right n) := hC.support_subset n hn
  exact Set.disjoint_left.mp (hC.2.2.1 n m hmn) hnr hr

theorem N01Properties.border_zero_on_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) : D.chi r = 0 := by
  by_contra hχ
  have hpositive : 0 < deriv D.w r := (hN.1.2.2.2.1.support_subset hχ).2
  have hnegative := hN.2.2.2.1.2.2.2.1 m r hr
  exact (not_lt_of_ge hpositive.le) hnegative

theorem N01Properties.stateProfile_on_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x r = D.w r * Real.exp (stateKappa S x m * C.control m r) := by
  have hsum : (∑' n, stateKappa S x n * C.control n r) =
      stateKappa S x m * C.control m r := by
    apply tsum_eq_single m
    intro n hn
    rw [hN.2.2.2.1.control_zero_other hn hr, mul_zero]
  simp only [stateProfile, hN.border_zero_on_component m hr, mul_zero, zero_add, hsum]

private theorem angularMean_eq_of_constant (f : ℝ → ℝ)
    (hf : ∀ θ, f θ = f 0) : angularMean f = f 0 := by
  have heq : f = fun _ : ℝ => f 0 := funext hf
  rw [heq, angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem stateKappa_eq_decode_zero
    {S : PhysicalSpacesData} {x : AnnularState S} (hx : stateSector S x) (m : ℕ) :
    stateKappa S x m = (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m 0 :=
  angularMean_eq_of_constant _ (fun θ => hx.1 m θ 0)

theorem liftSectorParameter_direction_height
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z v : StateDirections S × ℝ) (t : ℝ) (p : PolarPoint) :
    stateU S (liftSectorParameter S C (z + t • v)).1 p =
      stateU S (liftSectorParameter S C z).1 p + t * heightPairField S v.1.val.1 p := by
  change (S.height (3 / 4 : ℝ)).decode
      (C.referenceState.1.1 + (z.1.val.1.1 + t • v.1.val.1.1)) p +
      (C.referenceState.1.2 + (z.1.val.1.2 + t * v.1.val.1.2)) * S.chiLeft p.1 =
    (S.height (3 / 4 : ℝ)).decode (C.referenceState.1.1 + z.1.val.1.1) p +
      (C.referenceState.1.2 + z.1.val.1.2) * S.chiLeft p.1 +
      t * ((S.height (3 / 4 : ℝ)).decode v.1.val.1.1 p + v.1.val.1.2 * S.chiLeft p.1)
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem liftSectorParameter_direction_control
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z v : StateDirections S × ℝ) (t : ℝ) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (liftSectorParameter S C (z + t • v)).1.2.2.1 m θ =
      (S.circle (3 / 4 : ℝ)).decode (liftSectorParameter S C z).1.2.2.1 m θ +
        t * (S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m θ := by
  change (S.circle (3 / 4 : ℝ)).decode
      (C.referenceState.2.2.1 + (z.1.val.2.2.1 + t • v.1.val.2.2.1)) m θ =
    (S.circle (3 / 4 : ℝ)).decode (C.referenceState.2.2.1 + z.1.val.2.2.1) m θ +
      t * (S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m θ
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem height_line_add_constant (a t b c : ℝ) :
    a + t * (b + c) = (a + t * b) + t * c := by ring

theorem N01Properties.ordinaryFlowFamily_state_line_locality
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (v w : StateDirections S × ℝ) (hvq : v.2 = 0) (hwq : w.2 = 0)
    (m b : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hκ : (S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m 0 =
      (S.circle (3 / 4 : ℝ)).decode w.1.val.2.2.1 m 0)
    (c : ℝ) (hheight : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S v.1.val.1 (s, ψ) = heightPairField S w.1.val.1 (s, ψ) + c) :
    (fun t : ℝ => ordinaryFlowFamily S C m 0 b (r, θ)
      (liftSectorParameter S C (z + t • v))) =ᶠ[𝓝 0]
    (fun t : ℝ => ordinaryFlowFamily S C m 0 b (r, θ)
      (liftSectorParameter S C (z + t • w))) := by
  filter_upwards [sectorParameter_line_eventually_mem hz v,
    sectorParameter_line_eventually_mem hz w] with t htv htw
  have hq : (liftSectorParameter S C (z + t • v)).2 =
      (liftSectorParameter S C (z + t • w)).2 := by
    change z.2 + t * v.2 = z.2 + t * w.2
    exact congrArg (fun q : ℝ => z.2 + t * q) (hvq.trans hwq.symm)
  have hprofile : EqOn
      (stateProfile D S C (liftSectorParameter S C (z + t • v)).1)
      (stateProfile D S C (liftSectorParameter S C (z + t • w)).1)
      (Ioo (C.left m) (C.right m)) := by
    intro s hs
    have hv := (stateKappa_eq_decode_zero
      (hN.2.2.1.liftSectorParameter_sector (z + t • v)) m).trans
        (liftSectorParameter_direction_control S C z v t m 0)
    have hw := (stateKappa_eq_decode_zero
      (hN.2.2.1.liftSectorParameter_sector (z + t • w)) m).trans
        (liftSectorParameter_direction_control S C z w t m 0)
    have hk := hv.trans ((congrArg (fun q : ℝ =>
      (S.circle (3 / 4 : ℝ)).decode (liftSectorParameter S C z).1.2.2.1 m 0 + t * q)
        hκ).trans hw.symm)
    exact (hN.stateProfile_on_component _ m hs).trans
      ((congrArg (fun q : ℝ => D.w s * Real.exp (q * C.control m s)) hk).trans
        (hN.stateProfile_on_component _ m hs).symm)
  have hu : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      stateU S (liftSectorParameter S C (z + t • v)).1 (s, ψ) =
        stateU S (liftSectorParameter S C (z + t • w)).1 (s, ψ) + t * c := by
    intro s hs ψ
    have hv := liftSectorParameter_direction_height S C z v t (s, ψ)
    have hw := liftSectorParameter_direction_height S C z w t (s, ψ)
    have hh := congrArg (fun q : ℝ =>
      stateU S (liftSectorParameter S C z).1 (s, ψ) + t * q) (hheight s hs ψ)
    exact hv.trans (hh.trans ((height_line_add_constant _ _ _ _).trans
      (congrArg (fun q : ℝ => q + t * c) hw.symm)))
  have hflow (ψ : ℝ) := hN.minusFlow_eq_of_local_profile_height hS hT
    (liftSectorParameter_mem_stateNeighborhood htv le_rfl)
    (liftSectorParameter_mem_stateNeighborhood htw le_rfl)
    (hN.2.2.1.liftSectorParameter_sector _) hq m hprofile (t * c) hu ψ hr
  have heq :
      (fun ψ => C.minusFlow (liftSectorParameter S C (z + t • v)) m r ψ -
        C.minusFlow (C.referenceState, 0) m r ψ) =
      (fun ψ => C.minusFlow (liftSectorParameter S C (z + t • w)) m r ψ -
        C.minusFlow (C.referenceState, 0) m r ψ) := by
    funext ψ
    exact congrArg (fun a => a - C.minusFlow (C.referenceState, 0) m r ψ) (hflow ψ)
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero] using
    congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ) heq

theorem N01Properties.ordinaryFlowFamily_first_state_jet_locality
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (v w : StateDirections S × ℝ) (hvq : v.2 = 0) (hwq : w.2 = 0)
    (m b : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hκ : (S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m 0 =
      (S.circle (3 / 4 : ℝ)).decode w.1.val.2.2.1 m 0)
    (c : ℝ) (hheight : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S v.1.val.1 (s, ψ) = heightPairField S w.1.val.1 (s, ψ) + c)
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y))) :
    J.D 1 z (fun _ => v) = J.D 1 z (fun _ => w) := by
  have heq := (hN.ordinaryFlowFamily_state_line_locality hS hT hz v w hvq hwq
    m b θ hr hκ c hheight).deriv_eq
  exact (J.deriv_line z v hz).symm.trans (heq.trans (J.deriv_line z w hz))

theorem N01Properties.ordinaryFlowFamily_state_jet_locality
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (v w : StateDirections S × ℝ) (hvq : v.2 = 0) (hwq : w.2 = 0)
    (m b : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hκ : (S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m 0 =
      (S.circle (3 / 4 : ℝ)).decode w.1.val.2.2.1 m 0)
    (c : ℝ) (hheight : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S v.1.val.1 (s, ψ) = heightPairField S w.1.val.1 (s, ψ) + c)
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y)))
    (n : ℕ) (vs : Fin n → (StateDirections S × ℝ)) :
    J.D (n + 1) z (Fin.snoc vs v) = J.D (n + 1) z (Fin.snoc vs w) := by
  exact J.snoc_jet_eq_of_first_jet_eq v w
    (fun y hy => hN.ordinaryFlowFamily_first_state_jet_locality hS hT hy
      v w hvq hwq m b θ hr hκ c hheight J) n z hz vs

end ContinuousFlexibility.Statements
