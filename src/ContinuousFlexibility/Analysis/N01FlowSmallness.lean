import ContinuousFlexibility.Analysis.N01CoefficientSmallness
import ContinuousFlexibility.Analysis.N01FlowAngularSmoothness
import ContinuousFlexibility.Analysis.N01RadialFlow
import Mathlib.Topology.Order.OrderClosed

/-!
# Actual ordinary flows remain uniformly close to the reference flow

The genuine first parameter variation from N01 bounds every pure angular
jet difference linearly in the radius of a sufficiently high common
neighborhood. Continuity of the actual angular jets extends the interior
tower estimates to both return radii. Material absorption then yields
uniform quantitative bounds for the value and angular derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem ordinaryFlowFamily_reference_zero
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m a b : ℕ) (p : PolarPoint) :
    ordinaryFlowFamily S C m a b p (C.referenceState, 0) = 0 := by
  simp only [ordinaryFlowFamily, sub_self, mixedDerivative,
    iteratedDeriv_const, ite_self]

theorem N01Properties.ordinaryFlowFamily_angular_small_of_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ base' : ℕ, base ≤ base' → s + loss ≤ base' →
      ∀ η : ℝ, η ≤ ε → η ≤ 1 / 2 →
      ∀ z ∈ stateNeighborhood S C base' η, ∀ m b p,
        b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
        |ordinaryFlowFamily S C m 0 b p z| ≤
          6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B * η := by
  let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.2 1 s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ base' : ℕ, base ≤ base' → s + loss ≤ base' →
      ∀ η : ℝ, η ≤ ε → η ≤ 1 / 2 →
      ∀ z ∈ stateNeighborhood S C base' η, ∀ m b p,
        b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
        |ordinaryFlowFamily S C m 0 b p z| ≤
          6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B * η := by
    intro base' hb hh η hηε hη₁ z hz m b p hbs hp
    have hzold := stateNeighborhood_mono S C hb hηε hz
    obtain ⟨J, hJ⟩ := hdata.choose_spec.2 m 0 b p (by simpa only [zero_add] using hbs) hp
    obtain ⟨_, hRef⟩ := hN.1.1
    have hsample := materialSample_mem_radialCore hT hRef.2.1 (C.cell m)
    have hH : 0 < T.H (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.1
    have hE : 0 < T.E0 (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.2.1
    let A := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B
    have hA : 0 ≤ A := mul_nonneg
      (mul_nonneg hB.le (Real.rpow_nonneg hH.le _)) (Real.rpow_nonneg hE.le _)
    have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        (C.referenceState, (0 : ℝ)) + t • (z - (C.referenceState, 0)) ∈
          stateNeighborhood S C base ε := stateNeighborhood_segment S C hzold ht
    have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        |J.D 1 ((C.referenceState, 0) + t • (z - (C.referenceState, 0)))
          (fun _ => z - (C.referenceState, 0))| ≤
          A * oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss)
            (((C.referenceState, 0) + t • (z - (C.referenceState, 0))) -
              (C.referenceState, 0)) (fun _ : Fin 1 => z - (C.referenceState, 0)) := by
      simpa only [pow_zero, one_mul] using
        hJ _ (hline t ht) (fun _ : Fin 1 => z - (C.referenceState, 0))
    have hsmall := J.abs_le_of_first_variation_small
      (pairGrading (stateGrading S) realGrading) base (s + loss)
      (C.referenceState, 0) z hline (ordinaryFlowFamily_reference_zero S C m 0 b p)
      hA hη₁ (stateNeighborhood_pairGrading_lt S C hb hz).le
      (stateNeighborhood_pairGrading_lt S C hh hz).le hbound
    calc
      _ ≤ 6 * A * η := hsmall
      _ = _ := by dsimp only [A]; ring
  exact Exists.intro B (And.intro hB hpoint)

theorem N01Properties.minusFlow_reference_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    C.minusFlow (C.referenceState, 0) m r θ =
      θ - opticalTravel D.w (C.left m) r := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hprofile : stateProfile D S C C.referenceState = D.w := by
    funext s
    simp [stateProfile, stateKappa, href.2.2.1, href.2.2.2.1, angularMean]
  have hz₀ : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      rw [sub_self, (stateGrading S base).map_zero']
      exact hN.2.1
    · simpa only [abs_zero] using hN.2.1
  simpa only [hprofile] using hN.minusFlow_zero_eq_opticalTravel hS hT hz₀ m θ hr

theorem N01Properties.minusFlow_reference_angular_deriv
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    deriv (C.minusFlow (C.referenceState, 0) m r) θ = 1 := by
  have heq : C.minusFlow (C.referenceState, 0) m r =
      fun t => t - opticalTravel D.w (C.left m) r :=
    funext (hN.minusFlow_reference_eq hS hT m hr)
  rw [heq]
  exact ((hasDerivAt_id θ).sub_const _).deriv

theorem N01Properties.minusFlow_near_reference_weighted
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ base' : ℕ, base ≤ base' → 1 + loss ≤ base' →
      ∀ η : ℝ, η ≤ ε → η ≤ 1 / 2 →
      ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
      ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      let M := 6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B * η
      |C.minusFlow z m r θ - (θ - opticalTravel D.w (C.left m) r)| ≤ M ∧
        |deriv (C.minusFlow z m r) θ - 1| ≤ M := by
  obtain ⟨B, hB, hb⟩ := hN.ordinaryFlowFamily_angular_small_of_neighborhood hT 1
  refine ⟨B, hB, fun base' hbase hhigh η hηε hη₁ z hz hsector m r hr θ => ?_⟩
  have hzold := stateNeighborhood_mono S C hbase hηε hz
  have hz₀ : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      rw [sub_self, (stateGrading S base).map_zero']
      exact hN.2.1
    · simpa only [abs_zero] using hN.2.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hclosure : closure (Ioo (C.left m) (C.right m)) = Icc (C.left m) (C.right m) :=
    closure_Ioo (hC.1 m).2.1.ne
  have hc₀ : ContinuousOn (fun s => |C.minusFlow z m s θ -
      C.minusFlow (C.referenceState, 0) m s θ|) (Icc (C.left m) (C.right m)) :=
    ((hflow z hzold m θ).2.1.sub (hflow _ hz₀ m θ).2.1).abs
  have hc₁ : ContinuousOn (fun s => |deriv (C.minusFlow z m s) θ - 1|)
      (Icc (C.left m) (C.right m)) := by
    have hj := (hN.minusFlow_angular_iteratedDeriv_continuousOn
      hS hT hzold hsector m 1).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ θ⟩)
    simpa only [iteratedDeriv_one, Function.comp_def, Pi.sub_apply, id_eq] using
      (hj.sub continuousOn_const).abs
  have hv₀ (s : ℝ) (hs : s ∈ Ioo (C.left m) (C.right m)) :
      |C.minusFlow z m s θ - C.minusFlow (C.referenceState, 0) m s θ| ≤
        6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B * η := by
    simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero] using
      hb base' hbase hhigh η hηε hη₁ z hz m 0 (s, θ) (by norm_num) hs
  have hv₁ (s : ℝ) (hs : s ∈ Ioo (C.left m) (C.right m)) :
      |deriv (C.minusFlow z m s) θ - 1| ≤
        6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B * η := by
    have h := hb base' hbase hhigh η hηε hη₁ z hz m 1 (s, θ) le_rfl hs
    simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero,
      iteratedDeriv_one] at h
    rw [deriv_fun_sub
      (N01Properties.minusFlow_differentiable S C z m hN hzold ⟨hs.1.le, hs.2.le⟩ θ)
      (N01Properties.minusFlow_differentiable S C (C.referenceState, 0) m hN hz₀
        ⟨hs.1.le, hs.2.le⟩ θ),
      hN.minusFlow_reference_angular_deriv hS hT m ⟨hs.1.le, hs.2.le⟩ θ] at h
    exact h
  have hv₀' := le_on_closure hv₀ (by simpa only [hclosure] using hc₀) continuousOn_const
    (show r ∈ closure (Ioo (C.left m) (C.right m)) by simpa only [hclosure] using hr)
  have hv₁' := le_on_closure hv₁ (by simpa only [hclosure] using hc₁) continuousOn_const
    (show r ∈ closure (Ioo (C.left m) (C.right m)) by simpa only [hclosure] using hr)
  exact ⟨by simpa only [hN.minusFlow_reference_eq hS hT m hr θ] using hv₀', hv₁'⟩

theorem N01Properties.minusFlow_near_reference_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 < K ∧ ∀ base' : ℕ, base ≤ base' → 1 + loss ≤ base' →
      ∀ η : ℝ, 0 ≤ η → η ≤ ε → η ≤ 1 / 2 →
      ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
      ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      |C.minusFlow z m r θ - (θ - opticalTravel D.w (C.left m) r)| ≤ K * η ∧
        |deriv (C.minusFlow z m r) θ - 1| ≤ K * η := by
  obtain ⟨B, hB, hb⟩ := hN.minusFlow_near_reference_weighted hS hT
  obtain ⟨K, hK, he⟩ := materialSample_H_E0_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  refine ⟨6 * B * K, mul_pos (mul_pos (by norm_num) hB) hK,
    fun base' hbase hhigh η hη hηε hη₁ z hz hsector m r hr θ => ?_⟩
  have h := hb base' hbase hhigh η hηε hη₁ z hz hsector m r hr θ
  have he' := mul_le_mul_of_nonneg_left (he (C.cell m))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hB.le) hη)
  have hM : 6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B * η ≤ (6 * B * K) * η := by
    convert he' using 1 <;> ring
  exact ⟨h.1.trans hM, h.2.trans hM⟩

end ContinuousFlexibility.Statements

