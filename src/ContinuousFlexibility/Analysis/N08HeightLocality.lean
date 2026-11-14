module

public import ContinuousFlexibility.Analysis.N08FlowLocality

/-!
# Local height rescaling preserves the actual return map

The characteristic coefficients depend on the first height jets, and their
spatial derivatives, on the chosen negative component. Thus two different
external parameters give the same actual flow whenever their scaled heights
agree locally up to a constant. This includes the constant endpoint-height
coordinate and permits a compactly supported rescaling of the decaying
height coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem n08_scaled_height_jets_eq_of_germ
    {u v : PolarPoint → ℝ} {p : PolarPoint} {q q' c : ℝ}
    (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p)
    (h : (fun y => q * u y) =ᶠ[𝓝 p] (fun y => q' * v y + c)) :
    q * heightRadial u p = q' * heightRadial v p ∧
      q * heightAngular u p = q' * heightAngular v p := by
  have hd := h.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_add_const, fderiv_const_mul hu, fderiv_const_mul hv] at hd
  have hr := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hd
  have ha := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hd
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hr ha
  refine ⟨hr, ?_⟩
  simpa only [heightAngular, angularPartial, mul_div_assoc] using
    congrArg (fun t : ℝ => t / p.1) ha

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

/-- Only the actual scaled height germ is required; the constants may
vary between components, and no global equality of heights is imposed. -/
theorem n08_originalCoefficients_eq_of_local_height
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (hheight : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S y p + c))
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    (originalCoefficients D S C (x, q)).a (r, θ) =
        (originalCoefficients D S C (y, q')).a (r, θ) ∧
      (originalCoefficients D S C (x, q)).b (r, θ) =
        (originalCoefficients D S C (y, q')).b (r, θ) ∧
      (originalCoefficients D S C (x, q)).c (r, θ) =
        (originalCoefficients D S C (y, q')).c (r, θ) := by
  have hw := n08_stateProfile_component_germ hN.2.2.2.1 hν hκ hr
  have hn : ∀ᶠ p : PolarPoint in 𝓝 (r, θ), p.1 ∈ Ioo (C.left m) (C.right m) :=
    continuous_fst.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hr)
  have hwp := hw.comp_tendsto
    (continuous_fst.continuousAt : ContinuousAt Prod.fst (r, θ))
  have hjets (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
      q * heightRadial (stateU S x) p = q' * heightRadial (stateU S y) p ∧
        q * heightAngular (stateU S x) p = q' * heightAngular (stateU S y) p := by
    obtain ⟨c, hc⟩ := hheight p.1 hp p.2
    exact n08_scaled_height_jets_eq_of_germ
      ((n08_stateU_contDiff hT hS x).differentiable (by simp) p)
      ((n08_stateU_contDiff hT hS y).differentiable (by simp) p) hc
  have hk : heightRadial (stateHeight D S C (x, q)) =ᶠ[𝓝 (r, θ)]
      heightRadial (stateHeight D S C (y, q')) := by
    filter_upwards [hn, hwp] with p hp hprof
    simp only [Function.comp_apply] at hprof
    rw [n08_heightRadial_stateHeight hT hS hN, n08_heightRadial_stateHeight hT hS hN,
      hprof, (hjets p hp).1]
  have hp : heightAngular (stateHeight D S C (x, q)) =ᶠ[𝓝 (r, θ)]
      heightAngular (stateHeight D S C (y, q')) := by
    filter_upwards [hn] with p hp
    rw [n08_heightAngular_stateHeight hT hS hN, n08_heightAngular_stateHeight hT hS hN,
      (hjets p hp).2]
  exact n08_polarCoefficients_eq_of_germs hw hk hp

theorem n08_minusFlow_eq_of_local_height
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q') ∈ stateNeighborhood S C base ε) (hsx : stateSector S x)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (hheight : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S y p + c))
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, q) m r θ = C.minusFlow (y, q') m r θ := by
  apply n08_minusFlow_component_eq_of_speed hT hS hN hx hy hsx ?_ θ hr
  intro t ht φ
  obtain ⟨ha, hb, hc⟩ := n08_originalCoefficients_eq_of_local_height hT hS hN hν hκ
    hheight ht φ
  simp only [minusCharacteristicSpeed, ha, hb, hc]

theorem n08_returnResidual_eq_of_local_height
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q') ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (hheight : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S y p + c))
    (hchart : stateLeftChart S x m = stateLeftChart S y m) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (R.residual (x, q)) m θ =
      (S.circle (3 / 4 : ℝ)).decode (R.residual (y, q')) m θ := by
  rw [hR.2.1 (x, q) hx hsx m θ, hR.2.1 (y, q') hy hsy m θ]
  exact n08_returnResidualField_component_eq_of_flow hR hx hy hsx hsy
    (fun φ => n08_minusFlow_eq_of_local_height hT hS hN hx hy hsx hν hκ hheight φ
      ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩) hchart θ

end ContinuousFlexibility.Statements
