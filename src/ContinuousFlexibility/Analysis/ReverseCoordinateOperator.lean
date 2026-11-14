module

public import ContinuousFlexibility.Analysis.CoordinateOperatorConstruction
public import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities
public import ContinuousFlexibility.Geometry.PlanarOrientation
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A smooth effective physical operator from a genuine canonical action

Only the forward chart, its interior inverse, the height, and the canonical
coefficient field are assumed smooth. The stored physical coefficient field
may be arbitrary. The canonical identity for global smooth tests determines
its actual action locally: a real smooth cutoff extends each required germ
to an admissible global test. Reversing the coordinate change gives a smooth
principal field, and the constant test removes the entire zeroth-order term.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A smooth function on an open set has a genuine global smooth
representative of its germ at each point, constructed with a smooth bump. -/
theorem exists_global_contDiff_germ_of_open
    {U : Set PolarPoint} (hU : IsOpen U) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {x : PolarPoint} (hx : x ∈ U) :
    ∃ g : PolarPoint → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hsupport : tsupport (χ : PolarPoint → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    intro y hy
    apply hball
    apply Metric.mem_ball.mpr
    have hy' : dist y x ≤ ε / 2 := Metric.mem_closedBall.mp hy
    linarith
  let g : PolarPoint → ℝ := fun y => χ y * f y
  have hχ : ContDiff ℝ ∞ (χ : PolarPoint → ℝ) := χ.contDiff
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport (χ : PolarPoint → ℝ)
    · exact hχ.contDiffAt.mul
        ((hf y (hsupport hy)).contDiffAt (hU.mem_nhds (hsupport hy)))
    · have hz := notMem_tsupport_iff_eventuallyEq.mp hy
      have he : g =ᶠ[𝓝 y] (fun _ : PolarPoint => (0 : ℝ)) := by
        filter_upwards [hz] with z hz
        simp only [g, hz, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨g, hg, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  have hy' : χ y = 1 := hy
  simp only [g, hy', one_mul]

/-- The actual divergence is local even when its stored coefficients have
no assumed regularity. No product rule for those coefficients is used. -/
theorem divergenceOperator_eq_of_germ
    (A : SymmetricCoefficients) {u v : PolarPoint → ℝ} {x : PolarPoint}
    (huv : u =ᶠ[𝓝 x] v) :
    divergenceOperator A u x = divergenceOperator A v x := by
  have hd : fderiv ℝ u =ᶠ[𝓝 x] fderiv ℝ v := huv.fderiv
  have hr : radialPartial u =ᶠ[𝓝 x] radialPartial v :=
    hd.mono fun y hy => congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hy
  have ht : angularPartial u =ᶠ[𝓝 x] angularPartial v :=
    hd.mono fun y hy => congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hy
  have hradial :
      (fun y => A.a y * radialPartial u y + A.b y * angularPartial u y) =ᶠ[𝓝 x]
        (fun y => A.a y * radialPartial v y + A.b y * angularPartial v y) := by
    filter_upwards [hr, ht] with y hyr hyt
    rw [hyr, hyt]
  have hangular :
      (fun y => A.b y * radialPartial u y + A.c y * angularPartial u y) =ᶠ[𝓝 x]
        (fun y => A.b y * radialPartial v y + A.c y * angularPartial v y) := by
    filter_upwards [hr, ht] with y hyr hyt
    rw [hyr, hyt]
  change
    (fderiv ℝ (fun y => A.a y * radialPartial u y + A.b y * angularPartial u y) x) (1, 0) +
      (fderiv ℝ (fun y => A.b y * radialPartial u y + A.c y * angularPartial u y) x) (0, 1) =
    (fderiv ℝ (fun y => A.a y * radialPartial v y + A.b y * angularPartial v y) x) (1, 0) +
      (fderiv ℝ (fun y => A.b y * radialPartial v y + A.c y * angularPartial v y) x) (0, 1)
  rw [hradial.fderiv_eq (𝕜 := ℝ), hangular.fderiv_eq (𝕜 := ℝ)]

/-- The effective physical coefficients use the actual inverse chart as
the reverse coordinate change and the reciprocal transported height. -/
def reverseCoordinatePrincipalCoefficients (A : SymmetricCoefficients)
    (F G : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) : SymmetricCoefficients :=
  inverseChartPrincipalCoefficients A G F (fun y => 1 / h (G y))

private theorem reverse_operator_scalar
    {h J Ji P C D V Q u : ℝ}
    (hh : h ≠ 0) (hJ : J ≠ 0) (hprod : Ji * J = 1)
    (hforward : h * P / J = C + V * (u / h))
    (hreverse : (1 / h) * C / Ji = D + Q * u) :
    P = D + (Q + (J / h) * (V / h)) * u := by
  have hJi : Ji = 1 / J := (eq_div_iff hJ).mpr hprod
  have hscale : J / h * (h * P / J) = P := by
    field_simp [hh, hJ]
  have hrev : J / h * C = D + Q * u := by
    calc
      J / h * C = (1 / h) * C / Ji := by
        rw [hJi]
        field_simp [hh, hJ]
      _ = D + Q * u := hreverse
  calc
    P = J / h * (h * P / J) := hscale.symm
    _ = J / h * (C + V * (u / h)) := congrArg (fun r : ℝ => J / h * r) hforward
    _ = J / h * C + (J / h) * (V / h) * u := by ring
    _ = D + (Q + (J / h) * (V / h)) * u := by rw [hrev]; ring

/-- A canonical operator identity on all global smooth tests determines
a genuine smooth physical divergence action. No smoothness, continuity,
or differentiability of the stored physical field L is assumed. -/
theorem reverseCoordinateOperator_action
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {L A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h pot : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G V)
    (hh : ContDiffOn ℝ ∞ h U)
    (hAa : ContDiffOn ℝ ∞ A.a V) (hAb : ContDiffOn ℝ ∞ A.b V)
    (hAc : ContDiffOn ℝ ∞ A.c V)
    (hFV : MapsTo F U V) (hGU : MapsTo G V U)
    (hGF : ∀ x ∈ U, G (F x) = x)
    (hFG : ∀ y ∈ V, F (G y) = y)
    (hh0 : ∀ x ∈ U, h x ≠ 0)
    {x : PolarPoint} (hx : x ∈ U)
    (hop : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x * divergenceOperator L (fun y => h y * W (F y)) x /
          |planeJacobian F x| =
        divergenceOperator A W (F x) + pot (F x) * W (F x)) :
    ContDiffAt ℝ ∞ (reverseCoordinatePrincipalCoefficients A F G h).a x ∧
      ContDiffAt ℝ ∞ (reverseCoordinatePrincipalCoefficients A F G h).b x ∧
      ContDiffAt ℝ ∞ (reverseCoordinatePrincipalCoefficients A F G h).c x ∧
      ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
        divergenceOperator L u x =
          divergenceOperator (reverseCoordinatePrincipalCoefficients A F G h) u x := by
  let k : PolarPoint → ℝ := fun y => 1 / h (G y)
  let B : SymmetricCoefficients := inverseChartPrincipalCoefficients A G F k
  let Q : PolarPoint → ℝ := inverseChartPotential A G F k
  have hy : F x ∈ V := hFV hx
  have hFx : ContDiffAt ℝ ∞ F x := (hF x hx).contDiffAt (hU.mem_nhds hx)
  have hGy : ContDiffAt ℝ ∞ G (F x) := (hG (F x) hy).contDiffAt (hV.mem_nhds hy)
  have hGFx : G (F x) = x := hGF x hx
  have hGFgerm : G ∘ F =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hGF y hy
  have hFGgerm : F ∘ G =ᶠ[𝓝 (F x)] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hV.mem_nhds hy] with y hy
    exact hFG y hy
  have hJid : planeJacobian (G ∘ F) x = 1 := by
    unfold planeJacobian
    rw [hGFgerm.fderiv_eq]
    simp only [fderiv_id, ContinuousLinearMap.id_apply, one_mul, zero_mul, sub_zero]
  have hJprod : planeJacobian G (F x) * planeJacobian F x = 1 :=
    (planeJacobian_comp (hFx.differentiableAt (by simp))
      (hGy.differentiableAt (by simp))).symm.trans hJid
  have hJG : planeJacobian G (F x) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hJprod
    exact zero_ne_one hJprod
  have hJF : planeJacobian F x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hJprod
    exact zero_ne_one hJprod
  have hAbs : |planeJacobian G (F x)| * |planeJacobian F x| = 1 := by
    rw [← abs_mul, hJprod, abs_one]
  have hk : ContDiffOn ℝ ∞ k V :=
    contDiffOn_const.div (hh.comp hG hGU) (fun y hy => hh0 (G y) (hGU hy))
  have hky : ContDiffAt ℝ ∞ k (F x) := (hk (F x) hy).contDiffAt (hV.mem_nhds hy)
  have hax := (hAa (F x) hy).contDiffAt (hV.mem_nhds hy)
  have hbx := (hAb (F x) hy).contDiffAt (hV.mem_nhds hy)
  have hcx := (hAc (F x) hy).contDiffAt (hV.mem_nhds hy)
  have hDensity := contDiffAt_coordinatePrincipalDensity hax hbx hcx hGy hky hJG
  have hBa : ContDiffAt ℝ ∞ B.a x := hDensity.1.comp x hFx
  have hBb : ContDiffAt ℝ ∞ B.b x := hDensity.2.1.comp x hFx
  have hBc : ContDiffAt ℝ ∞ B.c x := hDensity.2.2.comp x hFx
  have haction (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
      divergenceOperator L u x = divergenceOperator B u x +
        (Q x + (|planeJacobian F x| / h x) * (pot (F x) / h x)) * u x := by
    let f : PolarPoint → ℝ := fun y => k y * u (G y)
    have huG : ContDiffOn ℝ ∞ (u ∘ G) V := hu.comp_contDiffOn hG
    have hf : ContDiffOn ℝ ∞ f V := hk.mul huG
    obtain ⟨W, hW, hWgerm⟩ := exists_global_contDiff_germ_of_open hV hf hy
    have hpull : (fun y => h y * W (F y)) =ᶠ[𝓝 x] u := by
      filter_upwards [hFx.continuousAt.tendsto.eventually hWgerm, hU.mem_nhds hx]
        with y hWy hy
      rw [hWy]
      dsimp only [f, k]
      rw [hGF y hy]
      field_simp [hh0 y hy]
    have hWvalue : W (F x) = u x / h x := by
      rw [hWgerm.self_of_nhds]
      dsimp only [f, k]
      rw [hGFx]
      ring
    have hforward := hop W hW
    rw [divergenceOperator_eq_of_germ L hpull,
      divergenceOperator_eq_of_germ A hWgerm, hWvalue] at hforward
    have hFxG : ContDiffAt ℝ ∞ F (G (F x)) := by
      simpa only [hGFx] using hFx
    have hreverse := coordinateOperator_explicit_fields
      hax hbx hcx hGy hFxG hky hu hJG hFGgerm
    change k (F x) * divergenceOperator A f (F x) / |planeJacobian G (F x)| =
      divergenceOperator B u (G (F x)) + Q (G (F x)) * u (G (F x)) at hreverse
    rw [hGFx] at hreverse
    have hkx : k (F x) = 1 / h x := by dsimp only [k]; rw [hGFx]
    rw [hkx] at hreverse
    exact reverse_operator_scalar (hh0 x hx) (abs_ne_zero.mpr hJF)
      hAbs hforward hreverse
  have hzero : Q x + (|planeJacobian F x| / h x) * (pot (F x) / h x) = 0 := by
    simpa only [divergenceOperator_const, mul_one, zero_add] using
      (haction (fun _ : PolarPoint => (1 : ℝ)) contDiff_const).symm
  refine ⟨hBa, hBb, hBc, ?_⟩
  intro u hu
  change divergenceOperator L u x = divergenceOperator B u x
  simpa only [hzero, zero_mul, add_zero] using haction u hu

end ContinuousFlexibility.Analysis
