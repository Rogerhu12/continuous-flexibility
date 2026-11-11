import ContinuousFlexibility.Statements.Analysis
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation

/-!
# Differentiating a continuous family of linear inverses

The resolvent identity is used in the original projective topology.  In
particular, continuity of the inverse family is applied simultaneously to
the changing parameter and the converging difference quotient.  No norm on
the space of continuous linear maps is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section Resolvent

variable {X Y Z : Type*}
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]

/-- The exact resolvent identity, with both the parameter and source
allowed to change. -/
theorem inverseFamily_resolvent
    (L : X → Y →ₗ[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    {x x' : X} (hleft : ∀ u, V x' (L x' u) = u)
    (hright : ∀ z, L x (V x z) = z) (y y' : Z) :
    V x' y' - V x y =
      V x' ((y' - y) - (L x' (V x y) - L x (V x y))) := by
  rw [map_sub, map_sub, map_sub, hleft, hright]
  abel

end Resolvent

section InverseDerivative

variable {X Y Z : Type*}
  [TopologicalSpace X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]

/-- Joint continuity supplies each inverse with its actual continuity
proof.  Outside the open parameter set we choose the zero map. -/
def inverseFamilyContinuousLinearMap
    {U : Set X} (V : X → Z →ₗ[ℝ] Y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    (x : X) : Z →L[ℝ] Y := by
  classical
  exact if hx : x ∈ U then
    { toLinearMap := V x
      cont := continuousOn_univ.mp
        (hV.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun z _ => ⟨hx, mem_univ z⟩)) }
  else 0

@[simp] theorem inverseFamilyContinuousLinearMap_apply
    {U : Set X} (V : X → Z →ₗ[ℝ] Y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    {x : X} (hx : x ∈ U) (y : Z) :
    inverseFamilyContinuousLinearMap V hV x y = V x y := by
  simp only [inverseFamilyContinuousLinearMap, dite_eq_left hx,
    ContinuousLinearMap.coe_mk']

/-- Packaging the fibers does not change joint continuity on the domain. -/
theorem continuousOn_inverseFamilyContinuousLinearMap
    {U : Set X} (V : X → Z →ₗ[ℝ] Y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ)) :
    ContinuousOn (fun z : X × Z => inverseFamilyContinuousLinearMap V hV z.1 z.2)
      (U ×ˢ univ) :=
  hV.congr (fun z hz => inverseFamilyContinuousLinearMap_apply V hV hz.1 z.2)

/-- The curve derivative of a continuous inverse family follows directly
from its resolvent identity.  The forward family is differentiated only
at the fixed vector `V (x t) (y t)`. -/
theorem hasProjectiveCurveDerivAt_inverseFamily
    {U : Set X} (hU : IsOpen U)
    (L : X → Y →ₗ[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hleft : ∀ x ∈ U, ∀ u, V x (L x u) = u)
    (hright : ∀ x ∈ U, ∀ z, L x (V x z) = z)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    {x : ℝ → X} {y : ℝ → Z} {t : ℝ} {dy dL : Z}
    (hx : ContinuousAt x t) (hxt : x t ∈ U)
    (hy : HasProjectiveCurveDerivAt y dy t)
    (hL : HasProjectiveCurveDerivAt
      (fun s => L (x s) (V (x t) (y t))) dL t) :
    HasProjectiveCurveDerivAt (fun s => V (x s) (y s))
      (V (x t) (dy - dL)) t := by
  have hshift : Tendsto (fun h : ℝ => t + h) (𝓝[≠] (0 : ℝ)) (𝓝 t) := by
    simpa only [add_zero, id_eq] using (tendsto_const_nhds (x := t)).add
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  have hxshift := hx.tendsto.comp hshift
  have hnear := hxshift.eventually (hU.mem_nhds hxt)
  have hquot : Tendsto
      (fun h : ℝ => h⁻¹ • (y (t + h) - y t) -
        h⁻¹ • (L (x (t + h)) (V (x t) (y t)) - L (x t) (V (x t) (y t))))
      (𝓝[≠] (0 : ℝ)) (𝓝 (dy - dL)) := Filter.Tendsto.sub hy hL
  have hVc : ContinuousAt (fun z : X × Z => V z.1 z.2) (x t, dy - dL) :=
    (hV (x t, dy - dL) ⟨hxt, mem_univ _⟩).continuousAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hxt, mem_univ _⟩)
  have hlim := hVc.tendsto.comp (hxshift.prodMk_nhds hquot)
  unfold HasProjectiveCurveDerivAt
  apply hlim.congr'
  filter_upwards [hnear] with h hh
  change V (x (t + h))
      (h⁻¹ • (y (t + h) - y t) -
        h⁻¹ • (L (x (t + h)) (V (x t) (y t)) - L (x t) (V (x t) (y t)))) =
    h⁻¹ • (V (x (t + h)) (y (t + h)) - V (x t) (y t))
  have hres := inverseFamily_resolvent L V
    (x := x t) (x' := x (t + h))
    (hleft (x (t + h)) hh) (hright (x t) hxt) (y t) (y (t + h))
  calc
    _ = h⁻¹ • V (x (t + h))
        ((y (t + h) - y t) -
          (L (x (t + h)) (V (x t) (y t)) - L (x t) (V (x t) (y t)))) := by
      rw [← smul_sub, map_smul]
    _ = _ := congrArg (fun w : Y => h⁻¹ • w) hres.symm

variable [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The actual joint directional derivative of the inverse family. -/
theorem hasProjectiveLineDerivAt_inverseFamily
    {U : Set X} (hU : IsOpen U)
    (L : X → Y →L[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hleft : ∀ x ∈ U, ∀ u, V x (L x u) = u)
    (hright : ∀ x ∈ U, ∀ z, L x (V x z) = z)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    {x : X} (hx : x ∈ U) (y : Z) (h : X) (k : Z) :
    HasProjectiveLineDerivAt (fun z : X × Z => V z.1 z.2)
      (V x (k - J.D 1 (x, V x y) (Fin.cons (h, 0) Fin.elim0)))
      (x, y) (h, k) := by
  have hJ : HasProjectiveJetsOn (fun z : X × Y => L z.1 z.2) J.D (U ×ˢ univ) :=
    ⟨J.zero, J.continuous, fun n z hz w v => J.derivative n z hz v w⟩
  have hL := hJ.hasLineDerivAt J.open_domain
    (x := (x, V x y)) ⟨hx, mem_univ (V x y)⟩ (h, 0)
  have hL' : HasProjectiveCurveDerivAt
      (fun t : ℝ => L (x + t • h) (V x y))
      (J.D 1 (x, V x y) (Fin.cons (h, 0) Fin.elim0)) 0 := by
    simpa only [HasProjectiveLineDerivAt, projectiveFirstJetValue,
      Prod.smul_mk, Prod.fst_add, Prod.snd_add, smul_zero, add_zero] using hL
  have hy : HasProjectiveCurveDerivAt (fun t : ℝ => y + t • k) k 0 := by
    simpa only [HasProjectiveLineDerivAt, ContinuousLinearMap.id_apply] using
      hasProjectiveLineDerivAt_clm (ContinuousLinearMap.id ℝ Z) y k
  have hi := hasProjectiveCurveDerivAt_inverseFamily hU (fun x => (L x).toLinearMap) V
    hleft hright hV
    (x := fun t : ℝ => x + t • h) (y := fun t : ℝ => y + t • k)
    (t := 0) (dy := k)
    (dL := J.D 1 (x, V x y) (Fin.cons (h, 0) Fin.elim0))
    ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt)
    (by simpa only [zero_smul, add_zero] using hx) hy
    (by simpa only [zero_smul, add_zero, ContinuousLinearMap.coe_coe] using hL')
  simpa only [HasProjectiveLineDerivAt, Prod.smul_mk, Prod.fst_add, Prod.snd_add,
    zero_smul, add_zero] using hi

end InverseDerivative

end ContinuousFlexibility.Analysis
