module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryAffineSpatialWords
public import ContinuousFlexibility.Analysis.N04PositiveGeometryFixedSpatialWords
public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
public import ContinuousFlexibility.Analysis.JointMixedTransportCalculus

/-!
# Fixed unit-coordinate normalizations of positive parameter jets

The physical unit interval has a uniform finite linear cost. Fixed
angular defects and fixed radial origins vanish in positive parameter
derivatives. A radial division contributes only the displayed reciprocal
width.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_unitPullback_word_bound
    {U : Set E} (hU : IsOpen U) {f : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ univ) f) (l r : ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hspan : |r - l| ≤ C)
    (Q : SmoothDirections (U ×ˢ unitStrip)
      (fun z : E × PolarPoint => f (z.1, (l + (r - l) * z.2.1, z.2.2))))
    (p q : Seminorm ℝ E) {R M : ℝ} (hR : 0 ≤ R)
    (n : ℕ) (w : StateAngleWord n) (x : E) (hx : x ∈ U)
    (y : PolarPoint) (hy : y ∈ unitStrip)
    (hbound : ∀ u : Fin n → E × PolarPoint,
      (∀ i, p (u i).1 ≤ 1) → (∀ i, q (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (u i).1 = 0) →
      (∀ i, w.isState i = true → (u i).2 = 0) →
      ‖J.D n (x, (l + (r - l) * y.1, y.2)) u‖ ≤ M)
    (v : Fin n → E × PolarPoint)
    (hvL : ∀ i, p (v i).1 ≤ 1) (hvH : ∀ i, q (v i).1 ≤ R)
    (hvS : ∀ i, ‖(v i).2‖ ≤ 1)
    (hv0 : ∀ i, w.isState i = false → (v i).1 = 0)
    (hv1 : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖Q.D n (x, y) v‖ ≤ C ^ n * M := by
  let L : PolarPoint →L[ℝ] PolarPoint :=
    ((r - l) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL : ‖L‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hC)
    intro u
    change ‖((r - l) * u.1, u.2)‖ ≤ C * ‖u‖
    rw [Prod.norm_def]
    apply max_le
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul hspan (norm_fst_le u) (norm_nonneg _) (zero_le_one.trans hC)
    · exact (norm_snd_le u).trans (le_mul_of_one_le_left (norm_nonneg _) hC)
  have hLval (q : PolarPoint) : (l, 0) + L q = (l + (r - l) * q.1, q.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
      Prod.mk_add_mk, zero_add]
  let Q' : SmoothDirections (U ×ˢ unitStrip)
      (fun z : E × PolarPoint => f (z.1, (l, 0) + L z.2)) :=
    Q.congrOn (fun z _ => congrArg (fun p => f (z.1, p)) (hLval z.2).symm)
  have hb := n04PositiveGeometry_affineSpatial_word_bound J hU
    (isOpen_Ioo.prod isOpen_univ) L (l, 0) (fun _ _ => mem_univ _) Q'
    p q hC hL hR n w x hx y hy
    (fun u huL huH huS hu0 hu1 => by
      simpa only [hLval] using hbound u huL huH huS hu0 hu1)
    v hvL hvH hvS hv0 hv1
  exact hb

theorem n04PositiveGeometry_unitAngleDefect_word_bound
    {U : Set E} (hU : IsOpen U) {f : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ unitStrip) f)
    (Q : SmoothDirections (U ×ˢ unitStrip) (fun z : E × PolarPoint => f z - z.2.2))
    {n : ℕ} (w : StateAngleWord n) (hw : 0 < w.stateArity)
    {x : E} (hx : x ∈ U) {q : PolarPoint} (hq : q ∈ unitStrip)
    (v : Fin n → E × PolarPoint)
    (hv : ∀ j, w.isState j = true → (v j).2 = 0) :
    Q.D n (x, q) v = J.D n (x, q) v := by
  have hV : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  let L : (E × PolarPoint) →L[ℝ] ℝ :=
    -(ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let Jθ : SmoothDirections (U ×ˢ unitStrip) (fun z : E × PolarPoint => -z.2.2) :=
    (smoothDirectionsLinearOn L (hU.prod hV)).congrOn (fun _ _ => rfl)
  exact n04PositiveGeometry_sub_fixedSpatial_stateWord hU hV contDiff_snd.contDiffOn
    J Q Jθ w hw hx hq v hv

theorem n04PositiveGeometry_positiveMixed_fixedAffine
    {U : Set E} {Ω : Set PolarPoint} (hΩ : IsOpen Ω)
    {f : E → PolarPoint → ℝ} {g : PolarPoint → ℝ}
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (c : ℝ) (a b : ℕ) {q : PolarPoint} (hq : q ∈ Ω)
    (J : SmoothDirections U (fun x => mixedDerivative a b (f x) q))
    (Q : SmoothDirections U
      (fun x => mixedDerivative a b (fun p => c * (f x p - g p)) q))
    {k : ℕ} (hk : 0 < k) {x : E} (hx : x ∈ U) (v : Fin k → E) :
    Q.D k x v = c * J.D k x v := by
  let d := mixedDerivative a b g q
  let JD : SmoothDirections U (fun y => mixedDerivative a b (f y) q - d) :=
    (smoothDirectionsAdd J (smoothDirections_constant J.open_domain (-d))).congrOn
      (fun _ _ => (sub_eq_add_neg _ _).symm)
  let L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  let JC := smoothDirections_postcompCLM JD L
  let Q' : SmoothDirections U (fun y => c * (mixedDerivative a b (f y) q - d)) :=
    Q.congrOn (fun y hy => (mixedDerivative_const_mul c _ a b q).trans
      (congrArg (fun t : ℝ => c * t)
        (mixedDerivative_sub_of_contDiffOn hΩ (hf y hy) hg a b hq)))
  have he : Q.D k x v = c * JD.D k x v :=
    (congrArg (fun A => A v) (Q'.unique JC k x hx)).trans
      (smoothDirections_postcompCLM_D_apply JD L k x v)
  exact he.trans (congrArg (fun t : ℝ => c * t)
    (smoothDirections_D_sub_constant J JD hk hx v))

end ContinuousFlexibility.Analysis
