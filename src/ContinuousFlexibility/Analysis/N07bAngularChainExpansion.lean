import ContinuousFlexibility.Analysis.N07bMaterialAngularChain
import Mathlib.Tactic.FinCases

/-!
# All-order finite expansions of the actual angular source jets

Each differentiation has three branches: differentiate the coefficient,
increase the material radial order, or increase the angular order. A path
records these choices without collecting paths with the same pair of jet
orders. Every coefficient is defined before, and independently of, the
physical source. The resulting finite expansion has exactly `3 ^ j` paths
and every jet occurring at level `j` has total order at most `j`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A path in the three-branch differentiation recursion. -/
def n07bAngularChainIndex : ℕ → Type
  | 0 => Unit
  | j + 1 => n07bAngularChainIndex j × Fin 3

instance n07bAngularChainIndexFintype : (j : ℕ) → Fintype (n07bAngularChainIndex j)
  | 0 => inferInstanceAs (Fintype Unit)
  | j + 1 => by
      letI : Fintype (n07bAngularChainIndex j) := n07bAngularChainIndexFintype j
      exact inferInstanceAs (Fintype (n07bAngularChainIndex j × Fin 3))

def n07bAngularChainRadial : (j : ℕ) → n07bAngularChainIndex j → ℕ
  | 0, _ => 0
  | j + 1, i => n07bAngularChainRadial j i.1 + if i.2 = 1 then 1 else 0

def n07bAngularChainAngular : (j : ℕ) → n07bAngularChainIndex j → ℕ
  | 0, _ => 0
  | j + 1, i => n07bAngularChainAngular j i.1 + if i.2 = 2 then 1 else 0

/-- Actual geometric coefficients, with no source or material function as
an argument. The initial coefficient is the prescribed `h / |J|`. -/
def n07bAngularChainCoefficient {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) : (j : ℕ) → n07bAngularChainIndex j → PolarPoint → ℝ
  | 0, _ => fun x => K.height z m x / |planeJacobian (K.chart z m) x|
  | j + 1, i =>
      if i.2 = 0 then
        n07bMaterialCoeffStay T β (K.chart z m) (n07bAngularChainCoefficient T K z m β j i.1)
      else if i.2 = 1 then
        n07bMaterialCoeffRadial T (K.chart z m) (n07bAngularChainCoefficient T K z m β j i.1)
      else
        n07bMaterialCoeffAngular (K.chart z m) (n07bAngularChainCoefficient T K z m β j i.1)

theorem n07b_angularChain_card (j : ℕ) :
    Fintype.card (n07bAngularChainIndex j) = 3 ^ j := by
  induction j with
  | zero => simp [n07bAngularChainIndex]
  | succ j ih =>
      change Fintype.card (n07bAngularChainIndex j × Fin 3) = 3 ^ (j + 1)
      rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

/-- Each branch raises the total material jet order by at most one. -/
theorem n07b_angularChain_order (j : ℕ) (i : n07bAngularChainIndex j) :
    n07bAngularChainRadial j i + n07bAngularChainAngular j i ≤ j := by
  induction j with
  | zero => simp [n07bAngularChainRadial, n07bAngularChainAngular]
  | succ j ih =>
      rcases i with ⟨i, k⟩
      have hi := ih i
      fin_cases k <;>
        simp [n07bAngularChainRadial, n07bAngularChainAngular] <;> omega

/-- Expanding the last branch is an exact finite-sum identity. It uses no
regularity or source-dependent choices. -/
theorem n07b_angularChain_sum_succ {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (j : ℕ) (u : PolarPoint → ℝ) (x : PolarPoint) :
    (∑ i : n07bAngularChainIndex (j + 1),
      n07bAngularChainCoefficient T K z m β (j + 1) i x *
        mixedDerivative (n07bAngularChainRadial (j + 1) i)
          (n07bAngularChainAngular (j + 1) i) u (n07bMaterialChart T x)) =
      ∑ i : n07bAngularChainIndex j,
        (n07bMaterialCoeffStay T β (K.chart z m)
            (n07bAngularChainCoefficient T K z m β j i) x *
          mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
            u (n07bMaterialChart T x) +
        n07bMaterialCoeffRadial T (K.chart z m)
            (n07bAngularChainCoefficient T K z m β j i) x *
          mixedDerivative (n07bAngularChainRadial j i + 1) (n07bAngularChainAngular j i)
            u (n07bMaterialChart T x) +
        n07bMaterialCoeffAngular (K.chart z m)
            (n07bAngularChainCoefficient T K z m β j i) x *
          mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i + 1)
            u (n07bMaterialChart T x)) := by
  classical
  change (∑ i : n07bAngularChainIndex j × Fin 3, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_three, n07bAngularChainCoefficient,
    n07bAngularChainRadial, n07bAngularChainAngular]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hT hK hz hs

/-- The recursively defined coefficients are genuinely smooth throughout
each physical open piece, by the actual chart and material fields. -/
theorem n07b_angularChainCoefficient_contDiffAt (m : ℕ) (β : ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) :
    ContDiffAt ℝ ∞ (n07bAngularChainCoefficient T K z m β j i) x := by
  have hxcore : x.1 ∈ Ioo D.a D.b := (hK.2.2.2.1 m).2.2 hx.1
  have hxclosed : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) :=
    ⟨hx.1.1.le, hx.1.2.le⟩
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hs m x hxclosed
  induction j with
  | zero =>
      have hJ := ContinuousFlexibility.contDiffAt_planeJacobian hclosed.1
      exact hclosed.2.1.div (hJ.abs hclosed.2.2.1) (abs_ne_zero.mpr hclosed.2.2.1)
  | succ j ih =>
      rcases i with ⟨i, k⟩
      have hc := n07b_contDiffAt_materialChainCoefficients hT hxcore β
        hclosed.1 hclosed.2.2.1 (ih i)
      fin_cases k
      · simpa [n07bAngularChainCoefficient] using hc.1
      · simpa [n07bAngularChainCoefficient] using hc.2.1
      · simpa [n07bAngularChainCoefficient] using hc.2.2

/-- Every actual recursively computed physical source jet has the finite
material expansion with the preassigned geometric coefficients. -/
theorem n07b_physicalSourceJet_material_expansion (m : ℕ) (β : ℝ)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (j : ℕ) {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K m) :
    n07bPhysicalSourceJet K z m f j x = T.H x.1 ^ β *
      ∑ i : n07bAngularChainIndex j, n07bAngularChainCoefficient T K z m β j i x *
        mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
          (materialPullback T β f) (n07bMaterialChart T x) := by
  have hu : ContDiff ℝ ∞ (materialPullback T β f) := contDiff_materialPullback hT hf
  have hopen : IsOpen (physicalPieceOpen S K m) := isOpen_Ioo.prod isOpen_univ
  induction j generalizing x with
  | zero =>
      simpa [n07bAngularChainIndex, n07bAngularChainCoefficient,
        n07bAngularChainRadial, n07bAngularChainAngular, mul_assoc] using
        n07b_physicalSourceJet_zero_material hT K z m β f ((hK.2.2.2.1 m).2.2 hx.1)
  | succ j ih =>
      have hxcore : x.1 ∈ Ioo D.a D.b := (hK.2.2.2.1 m).2.2 hx.1
      have hgerm : n07bPhysicalSourceJet K z m f j =ᶠ[𝓝 x]
          (fun y => T.H y.1 ^ β * ∑ i : n07bAngularChainIndex j,
            n07bAngularChainCoefficient T K z m β j i y *
              mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
                (materialPullback T β f) (n07bMaterialChart T y)) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact ih hy
      have hcoeff (i : n07bAngularChainIndex j) (_ : i ∈ Finset.univ) :
          ContDiffAt ℝ ∞ (n07bAngularChainCoefficient T K z m β j i) x :=
        n07b_angularChainCoefficient_contDiffAt hT hK hz hs m β j i hx
      calc
        n07bPhysicalSourceJet K z m f (j + 1) x =
            n07bInverseAngleDerivative (K.chart z m)
              (fun y => T.H y.1 ^ β * ∑ i : n07bAngularChainIndex j,
                n07bAngularChainCoefficient T K z m β j i y *
                  mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
                    (materialPullback T β f) (n07bMaterialChart T y)) x := by
          change n07bInverseAngleDerivative (K.chart z m) _ x = _
          rw [n07b_inverseAngle_eq_fderiv, n07b_inverseAngle_eq_fderiv]
          exact congrArg (fun L : PolarPoint →L[ℝ] ℝ =>
            L (n07bInverseAngleVector (K.chart z m) x)) (hgerm.fderiv_eq (𝕜 := ℝ))
        _ = T.H x.1 ^ β * ∑ i : n07bAngularChainIndex j,
            (n07bMaterialCoeffStay T β (K.chart z m)
                (n07bAngularChainCoefficient T K z m β j i) x *
              mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
                (materialPullback T β f) (n07bMaterialChart T x) +
            n07bMaterialCoeffRadial T (K.chart z m)
                (n07bAngularChainCoefficient T K z m β j i) x *
              mixedDerivative (n07bAngularChainRadial j i + 1) (n07bAngularChainAngular j i)
                (materialPullback T β f) (n07bMaterialChart T x) +
            n07bMaterialCoeffAngular (K.chart z m)
                (n07bAngularChainCoefficient T K z m β j i) x *
              mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i + 1)
                (materialPullback T β f) (n07bMaterialChart T x)) :=
          n07b_inverseAngle_weighted_material_sum hT (K.chart z m) β Finset.univ
            (n07bAngularChainRadial j) (n07bAngularChainAngular j)
            (n07bAngularChainCoefficient T K z m β j) hu hxcore hcoeff
        _ = _ := by
          rw [n07b_angularChain_sum_succ]

/-- Actual height membership supplies all source regularity used by the
expansion. No estimates or coefficient identities are assumed. -/
theorem n07b_physicalSourceJet_material_expansion_of_heightMember (m : ℕ) (β : ℝ)
    {f : PolarPoint → ℝ} (hf : HeightMember D T β f)
    (j : ℕ) {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K m) :
    n07bPhysicalSourceJet K z m f j x = T.H x.1 ^ β *
      ∑ i : n07bAngularChainIndex j, n07bAngularChainCoefficient T K z m β j i x *
        mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
          (materialPullback T β f) (n07bMaterialChart T x) :=
  n07b_physicalSourceJet_material_expansion hT hK hz hs m β hf.1 j hx

/-- For globally smooth physical sources this is directly an expansion of
the actual canonical angular derivative at the actual chart image. -/
theorem n07b_canonicalSource_material_expansion (m : ℕ) (β : ℝ)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K m) :
    mixedDerivative 0 j (canonicalSource S K z m f) (K.chart z m x) = T.H x.1 ^ β *
      ∑ i : n07bAngularChainIndex j, n07bAngularChainCoefficient T K z m β j i x *
        mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
          (materialPullback T β f) (n07bMaterialChart T x) := by
  rw [n07b_canonicalSource_angularJet_comp_chart_of_contDiff hK hz hs m hf j hx]
  exact n07b_physicalSourceJet_material_expansion hT hK hz hs m β hf.contDiffOn j hx

end ContinuousFlexibility.Analysis
