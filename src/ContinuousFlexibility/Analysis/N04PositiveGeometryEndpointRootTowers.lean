module

public import ContinuousFlexibility.Analysis.N06RootBoundaryRecursion
public import ContinuousFlexibility.Analysis.N01cAngularJetTowers
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Genuine parameter towers of the root transport traces

The regular even/odd root transport equations determine all boundary
traces by finite Leibniz polynomials. Applying their recurrences in radial
order constructs joint state-and-angle towers from the raw coefficient
traces and the original root label. The root-coordinate witness may be
chosen separately at every state: no parameter regularity of that choice
is assumed. Every tower is for the literal trace of that same witness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

/-- The finite Leibniz expression in the root equations preserves genuine
joint towers. Its only differentiated inputs are the lower trace functions. -/
def n04PositiveGeometry_rootJetProduct_jointDirections
    (hU : IsOpen U) (a f : E → ℕ → ℝ → ℝ) (n : ℕ)
    (Ja : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => a p.1 j p.2))
    (Jf : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => f p.1 j p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => n06RootJetProduct (a p.1) (f p.1) n p.2) := by
  let Jderiv (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => deriv (f p.1 j) p.2) :=
    (smoothDirections_angularIterate (Jf j hj) 1).congr
      (fun _ _ => by simp only [iteratedDeriv_one])
  let Jterm (j : Fin (n + 1)) : SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => (n.choose j : ℝ) * a p.1 j p.2 *
        deriv (f p.1 (n - j)) p.2) :=
    smoothDirections_realMul
      (smoothDirections_realConstMul (n.choose j : ℝ)
        (Ja j (Nat.le_of_lt_succ j.isLt)))
      (Jderiv (n - j) (Nat.sub_le _ _))
  apply (smoothDirections_finiteSum (hU.prod isOpen_univ) Jterm).congr
  intro p _
  exact Fin.sum_univ_eq_sum_range
    (fun j => (n.choose j : ℝ) * a p.1 j p.2 * deriv (f p.1 (n - j)) p.2) (n + 1)

/-- Actual even and divided-odd root traces have genuine joint towers at
every radial order. The hypotheses only differentiate the raw drift,
speed and label; they do not differentiate the selected root solution. -/
theorem n04PositiveGeometry_rootBoundary_jointDirections_nonempty
    (hU : IsOpen U)
    (d c : E → PolarPoint → ℝ) (β : E → ℝ → ℝ)
    (Φ : E → ℝ → ℝ → ℝ) (R σ : E → ℝ) (G : E → ℝ × ℝ × ℝ → ℝ)
    (hroot : ∀ x ∈ U, N04bRootCoordinateProperties
      (d x) (c x) (β x) (Φ x) (R x) (σ x) (G x))
    (hd : ∀ x ∈ U, ContDiff ℝ ∞ (d x))
    (hc : ∀ x ∈ U, ContDiff ℝ ∞ (c x))
    (Jd : ∀ j, SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (d p.1) 0 j p.2))
    (Jc : ∀ j, SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (c p.1) 0 j p.2))
    (Jβ : SmoothDirections (U ×ˢ univ) (fun p : E × ℝ => β p.1 p.2)) :
    ∀ n, Nonempty (SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 n p.2)) ∧
      Nonempty (SmoothDirections (U ×ˢ univ)
        (fun p : E × ℝ => radialBoundaryJet (extendedRootOddCoefficient (G p.1))
          0 n p.2)) := by
  classical
  let A : E → ℕ → ℝ → ℝ := fun x => radialBoundaryJet (d x) 0
  let B : E → ℕ → ℝ → ℝ := fun x => radialBoundaryJet (c x) 0
  let F : E → ℕ → ℝ → ℝ := fun x => radialBoundaryJet (extendedRootEven (G x)) 0
  let H : E → ℕ → ℝ → ℝ := fun x =>
    radialBoundaryJet (extendedRootOddCoefficient (G x)) 0
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          let JE : SmoothDirections (U ×ˢ univ)
              (fun p : E × ℝ => F p.1 0 p.2) :=
            Jβ.congr (fun p hp => (hroot p.1 hp.1).n06_even_boundary_jet_zero p.2 |>.symm)
          let Jβ' : SmoothDirections (U ×ˢ univ)
              (fun p : E × ℝ => deriv (β p.1) p.2) :=
            (smoothDirections_angularIterate Jβ 1).congr
              (fun _ _ => by simp only [iteratedDeriv_one])
          let JO := smoothDirections_realMul
            (smoothDirections_realConstMul (2 / 3 : ℝ) (Jc 0)) Jβ'
          refine ⟨⟨JE⟩, ⟨JO.congr ?_⟩⟩
          intro p hp
          exact ((hroot p.1 hp.1).n06_odd_boundary_jet_zero p.2).symm
      | succ n =>
          let JFlo (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
              (fun p : E × ℝ => F p.1 j p.2) :=
            Classical.choice (ih j (by omega)).1
          let JHlo (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
              (fun p : E × ℝ => H p.1 j p.2) :=
            Classical.choice (ih j (by omega)).2
          let JAF := n04PositiveGeometry_rootJetProduct_jointDirections hU A F n
            (fun j _ => Jd j) JFlo
          let JBH := n04PositiveGeometry_rootJetProduct_jointDirections hU B H (n - 2)
            (fun j _ => Jc j) (fun j hj => JHlo j (hj.trans (Nat.sub_le _ _)))
          let JE : SmoothDirections (U ×ˢ univ)
              (fun p : E × ℝ => F p.1 (n + 1) p.2) := by
            apply (smoothDirectionsAdd
              (smoothDirections_realConstMul (-1 : ℝ) JAF)
              (smoothDirections_realConstMul ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) JBH)).congr
            intro p hp
            simpa only [neg_one_mul] using
              ((hroot p.1 hp.1).n06_even_boundary_recursion
                (hd p.1 hp.1) (hc p.1 hp.1) n p.2).symm
          let JF (j : ℕ) (hj : j ≤ n + 1) : SmoothDirections (U ×ˢ univ)
              (fun p : E × ℝ => F p.1 j p.2) := by
            by_cases he : j = n + 1
            · subst j
              exact JE
            · exact JFlo j (by omega)
          let JBF := n04PositiveGeometry_rootJetProduct_jointDirections hU B F (n + 1)
            (fun j _ => Jc j) JF
          let JAH := n04PositiveGeometry_rootJetProduct_jointDirections hU A H n
            (fun j _ => Jd j) JHlo
          let JO : SmoothDirections (U ×ˢ univ)
              (fun p : E × ℝ => H p.1 (n + 1) p.2) := by
            apply (smoothDirections_realConstMul
              (((n + 1 : ℕ) : ℝ) + (3 : ℝ) / 2)⁻¹
              (smoothDirectionsAdd JBF
                (smoothDirections_realConstMul (-((n + 1 : ℕ) : ℝ)) JAH))).congr
            intro p hp
            have he := ((hroot p.1 hp.1).n06_odd_boundary_recursion_solved
              (hd p.1 hp.1) (hc p.1 hp.1) (n + 1) p.2).symm
            simpa only [Nat.add_sub_cancel, div_eq_mul_inv, sub_eq_add_neg,
              neg_mul, mul_comm] using he
          exact ⟨⟨JE⟩, ⟨JO⟩⟩

/-- The selected objects are proofs of regularity of the original two
trace functions. They do not select new root coordinates or a new domain. -/
def n04PositiveGeometry_rootBoundary_jointDirections
    (hU : IsOpen U)
    (d c : E → PolarPoint → ℝ) (β : E → ℝ → ℝ)
    (Φ : E → ℝ → ℝ → ℝ) (R σ : E → ℝ) (G : E → ℝ × ℝ × ℝ → ℝ)
    (hroot : ∀ x ∈ U, N04bRootCoordinateProperties
      (d x) (c x) (β x) (Φ x) (R x) (σ x) (G x))
    (hd : ∀ x ∈ U, ContDiff ℝ ∞ (d x))
    (hc : ∀ x ∈ U, ContDiff ℝ ∞ (c x))
    (Jd : ∀ j, SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (d p.1) 0 j p.2))
    (Jc : ∀ j, SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (c p.1) 0 j p.2))
    (Jβ : SmoothDirections (U ×ˢ univ) (fun p : E × ℝ => β p.1 p.2))
    (n : ℕ) :
    (SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 n p.2)) ×
      SmoothDirections (U ×ˢ univ)
        (fun p : E × ℝ => radialBoundaryJet (extendedRootOddCoefficient (G p.1))
          0 n p.2) :=
  let H := n04PositiveGeometry_rootBoundary_jointDirections_nonempty hU d c β
    Φ R σ G hroot hd hc Jd Jc Jβ n
  ⟨Classical.choice H.1, Classical.choice H.2⟩

end ContinuousFlexibility.Analysis
