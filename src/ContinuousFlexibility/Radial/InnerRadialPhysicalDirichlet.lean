module

public import ContinuousFlexibility.Radial.InnerRadialPhysicalPoisson

/-!
# Continuity of the same physical Dirichlet realization

Strictly ordered consecutive pieces are disjoint. Their actual H¹
values have the corresponding supports, so the Hilbert norm of a
realized field is the sum of the local squared norms, with the scalar
in the central piece only.

Local squared Dirichlet estimates and physical Bessel restriction then
make the canonical actual Dirichlet map continuous with the same bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped InnerProductSpace BigOperators

theorem innerRadialChainPieces_disjoint (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) :
    Pairwise (fun p k : Fin (n + 1) =>
      Disjoint (Ioo (G.left p) (G.right p)) (Ioo (G.left k) (G.right k))) := by
  intro p k hpk
  apply Set.disjoint_left.mpr
  intro r hp hk
  rcases lt_or_gt_of_ne hpk with hlt | hgt
  · have hsep : G.right p ≤ G.left k :=
      G.increasing.monotone (show p.succ ≤ k.castSucc by
        simpa only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] using
          Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hlt))
    exact (not_lt_of_ge hsep) (hk.1.trans hp.2)
  · have hsep : G.right k ≤ G.left p :=
      G.increasing.monotone (show k.succ ≤ p.castSucc by
        simpa only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] using
          Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hgt))
    exact (not_lt_of_ge hsep) (hp.1.trans hk.2)

section ActualNorm

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered
local notation "W" =>
  InnerRadialDomain D hw G forcing rowSource bordered j central column
local notation "realize" =>
  innerRadialPhysicalRealization D G hw bordered j central column

/-- Exact physical orthogonality, including the one central scalar. -/
theorem innerRadialPhysicalRealization_norm_sq (x : W) :
    ‖realize x‖ ^ 2 =
      ∑ p, ‖innerBorderPiece central (fun k => (x.val.1.1 k).1)
        x.val.1.2.2 p‖ ^ 2 := by
  have hx := (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j
    central column x.val).mp x.property
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G x.val.1.1).mp hx.1
  have hs (p : Fin (n + 1)) :
      ∀ᵐ r ∂radialHilbertMeasure D,
        r ∉ Ioo (G.left p) (G.right p) → (x.val.1.1 p).1 r = 0 :=
    innerRadialH1Domain_supported D hw (G.left_pos p) (G.in_core p)
      (G.weight_pos p) (hξ p).1
  have hnorm := (innerRadialPhysicalInclusion D G bordered).norm_map (realize x)
  rw [innerRadialPhysicalInclusion_apply, innerRadialPhysicalRealization_apply] at hnorm
  rw [← hnorm, innerBorderL2_norm_sq,
    innerL2_disjoint_sum_norm_sq (fun p => Ioo (G.left p) (G.right p))
      (innerRadialChainPieces_disjoint D G) (fun p => (x.val.1.1 p).1) hs]
  simp only [innerBorderPiece, innerBorderL2_norm_sq]
  rw [Finset.sum_add_distrib]
  congr 1
  symm
  rw [Finset.sum_eq_single central]
  · simp only [eq_self_iff_true, ite_true]
  · intro p _ hp
    simp only [if_neg hp, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  · intro hc
    exact (hc (Finset.mem_univ central)).elim

variable
  (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
  (hex : ∀ (F : InnerRadialPhysicalSource D G bordered)
    (ξ : EuclideanSpace ℝ (Fin n)) (p : Fin (n + 1)), Nonempty
      (InnerRadialPieceSolution D hw G
        (innerRadialPhysicalForcing D G bordered) (innerRadialPhysicalRowLinear D G bordered)
        bordered j central column F ξ p))

local notation "Dir" =>
  innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
    hunique hex
local notation "Dphys" =>
  innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex

/-- The bound comes from the actual local outputs and the true source
projections, not from a global continuity or inverse assumption. -/
theorem innerRadialPhysicalDirichlet_norm_le (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ (F : H) (p : Fin (n + 1)),
      ‖innerBorderPiece central (fun k => ((Dir F).val.1.1 k).1)
        (Dir F).val.1.2.2 p‖ ^ 2 ≤
      K ^ 2 * ‖innerBorderPieceProjection (radialHilbertMeasure D)
        (fun k => Ioo (G.left k) (G.right k)) central p F.val‖ ^ 2)
    (F : H) : ‖Dphys F‖ ≤ K * ‖F‖ := by
  have hF := (innerRadialPhysicalInclusion D G bordered).norm_map F
  rw [innerRadialPhysicalInclusion_apply] at hF
  have hsq : ‖Dphys F‖ ^ 2 ≤ (K * ‖F‖) ^ 2 := by
    calc
      _ = ∑ p, ‖innerBorderPiece central (fun k => ((Dir F).val.1.1 k).1)
          (Dir F).val.1.2.2 p‖ ^ 2 := by
        rw [innerRadialPhysicalDirichlet, LinearMap.comp_apply,
          innerRadialPhysicalRealization_norm_sq]
      _ ≤ ∑ p, K ^ 2 * ‖innerBorderPieceProjection (radialHilbertMeasure D)
          (fun k => Ioo (G.left k) (G.right k)) central p F.val‖ ^ 2 :=
        Finset.sum_le_sum (fun p _ => hlocal F p)
      _ = K ^ 2 * ∑ p, ‖innerBorderPieceProjection (radialHilbertMeasure D)
          (fun k => Ioo (G.left k) (G.right k)) central p F.val‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ K ^ 2 * ‖F.val‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (innerBorderPieceProjections_bessel (radialHilbertMeasure D)
            (fun k => Ioo (G.left k) (G.right k)) central
            (fun _ => measurableSet_Ioo) (innerRadialChainPieces_disjoint D G) F.val)
          (sq_nonneg K)
      _ = (K * ‖F‖) ^ 2 := by rw [hF, mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg F))).mp hsq

/-- The bounded operator is the same canonical physical Dirichlet map. -/
def innerRadialPhysicalDirichletCLM (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ (F : H) (p : Fin (n + 1)),
      ‖innerBorderPiece central (fun k => ((Dir F).val.1.1 k).1)
        (Dir F).val.1.2.2 p‖ ^ 2 ≤
      K ^ 2 * ‖innerBorderPieceProjection (radialHilbertMeasure D)
        (fun k => Ioo (G.left k) (G.right k)) central p F.val‖ ^ 2) :
    H →L[ℝ] H :=
  (Dphys).mkContinuous K
    (innerRadialPhysicalDirichlet_norm_le D hw G bordered j central column
      hunique hex K hK hlocal)

@[simp] theorem innerRadialPhysicalDirichletCLM_apply
    (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ (F : H) (p : Fin (n + 1)),
      ‖innerBorderPiece central (fun k => ((Dir F).val.1.1 k).1)
        (Dir F).val.1.2.2 p‖ ^ 2 ≤
      K ^ 2 * ‖innerBorderPieceProjection (radialHilbertMeasure D)
        (fun k => Ioo (G.left k) (G.right k)) central p F.val‖ ^ 2)
    (F : H) :
    innerRadialPhysicalDirichletCLM D hw G bordered j central column hunique hex
      K hK hlocal F = Dphys F := by
  simp only [innerRadialPhysicalDirichletCLM, LinearMap.mkContinuous_apply]

theorem norm_innerRadialPhysicalDirichletCLM_le
    (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ (F : H) (p : Fin (n + 1)),
      ‖innerBorderPiece central (fun k => ((Dir F).val.1.1 k).1)
        (Dir F).val.1.2.2 p‖ ^ 2 ≤
      K ^ 2 * ‖innerBorderPieceProjection (radialHilbertMeasure D)
        (fun k => Ioo (G.left k) (G.right k)) central p F.val‖ ^ 2) :
    ‖innerRadialPhysicalDirichletCLM D hw G bordered j central column hunique hex
      K hK hlocal‖ ≤ K :=
  LinearMap.mkContinuous_norm_le Dphys hK
    (innerRadialPhysicalDirichlet_norm_le D hw G bordered j central column
      hunique hex K hK hlocal)

/-- An actual ambient finite block operator transfers its bound to the
same supported Dirichlet map once their physical fields are identified. -/
theorem innerRadialPhysicalDirichlet_norm_le_ambient
    (A : InnerBorderL2 (radialHilbertMeasure D) →L[ℝ]
      InnerBorderL2 (radialHilbertMeasure D))
    (hA : ∀ F : H, A F.val = (Dphys F).val) (F : H) :
    ‖Dphys F‖ ≤ ‖A‖ * ‖F‖ := by
  have hD := (innerRadialPhysicalInclusion D G bordered).norm_map (Dphys F)
  have hF := (innerRadialPhysicalInclusion D G bordered).norm_map F
  rw [innerRadialPhysicalInclusion_apply] at hD hF
  calc
    _ = ‖(Dphys F).val‖ := hD.symm
    _ = ‖A F.val‖ := by rw [hA]
    _ ≤ ‖A‖ * ‖F.val‖ := A.le_opNorm F.val
    _ = ‖A‖ * ‖F‖ := by rw [hF]

/-- This restriction uses the same actual field identity, so the
ambient finite Dirichlet sum supplies a concrete canonical CLM. -/
def innerRadialPhysicalDirichletCLMOfAmbient
    (A : InnerBorderL2 (radialHilbertMeasure D) →L[ℝ]
      InnerBorderL2 (radialHilbertMeasure D))
    (hA : ∀ F : H, A F.val = (Dphys F).val) : H →L[ℝ] H :=
  (Dphys).mkContinuous ‖A‖
    (innerRadialPhysicalDirichlet_norm_le_ambient D hw G bordered j central column
      hunique hex A hA)

@[simp] theorem innerRadialPhysicalDirichletCLMOfAmbient_apply
    (A : InnerBorderL2 (radialHilbertMeasure D) →L[ℝ]
      InnerBorderL2 (radialHilbertMeasure D))
    (hA : ∀ F : H, A F.val = (Dphys F).val) (F : H) :
    innerRadialPhysicalDirichletCLMOfAmbient D hw G bordered j central column
      hunique hex A hA F = Dphys F := by
  simp only [innerRadialPhysicalDirichletCLMOfAmbient, LinearMap.mkContinuous_apply]

theorem norm_innerRadialPhysicalDirichletCLMOfAmbient_le
    (A : InnerBorderL2 (radialHilbertMeasure D) →L[ℝ]
      InnerBorderL2 (radialHilbertMeasure D))
    (hA : ∀ F : H, A F.val = (Dphys F).val) :
    ‖innerRadialPhysicalDirichletCLMOfAmbient D hw G bordered j central column
      hunique hex A hA‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le Dphys (norm_nonneg A)
    (innerRadialPhysicalDirichlet_norm_le_ambient D hw G bordered j central column
      hunique hex A hA)

end ActualNorm

end ContinuousFlexibility.Radial
