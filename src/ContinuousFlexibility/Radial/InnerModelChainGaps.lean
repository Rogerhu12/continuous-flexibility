import ContinuousFlexibility.Radial.InnerModelChainGeometry

/-!
# Gap indices and adjacency in the flattened physical chain

Models are the odd pieces and gaps are the even pieces. These formulas
identify both cut incidences and the terminal half-gaps without adding
extra boundary variables or assuming a pre-existing piece partition.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

def innerModelChainGap {m : ℕ} (g : Fin (m + 1)) : Fin (2 * m + 1) :=
  ⟨2 * g.val, by omega⟩

theorem innerModelChainGap_injective {m : ℕ} :
    Function.Injective (@innerModelChainGap m) := by
  intro g h hgh
  have hv := congrArg Fin.val hgh
  dsimp only [innerModelChainGap] at hv
  apply Fin.ext
  omega

theorem innerModelChainGap_ne_model {m : ℕ} (g : Fin (m + 1)) (p : Fin m) :
    innerModelChainGap g ≠ innerModelChainPiece p := by
  intro he
  have hv := congrArg Fin.val he
  dsimp only [innerModelChainGap, innerModelChainPiece] at hv
  omega

/-- Every physical piece has precisely one of the two actual index forms. -/
theorem innerModelChainPiece_or_gap {m : ℕ} (p : Fin (2 * m + 1)) :
    (∃ q : Fin m, p = innerModelChainPiece q) ∨
      ∃ g : Fin (m + 1), p = innerModelChainGap g := by
  by_cases he : p.val % 2 = 0
  · right
    refine ⟨⟨p.val / 2, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp only [innerModelChainGap]
    omega
  · left
    refine ⟨⟨p.val / 2, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp only [innerModelChainPiece]
    omega

/-- The left cut of a model is the right cut of its preceding gap. -/
theorem innerModelChain_left_incidence {m : ℕ} (p : Fin m) :
    (innerModelChainPiece p).castSucc = (innerModelChainGap p.castSucc).succ := by
  apply Fin.ext
  simp only [innerModelChainPiece, innerModelChainGap, Fin.val_castSucc, Fin.val_succ]

/-- The right cut of a model is the left cut of its following gap. -/
theorem innerModelChain_right_incidence {m : ℕ} (p : Fin m) :
    (innerModelChainPiece p).succ = (innerModelChainGap p.succ).castSucc := by
  apply Fin.ext
  simp only [innerModelChainPiece, innerModelChainGap, Fin.val_castSucc, Fin.val_succ] <;> omega

theorem innerModelChainCuts_gap_left {m : ℕ} (M : Fin m → Fin 2 → ℝ)
    (L R : ℝ) (g : Fin (m + 1)) :
    innerModelChainCuts M L R (innerModelChainGap g).castSucc =
      if hg : 0 < g.val then M ⟨g.val - 1, by omega⟩ 1 else L := by
  by_cases hg : 0 < g.val
  · rw [dif_pos hg]
    have hi : (innerModelChainGap g).castSucc =
        (innerModelChainPiece (⟨g.val - 1, by omega⟩ : Fin m)).succ := by
      apply Fin.ext
      simp only [innerModelChainGap, innerModelChainPiece, Fin.val_castSucc, Fin.val_succ] <;> omega
    rw [hi, innerModelChainCuts_model_right]
  · rw [dif_neg hg]
    have hi : (innerModelChainGap g).castSucc = 0 := by
      apply Fin.ext
      simp only [innerModelChainGap, Fin.val_castSucc, Fin.val_zero] <;> omega
    rw [hi, innerModelChainCuts_first]

theorem innerModelChainCuts_gap_right {m : ℕ} (M : Fin m → Fin 2 → ℝ)
    (L R : ℝ) (g : Fin (m + 1)) :
    innerModelChainCuts M L R (innerModelChainGap g).succ =
      if hg : g.val < m then M ⟨g.val, hg⟩ 0 else R := by
  by_cases hg : g.val < m
  · rw [dif_pos hg]
    have hi : (innerModelChainGap g).succ =
        (innerModelChainPiece (⟨g.val, hg⟩ : Fin m)).castSucc := by
      apply Fin.ext
      simp only [innerModelChainGap, innerModelChainPiece, Fin.val_castSucc, Fin.val_succ]
    rw [hi, innerModelChainCuts_model_left]
  · rw [dif_neg hg]
    have hi : (innerModelChainGap g).succ = Fin.last (2 * m + 1) := by
      apply Fin.ext
      simp only [innerModelChainGap, Fin.val_succ, Fin.val_last] <;> omega
    rw [hi, innerModelChainCuts_last]

section ModelChain

variable (D : ReferenceData) (hD : RadialProfileGeometry D)
  {m : ℕ} (M : Fin m → Fin 2 → ℝ) (L R : ℝ)
  (hL : L ∈ radialCore D) (hR : R ∈ radialCore D)
  (hLR : L < R) (hmodel : ∀ p, M p 0 < M p 1)
  (hsep : ∀ p q, p < q → M p 1 < M q 0)
  (hleft : ∀ p, L < M p 0) (hright : ∀ p, M p 1 < R)

theorem innerRadialChainOfModels_gap_left (g : Fin (m + 1)) :
    (innerRadialChainOfModels D hD M L R hL hR hLR hmodel hsep hleft hright).left
      (innerModelChainGap g) =
        if hg : 0 < g.val then M ⟨g.val - 1, by omega⟩ 1 else L :=
  innerModelChainCuts_gap_left M L R g

theorem innerRadialChainOfModels_gap_right (g : Fin (m + 1)) :
    (innerRadialChainOfModels D hD M L R hL hR hLR hmodel hsep hleft hright).right
      (innerModelChainGap g) =
        if hg : g.val < m then M ⟨g.val, hg⟩ 0 else R :=
  innerModelChainCuts_gap_right M L R g

end ModelChain

end ContinuousFlexibility.Radial
