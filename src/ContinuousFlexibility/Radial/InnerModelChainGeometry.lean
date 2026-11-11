import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph
import Mathlib.Order.Fin.Tuple

/-!
# A finite physical chain from ordered model cut pairs

Each model contributes its actual two cuts. Flattening these pairs and
adjoining the two outer boundary points gives all pieces, with the model
pieces at odd indices and the gaps at even indices. The physical core
and weight conditions follow from the original profile geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

def innerFlattenModelCuts {m : ℕ} (M : Fin m → Fin 2 → ℝ) (i : Fin (2 * m)) : ℝ :=
  M ⟨i.val / 2, by omega⟩ ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩

theorem innerFlattenModelCuts_apply {m : ℕ} (M : Fin m → Fin 2 → ℝ)
    (p : Fin m) (i : Fin 2) :
    innerFlattenModelCuts M ⟨2 * p.val + i.val, by omega⟩ = M p i := by
  have hdiv : (2 * p.val + i.val) / 2 = p.val := by omega
  have hmod : (2 * p.val + i.val) % 2 = i.val := by omega
  exact congrArg₂ M (Fin.ext hdiv) (Fin.ext hmod)

private theorem innerModelCut_left_le {m : ℕ} {M : Fin m → Fin 2 → ℝ}
    (hmodel : ∀ p, M p 0 < M p 1) (p : Fin m) (i : Fin 2) : M p 0 ≤ M p i := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact le_rfl
  · exact (hmodel p).le

private theorem innerModelCut_le_right {m : ℕ} {M : Fin m → Fin 2 → ℝ}
    (hmodel : ∀ p, M p 0 < M p 1) (p : Fin m) (i : Fin 2) : M p i ≤ M p 1 := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact (hmodel p).le
  · exact le_rfl

theorem innerFlattenModelCuts_strictMono {m : ℕ} {M : Fin m → Fin 2 → ℝ}
    (hmodel : ∀ p, M p 0 < M p 1)
    (hsep : ∀ p q, p < q → M p 1 < M q 0) : StrictMono (innerFlattenModelCuts M) := by
  intro a b hab
  have hle : a.val / 2 ≤ b.val / 2 := by omega
  by_cases heq : a.val / 2 = b.val / 2
  · have ha : a.val % 2 = 0 := by omega
    have hb : b.val % 2 = 1 := by omega
    simpa only [innerFlattenModelCuts, heq, ha, hb] using
      hmodel ⟨b.val / 2, by omega⟩
  · have hlt : a.val / 2 < b.val / 2 := lt_of_le_of_ne hle heq
    exact (innerModelCut_le_right hmodel _ _).trans_lt
      ((hsep ⟨a.val / 2, by omega⟩ ⟨b.val / 2, by omega⟩ hlt).trans_le
        (innerModelCut_left_le hmodel _ _))

def innerModelChainCuts {m : ℕ} (M : Fin m → Fin 2 → ℝ) (L R : ℝ) :
    Fin (2 * m + 2) → ℝ :=
  Fin.cons L (Fin.snoc (innerFlattenModelCuts M) R)

@[simp] theorem innerModelChainCuts_first {m : ℕ} (M : Fin m → Fin 2 → ℝ) (L R : ℝ) :
    innerModelChainCuts M L R 0 = L := Fin.cons_zero _ _

@[simp] theorem innerModelChainCuts_last {m : ℕ} (M : Fin m → Fin 2 → ℝ) (L R : ℝ) :
    innerModelChainCuts M L R (Fin.last (2 * m + 1)) = R := by
  rw [innerModelChainCuts, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

theorem innerModelChainCuts_strictMono {m : ℕ} {M : Fin m → Fin 2 → ℝ} {L R : ℝ}
    (hLR : L < R) (hmodel : ∀ p, M p 0 < M p 1)
    (hsep : ∀ p q, p < q → M p 1 < M q 0)
    (hleft : ∀ p, L < M p 0) (hright : ∀ p, M p 1 < R) :
    StrictMono (innerModelChainCuts M L R) := by
  have hflat := innerFlattenModelCuts_strictMono hmodel hsep
  have hl (i : Fin (2 * m)) : L < innerFlattenModelCuts M i :=
    (hleft _).trans_le (innerModelCut_left_le hmodel _ _)
  have hr (i : Fin (2 * m)) : innerFlattenModelCuts M i < R :=
    (innerModelCut_le_right hmodel _ _).trans_lt (hright _)
  have hsnoc : StrictMono (Fin.snoc (innerFlattenModelCuts M) R) := by
    intro i j hij
    cases i using Fin.lastCases
    · exact ((not_lt_of_ge (Fin.le_last j)) hij).elim
    · rename_i i
      cases j using Fin.lastCases
      · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hr i
      · rename_i j
        simpa only [Fin.snoc_castSucc] using hflat (show i < j from hij)
  apply Fin.strictMono_cons.mpr
  refine ⟨?_, hsnoc⟩
  intro i
  cases i using Fin.lastCases
  · simpa only [Fin.snoc_last] using hLR
  · rename_i i
    simpa only [Fin.snoc_castSucc] using hl i

/-- An actual model occupies the odd piece between its two flattened cuts. -/
def innerModelChainPiece {m : ℕ} (p : Fin m) : Fin (2 * m + 1) :=
  ⟨2 * p.val + 1, by omega⟩

theorem innerModelChainPiece_injective {m : ℕ} :
    Function.Injective (@innerModelChainPiece m) := by
  intro p q hpq
  have hv := congrArg Fin.val hpq
  dsimp only [innerModelChainPiece] at hv
  apply Fin.ext
  omega

theorem innerModelChainCuts_model_left {m : ℕ} (M : Fin m → Fin 2 → ℝ)
    (L R : ℝ) (p : Fin m) :
    innerModelChainCuts M L R (innerModelChainPiece p).castSucc = M p 0 := by
  have hi : (innerModelChainPiece p).castSucc =
      (⟨2 * p.val + (0 : Fin 2).val, by omega⟩ : Fin (2 * m)).castSucc.succ := by
    apply Fin.ext
    simp only [innerModelChainPiece, Fin.val_castSucc, Fin.val_succ, Fin.val_zero] <;> omega
  rw [hi, innerModelChainCuts, Fin.cons_succ, Fin.snoc_castSucc,
    innerFlattenModelCuts_apply]

theorem innerModelChainCuts_model_right {m : ℕ} (M : Fin m → Fin 2 → ℝ)
    (L R : ℝ) (p : Fin m) :
    innerModelChainCuts M L R (innerModelChainPiece p).succ = M p 1 := by
  have hi : (innerModelChainPiece p).succ =
      (⟨2 * p.val + (1 : Fin 2).val, by omega⟩ : Fin (2 * m)).castSucc.succ := by
    apply Fin.ext
    simp only [innerModelChainPiece, Fin.val_castSucc, Fin.val_succ, Fin.val_one]
  rw [hi, innerModelChainCuts, Fin.cons_succ, Fin.snoc_castSucc,
    innerFlattenModelCuts_apply]

/-- Build the common physical chain from actual ordered cut pairs and
the two outer points. There is no supplied chain geometry in the input. -/
def innerRadialChainOfModels (D : ReferenceData) (hD : RadialProfileGeometry D)
    {m : ℕ} (M : Fin m → Fin 2 → ℝ) (L R : ℝ)
    (hL : L ∈ radialCore D) (hR : R ∈ radialCore D)
    (hLR : L < R) (hmodel : ∀ p, M p 0 < M p 1)
    (hsep : ∀ p q, p < q → M p 1 < M q 0)
    (hleft : ∀ p, L < M p 0) (hright : ∀ p, M p 1 < R) :
    InnerRadialChainGeometry D (2 * m) := by
  let cuts := innerModelChainCuts M L R
  have hinc : StrictMono cuts := innerModelChainCuts_strictMono hLR hmodel hsep hleft hright
  have hc (i : Fin (2 * m + 2)) : cuts i ∈ radialCore D := by
    have hl := hinc.monotone (Fin.zero_le i)
    have hr := hinc.monotone (Fin.le_last i)
    dsimp only [cuts] at hl hr
    rw [innerModelChainCuts_first] at hl
    rw [innerModelChainCuts_last] at hr
    exact ⟨hL.1.trans_le hl, hr.trans_lt hR.2⟩
  refine ⟨cuts, hinc, (fun p => hD.1.trans (hc p.castSucc).1), ?_, ?_⟩
  · intro p r hr
    exact ⟨(hc p.castSucc).1.trans hr.1, hr.2.trans (hc p.succ).2⟩
  · intro p r hr
    exact hD.2.2.2.2.1 r
      ⟨(hc p.castSucc).1.trans_le hr.1, hr.2.trans_lt (hc p.succ).2⟩

section ModelPieces

variable (D : ReferenceData) (hD : RadialProfileGeometry D)
  {m : ℕ} (M : Fin m → Fin 2 → ℝ) (L R : ℝ)
  (hL : L ∈ radialCore D) (hR : R ∈ radialCore D)
  (hLR : L < R) (hmodel : ∀ p, M p 0 < M p 1)
  (hsep : ∀ p q, p < q → M p 1 < M q 0)
  (hleft : ∀ p, L < M p 0) (hright : ∀ p, M p 1 < R)

theorem innerRadialChainOfModels_left (p : Fin m) :
    (innerRadialChainOfModels D hD M L R hL hR hLR hmodel hsep hleft hright).left
      (innerModelChainPiece p) = M p 0 :=
  innerModelChainCuts_model_left M L R p

theorem innerRadialChainOfModels_right (p : Fin m) :
    (innerRadialChainOfModels D hD M L R hL hR hLR hmodel hsep hleft hright).right
      (innerModelChainPiece p) = M p 1 :=
  innerModelChainCuts_model_right M L R p

end ModelPieces

end ContinuousFlexibility.Radial
