import ContinuousFlexibility.Radial.InnerRadialActualAssembly
import ContinuousFlexibility.Radial.InnerRadialReferenceAssembly
import ContinuousFlexibility.Radial.InnerModelChainGaps

/-!
# The exact actual dictionary on an alternating model-gap chain

The two disjoint index families cover every physical piece. The
dependent selector retains their original values exactly, so the
assembled chain uses the same local models and the same actual gap
columns. Its interpolation walls are the physical images of the
original buffer walls on models and the true endpoints on gaps.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

section DisjointCover

variable {I A B : Type*} {β : I → Type*}
  (f : A → I) (g : B → I) (hf : Function.Injective f) (hg : Function.Injective g)
  (hdisjoint : ∀ a b, f a ≠ g b)
  (hcover : ∀ i, (∃ a, i = f a) ∨ ∃ b, i = g b)
  (left : ∀ a, β (f a)) (right : ∀ b, β (g b))

include hf hg hdisjoint hcover in
private theorem innerCover_value_exists (i : I) :
    ∃ v : β i, (∀ a, i = f a → HEq v (left a)) ∧
      ∀ b, i = g b → HEq v (right b) := by
  rcases hcover i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · refine ⟨left a, ?_, ?_⟩
    · intro a' ha
      have he : a = a' := hf ha
      subst a'
      rfl
    · intro b hb
      exact (hdisjoint a b hb).elim
  · refine ⟨right b, ?_, ?_⟩
    · intro a ha
      exact (hdisjoint a b ha.symm).elim
    · intro b' hb
      have he : b = b' := hg hb
      subst b'
      rfl

/-- Dependent assembly along two disjoint injective index families.
Both branch application lemmas are exact equalities. -/
def innerDisjointCoverElim (i : I) : β i :=
  Classical.choose (innerCover_value_exists f g hf hg hdisjoint hcover left right i)

theorem innerDisjointCoverElim_left (a : A) :
    innerDisjointCoverElim f g hf hg hdisjoint hcover left right (f a) = left a :=
  eq_of_heq ((Classical.choose_spec
    (innerCover_value_exists f g hf hg hdisjoint hcover left right (f a))).1 a rfl)

theorem innerDisjointCoverElim_right (b : B) :
    innerDisjointCoverElim f g hf hg hdisjoint hcover left right (g b) = right b :=
  eq_of_heq ((Classical.choose_spec
    (innerCover_value_exists f g hf hg hdisjoint hcover left right (g b))).2 b rfl)

end DisjointCover

section AlternatingChain

variable {D : ReferenceData} {m : ℕ} (G : InnerRadialChainGeometry D (2 * m))
  (bordered : Bool) (j : ℝ) (center : Fin m) (column : RadialModeL2 D)
  (models : ∀ p : Fin m, InnerRadialModelChart D G bordered j
    (innerModelChainPiece center) column (innerModelChainPiece p))
  (gaps : ∀ g : Fin (m + 1), InnerRadialGapChart D G j
    (innerModelChainPiece center) (innerModelChainGap g))

def innerActualChainOfModelsAndGaps :
    InnerRadialActualChain D G bordered j (innerModelChainPiece center) column where
  piece := innerDisjointCoverElim innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (fun p => Sum.inl (models p)) (fun g => Sum.inr (gaps g))

theorem innerActualChainOfModelsAndGaps_model (p : Fin m) :
    (innerActualChainOfModelsAndGaps G bordered j center column models gaps).piece
        (innerModelChainPiece p) = Sum.inl (models p) :=
  innerDisjointCoverElim_left
    (β := fun q => InnerRadialActualPiece D G bordered j (innerModelChainPiece center) column q)
    innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (fun p => Sum.inl (models p)) (fun g => Sum.inr (gaps g)) p

theorem innerActualChainOfModelsAndGaps_gap (g : Fin (m + 1)) :
    (innerActualChainOfModelsAndGaps G bordered j center column models gaps).piece
        (innerModelChainGap g) = Sum.inr (gaps g) :=
  innerDisjointCoverElim_right
    (β := fun q => InnerRadialActualPiece D G bordered j (innerModelChainPiece center) column q)
    innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (fun p => Sum.inl (models p)) (fun g => Sum.inr (gaps g)) g

/-- Every internal cut lies between one model and one gap, with the
original two endpoint conventions. -/
theorem innerModelChain_cut_incidence (i : Fin (2 * m)) :
    ∃ p : Fin m,
      (i.castSucc = innerModelChainGap p.castSucc ∧ i.succ = innerModelChainPiece p) ∨
      (i.castSucc = innerModelChainPiece p ∧ i.succ = innerModelChainGap p.succ) := by
  let p : Fin m := ⟨i.val / 2, by omega⟩
  refine ⟨p, ?_⟩
  by_cases he : i.val % 2 = 0
  · left
    constructor <;> apply Fin.ext <;>
      simp only [innerModelChainGap, innerModelChainPiece, Fin.val_castSucc, Fin.val_succ, p] <;>
      omega
  · right
    constructor <;> apply Fin.ext <;>
      simp only [innerModelChainGap, innerModelChainPiece, Fin.val_castSucc, Fin.val_succ, p] <;>
      omega

theorem innerActualChainOfModelsAndGaps_kappa_separated (i : Fin (2 * m)) :
    ((innerActualChainOfModelsAndGaps G bordered j center column models gaps).piece
        i.castSucc).kappa 1 = 0 ∨
      ((innerActualChainOfModelsAndGaps G bordered j center column models gaps).piece
        i.succ).kappa 0 = 0 := by
  obtain ⟨p, h | h⟩ := innerModelChain_cut_incidence i
  · left
    rw [h.1, innerActualChainOfModelsAndGaps_gap]
    exact rfl
  · right
    rw [h.2, innerActualChainOfModelsAndGaps_gap]
    exact rfl

theorem innerActualChainOfModelsAndGaps_kappa_pos
    (hκ : ∀ p i, 0 < (models p).kappa i) (i : Fin (2 * m)) :
    0 < (innerActualChainOfModelsAndGaps G bordered j center column models gaps).kappa i := by
  rw [InnerRadialActualChain.kappa_apply]
  obtain ⟨p, h | h⟩ := innerModelChain_cut_incidence i
  · rw [h.1, h.2, innerActualChainOfModelsAndGaps_gap,
      innerActualChainOfModelsAndGaps_model]
    simpa only [InnerRadialActualPiece.kappa, Pi.zero_apply, zero_add] using hκ p 0
  · rw [h.1, h.2, innerActualChainOfModelsAndGaps_model,
      innerActualChainOfModelsAndGaps_gap]
    simpa only [InnerRadialActualPiece.kappa, Pi.zero_apply, add_zero] using hκ p 1

theorem innerActualChainOfModelsAndGaps_model_internal
    (hκ : ∀ p i, 0 < (models p).kappa i) (p : Fin (2 * m + 1))
    (M : InnerRadialModelChart D G bordered j (innerModelChainPiece center) column p)
    (hp : (innerActualChainOfModelsAndGaps G bordered j center column models gaps).piece p =
      Sum.inl M) : 0 < p.val ∧ p.val < 2 * m ∧ ∀ i, 0 < M.kappa i := by
  rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
  · rw [innerActualChainOfModelsAndGaps_model] at hp
    have he : models q = M := Sum.inl.inj hp
    subst M
    exact ⟨by dsimp only [innerModelChainPiece]; omega,
      by dsimp only [innerModelChainPiece]; omega, hκ q⟩
  · rw [innerActualChainOfModelsAndGaps_gap] at hp
    cases hp

end AlternatingChain

namespace InnerRadialModelChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  {piece : Fin (n + 1)} (A : InnerRadialModelChart D G bordered j central column piece)

def leftWall : ℝ := A.radius (bufferInnerWall A.buffer 0)

def rightWall : ℝ := A.radius (bufferInnerWall A.buffer 1)

theorem walls_inside :
    G.left piece < A.leftWall ∧ A.leftWall < A.rightWall ∧ A.rightWall < G.right piece := by
  have hw := innerBuffer_walls_inside A.buffer_hypotheses
  have hmono : StrictMonoOn A.radius (Icc A.buffer.l A.buffer.h) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) A.radius_smooth.continuous.continuousOn
      (fun x hx => (A.chart_pos x (interior_subset hx)).2.1)
  have hl : A.buffer.l ∈ Icc A.buffer.l A.buffer.h :=
    left_mem_Icc.mpr A.buffer_hypotheses.1.le
  have hr : A.buffer.h ∈ Icc A.buffer.l A.buffer.h :=
    right_mem_Icc.mpr A.buffer_hypotheses.1.le
  have hw0 : bufferInnerWall A.buffer 0 ∈ Icc A.buffer.l A.buffer.h :=
    ⟨hw.1.le, (hw.2.1.trans hw.2.2).le⟩
  have hw1 : bufferInnerWall A.buffer 1 ∈ Icc A.buffer.l A.buffer.h :=
    ⟨(hw.1.trans hw.2.1).le, hw.2.2.le⟩
  rw [A.left_eq, A.right_eq]
  exact ⟨hmono hl hw0 hw.1, hmono hw0 hw1 hw.2.1, hmono hw1 hr hw.2.2⟩

end InnerRadialModelChart

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

def leftWall (p : Fin (n + 1)) : ℝ :=
  match C.piece p with
  | .inl M => M.leftWall
  | .inr _ => G.left p

def rightWall (p : Fin (n + 1)) : ℝ :=
  match C.piece p with
  | .inl M => M.rightWall
  | .inr _ => G.right p

theorem leftWall_model {p : Fin (n + 1)}
    {M : InnerRadialModelChart D G bordered j central column p} (hp : C.piece p = Sum.inl M) :
    C.leftWall p = M.radius (bufferInnerWall M.buffer 0) := by
  simp only [leftWall, hp, InnerRadialModelChart.leftWall]

theorem rightWall_model {p : Fin (n + 1)}
    {M : InnerRadialModelChart D G bordered j central column p} (hp : C.piece p = Sum.inl M) :
    C.rightWall p = M.radius (bufferInnerWall M.buffer 1) := by
  simp only [rightWall, hp, InnerRadialModelChart.rightWall]

theorem leftWall_gap {p : Fin (n + 1)} {Q : InnerRadialGapChart D G j central p}
    (hp : C.piece p = Sum.inr Q) : C.leftWall p = G.left p := by
  simp only [leftWall, hp]

theorem rightWall_gap {p : Fin (n + 1)} {Q : InnerRadialGapChart D G j central p}
    (hp : C.piece p = Sum.inr Q) : C.rightWall p = G.right p := by
  simp only [rightWall, hp]

theorem walls_inside (p : Fin (n + 1)) :
    G.left p ≤ C.leftWall p ∧ C.leftWall p < C.rightWall p ∧ C.rightWall p ≤ G.right p := by
  cases hp : C.piece p with
  | inl M =>
    simpa only [leftWall, rightWall, hp] using
      And.intro M.walls_inside.1.le ⟨M.walls_inside.2.1, M.walls_inside.2.2.le⟩
  | inr Q =>
    simpa only [leftWall, rightWall, hp] using
      And.intro (le_refl (G.left p)) ⟨G.left_lt_right p, le_refl (G.right p)⟩

end InnerRadialActualChain

end ContinuousFlexibility.Radial
