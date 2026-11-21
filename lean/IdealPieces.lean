import Mathlib

/-!
# 定理3：K=4 の「理想ペア部品」は存在しない（補題3.1 の形式化）

arXiv:2610.41622（査読・検証中の主張）の注意2.9・2.5節・4.6節が未解決とした
「行の切断と列の切断で 1 ビットあたりのコストが (2,0) と (0,2) の部品の族」についての否定的な答え。

設定：4つの脚 x, y, u, v（セル 11, 12, 21, 22。各脚は有限集合 `α` の値、N = |α|）。
長方形の交差 `crossing x y u v = [x = v][y = u]`。
* 行の切断 S₁ = {x,y} | {u,v} での平坦化 `rowFlat`
* 列の切断 S₂ = {x,u} | {y,v} での平坦化 `colFlat`

主定理 `card_le_sum_min_rank`：`crossing = ∑ i ∈ s, π i` なら
  N ≤ ∑ i ∈ s, min (rank (rowFlat (π i))) (rank (colFlat (π i))).

証明は y = u = c と代入すること：`crossing` は (x,v) の単位行列になり、各部品の代入後の行列は
どちらの平坦化の部分行列にもなる。あとは階数の劣加法性と単位行列の階数。
-/

open Matrix Module

set_option linter.unusedSectionVars false

namespace IdealPieces

section RankLemmas

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

/-- 行列版の階数の劣加法性（Mathlib には線形写像版 `LinearMap.rank_add_le` しかないので自前で作る）。 -/
theorem matrix_rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [← finrank_range_mulVecLin, ← finrank_range_mulVecLin, ← finrank_range_mulVecLin,
    Matrix.mulVecLin_add]
  calc finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank K (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule K (m → K)) := by
        apply Submodule.finrank_mono
        rintro _ ⟨x, rfl⟩
        exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- 有限和の版。 -/
theorem matrix_rank_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix m n K) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

end RankLemmas

variable {K : Type*} [Field K] {α : Type*} [Fintype α] [DecidableEq α]

/-- 長方形の交差（2×2 格子の2本の対角辺）：`[x = v][y = u]`。 -/
def crossing (K : Type*) [Field K] (α : Type*) [DecidableEq α] : α → α → α → α → K :=
  fun x y u v => if x = v ∧ y = u then 1 else 0

/-- 行の切断 {x,y} | {u,v} での平坦化。 -/
def rowFlat (π : α → α → α → α → K) : Matrix (α × α) (α × α) K :=
  fun p q => π p.1 p.2 q.1 q.2

/-- 列の切断 {x,u} | {y,v} での平坦化（行 = (x,u)、列 = (y,v)）。 -/
def colFlat (π : α → α → α → α → K) : Matrix (α × α) (α × α) K :=
  fun p q => π p.1 q.1 p.2 q.2

/-- y = u = c と代入した (x,v) の行列。 -/
def restrictDiag (π : α → α → α → α → K) (c : α) : Matrix α α K :=
  fun x v => π x c c v

theorem restrictDiag_eq_row (π : α → α → α → α → K) (c : α) :
    restrictDiag π c = (rowFlat π).submatrix (fun x => (x, c)) (fun v => (c, v)) := rfl

theorem restrictDiag_eq_col (π : α → α → α → α → K) (c : α) :
    restrictDiag π c = (colFlat π).submatrix (fun x => (x, c)) (fun v => (c, v)) := rfl

/-- 代入後の行列の階数は、どちらの切断の階数でも上から抑えられる。 -/
theorem rank_restrictDiag_le_min (π : α → α → α → α → K) (c : α) :
    (restrictDiag π c).rank ≤ min (rowFlat π).rank (colFlat π).rank := by
  refine le_min ?_ ?_
  · rw [restrictDiag_eq_row]; exact rank_submatrix_le _ _ _
  · rw [restrictDiag_eq_col]; exact rank_submatrix_le _ _ _

/-- 交差に代入すると単位行列になる。 -/
theorem restrictDiag_crossing (c : α) : restrictDiag (crossing K α) c = 1 := by
  ext x v
  simp [restrictDiag, crossing, Matrix.one_apply]

/-- 代入は部品の和と交換する。 -/
theorem restrictDiag_sum {ι : Type*} (s : Finset ι) (π : ι → α → α → α → α → K) (c : α) :
    restrictDiag (∑ i ∈ s, π i) c = ∑ i ∈ s, restrictDiag (π i) c := by
  ext x v
  simp [restrictDiag, Finset.sum_apply, Matrix.sum_apply]

/-- **補題3.1.** 交差の任意の分解 `crossing = ∑ π i` について
`N ≤ ∑ min(行の切断での階数, 列の切断での階数)`。係数体は任意。 -/
theorem card_le_sum_min_rank {ι : Type*} (s : Finset ι) (π : ι → α → α → α → α → K)
    (h : ∑ i ∈ s, π i = crossing K α) (c : α) :
    Fintype.card α ≤ ∑ i ∈ s, min (rowFlat (π i)).rank (colFlat (π i)).rank := by
  calc Fintype.card α = (1 : Matrix α α K).rank := (rank_one).symm
    _ = (∑ i ∈ s, restrictDiag (π i) c).rank := by
        rw [← restrictDiag_sum, h, restrictDiag_crossing]
    _ ≤ ∑ i ∈ s, (restrictDiag (π i) c).rank := matrix_rank_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => rank_restrictDiag_le_min _ _

/-- **系3.2（定量形）.** 全ての部品が、どちらか一方の切断で階数 ≤ R なら N ≤ |I|·R。
ブロック長 m（N = 2^m）で |I| ≤ 2^{o(m)} かつ R = 2^{x·m} なら x ≥ 1 − o(1)：
(2,0)・(0,2) の理想部品の族（x = 0）も、4.6節の族 {(2,x),(x,2)}（0 < x < 1）も存在しない。 -/
theorem card_le_card_mul_of_min_rank_le {ι : Type*} (s : Finset ι)
    (π : ι → α → α → α → α → K) (h : ∑ i ∈ s, π i = crossing K α) (c : α) (R : ℕ)
    (hR : ∀ i ∈ s, min (rowFlat (π i)).rank (colFlat (π i)).rank ≤ R) :
    Fintype.card α ≤ s.card * R := by
  calc Fintype.card α ≤ ∑ i ∈ s, min (rowFlat (π i)).rank (colFlat (π i)).rank :=
        card_le_sum_min_rank s π h c
    _ ≤ ∑ _i ∈ s, R := Finset.sum_le_sum hR
    _ = s.card * R := by simp

/-- 純粋な理想部品（各部品がどちらかの切断で階数 1 以下）なら、部品は N 個以上必要。 -/
theorem card_le_card_of_pure_pieces {ι : Type*} (s : Finset ι)
    (π : ι → α → α → α → α → K) (h : ∑ i ∈ s, π i = crossing K α) (c : α)
    (hpure : ∀ i ∈ s, (rowFlat (π i)).rank ≤ 1 ∨ (colFlat (π i)).rank ≤ 1) :
    Fintype.card α ≤ s.card := by
  have := card_le_card_mul_of_min_rank_le s π h c 1 fun i hi =>
    (hpure i hi).elim (fun h1 => (min_le_left _ _).trans h1) (fun h2 => (min_le_right _ _).trans h2)
  simpa using this

/-! ## N = 2 では純粋な2部品の族が実在する（ブロック長 m → ∞ が本質的であることの例）

A = [x ≠ u][y ≠ v] は列の切断で階数 1、crossing − A = s(x,y)·s(u,v)（s(a,b) = [a=b]·(−1)^a）は
行の切断で階数 1。これを 1 ビットずつのブロックに使うと λ ビットで 2^λ 項になり、
(L2) の |I| ≤ 2^{o(m)} に反する。 -/

/-- 列の切断で積の形の部品 A。 -/
def pieceCol : Bool → Bool → Bool → Bool → ℚ :=
  fun x y u v => (if x ≠ u then 1 else 0) * (if y ≠ v then 1 else 0)

/-- s(a,b) = [a = b]·(−1)^a。 -/
def sgnDiag : Bool → Bool → ℚ := fun a b => if a = b then (if a then -1 else 1) else 0

/-- 行の切断で積の形の部品 crossing − A。 -/
def pieceRow : Bool → Bool → Bool → Bool → ℚ := fun x y u v => sgnDiag x y * sgnDiag u v

theorem crossing_bool_eq : crossing ℚ Bool = pieceCol + pieceRow := by
  funext x y u v
  cases x <;> cases y <;> cases u <;> cases v <;>
    simp [crossing, pieceCol, pieceRow, sgnDiag]

theorem colFlat_pieceCol :
    colFlat pieceCol = Matrix.vecMulVec (fun p : Bool × Bool => if p.1 ≠ p.2 then (1 : ℚ) else 0)
      (fun q : Bool × Bool => if q.1 ≠ q.2 then (1 : ℚ) else 0) := by
  ext p q; simp [colFlat, pieceCol, Matrix.vecMulVec_apply]

theorem rowFlat_pieceRow :
    rowFlat pieceRow = Matrix.vecMulVec (fun p : Bool × Bool => sgnDiag p.1 p.2)
      (fun q : Bool × Bool => sgnDiag q.1 q.2) := by
  ext p q; simp [rowFlat, pieceRow, Matrix.vecMulVec_apply]

theorem rank_colFlat_pieceCol_le : (colFlat pieceCol).rank ≤ 1 := by
  rw [colFlat_pieceCol]; exact rank_vecMulVec_le _ _

theorem rank_rowFlat_pieceRow_le : (rowFlat pieceRow).rank ≤ 1 := by
  rw [rowFlat_pieceRow]; exact rank_vecMulVec_le _ _

end IdealPieces
