import Mathmatica.SATSymmetry
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# 猜想桥 IV：解空间重叠间隙性质（OGP）与团簇分解定理（Lean 4 + Mathlib）

本模块形式化随机 $k$-SAT / 组合优化解空间几何中的**重叠间隙性质（Overlap Gap Property, OGP）**
及其蕴含的**精确团簇分解（Clustering / Shattering）**：

1. **汉明距离（Hamming Distance）** `hammingDist` 及其度量公理：
   - 自反性 `hammingDist_self`
   - 同一性 `hammingDist_eq_zero`
   - 对称性 `hammingDist_comm`
   - 三角不等式 `hammingDist_triangle`
   - 变量置换群作用的等距性 `hammingDist_actAssignment`
2. **重叠间隙性质（OGP）** `HasOGP`：
   解空间中任意两个满足赋值要么足够接近（距离 `≤ ν₁`），要么被间隙严格隔开（距离 `≥ ν₂`）。
3. **团簇分解定理（Clustering Theorem）** `ogp_clustering_equivalence`：
   若公式 `φ` 满足 `HasOGP φ ν₁ ν₂` 且间隙宽度满足 `2 * ν₁ < ν₂`，
   则「处于同一团簇」关系 `SameCluster ν₁` 在解空间 `{ σ : Assignment n // Satisfies φ σ }`
   上构成严格的**等价关系（`Equivalence`）**，从而将解空间无交地碎裂为彼此相距至少 `ν₂` 的孤立团簇，
   并且公式的任意对称置换均将团簇等距地映射到团簇。
-/

namespace Mathmatica.OverlapGap

open Mathmatica.SAT

/-! ## 1. 汉明距离及其度量公理 -/

/-- 两个 `n` 元布尔赋值之间的汉明距离：取值不同的变量坐标个数。 -/
def hammingDist {n : ℕ} (σ τ : Assignment n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card

/-- 自反性：任意赋值与自身的汉明距离为 `0`。 -/
theorem hammingDist_self {n : ℕ} (σ : Assignment n) :
    hammingDist σ σ = 0 := by
  simp [hammingDist]

/-- 同一性：汉明距离为 `0` 当且仅当两个赋值相等。 -/
theorem hammingDist_eq_zero {n : ℕ} {σ τ : Assignment n} :
    hammingDist σ τ = 0 ↔ σ = τ := by
  unfold hammingDist
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    by_contra hne
    exact h (Finset.mem_univ i) hne
  · rintro rfl i _ hne
    exact hne rfl

/-- 对称性：汉明距离满足交换律。 -/
theorem hammingDist_comm {n : ℕ} (σ τ : Assignment n) :
    hammingDist σ τ = hammingDist τ σ := by
  unfold hammingDist
  congr 1
  ext i
  simp [ne_comm]

/-- 三角不等式：`d(σ, ρ) ≤ d(σ, τ) + d(τ, ρ)`。 -/
theorem hammingDist_triangle {n : ℕ} (σ τ ρ : Assignment n) :
    hammingDist σ ρ ≤ hammingDist σ τ + hammingDist τ ρ := by
  unfold hammingDist
  calc
    (Finset.univ.filter (fun i : Fin n => σ i ≠ ρ i)).card
      ≤ ((Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)) ∪
          (Finset.univ.filter (fun i : Fin n => τ i ≠ ρ i))).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_cases h : σ i = τ i
        · right
          intro h'
          exact hi (h.trans h')
        · left
          exact h
    _ ≤ (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card +
        (Finset.univ.filter (fun i : Fin n => τ i ≠ ρ i)).card :=
      Finset.card_union_le _ _

/-- **群作用等距性**：变量置换 `π ∈ S_n` 严格保持任意两个赋值之间的汉明距离。 -/
theorem hammingDist_actAssignment {n : ℕ} (π : Equiv.Perm (Fin n)) (σ τ : Assignment n) :
    hammingDist (actAssignment π σ) (actAssignment π τ) = hammingDist σ τ := by
  unfold hammingDist
  have hEq :
      Finset.univ.filter (fun i : Fin n => actAssignment π σ i ≠ actAssignment π τ i) =
      (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).map π.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    simp only [actAssignment]
    constructor
    · intro h
      exact ⟨π⁻¹ i, h, by simp⟩
    · rintro ⟨j, hj, hji⟩
      have hj' : j = π⁻¹ i := by
        rw [← hji]
        simp
      rw [← hj']
      exact hj
  rw [hEq, Finset.card_map]

/-! ## 2. 重叠间隙性质（Overlap Gap Property, OGP） -/

/-- **重叠间隙性质（OGP）**：
存在阈值 `ν₁ < ν₂`，使得公式 `φ` 的任意两个满足赋值 `σ, τ` 之间的汉明距离
要么不大于 `ν₁`（同一团簇内），要么不小于 `ν₂`（处于不同团簇），
中间区间 `(ν₁, ν₂)` 严禁出现任何解对。 -/
def HasOGP {n : ℕ} (φ : CNF n) (ν₁ ν₂ : ℕ) : Prop :=
  ν₁ < ν₂ ∧
    ∀ σ τ : Assignment n, Satisfies φ σ → Satisfies φ τ →
      hammingDist σ τ ≤ ν₁ ∨ ν₂ ≤ hammingDist σ τ

/-! ## 3. 团簇分解定理（Clustering Theorem）与对称等距性 -/

/-- 公式 `φ` 的解空间子类型。 -/
abbrev Solution {n : ℕ} (φ : CNF n) := { σ : Assignment n // Satisfies φ σ }

/-- 同团簇关系：两个赋值之间的汉明距离不超过团簇直径阈值 `ν₁`。 -/
def SameCluster {n : ℕ} (ν₁ : ℕ) (σ τ : Assignment n) : Prop :=
  hammingDist σ τ ≤ ν₁

/-- **核心定理（OGP 蕴含精确团簇分解 / Clustering Theorem）**：
若公式 `φ` 满足 `HasOGP φ ν₁ ν₂` 且重叠间隙足够宽（`2 * ν₁ < ν₂`），
则 `SameCluster ν₁` 在解空间 `{ σ : Assignment n // Satisfies φ σ }` 上构成严格的**等价关系**。

证明关键：三角不等式给出 `d(σ, ρ) ≤ d(σ, τ) + d(τ, ρ) ≤ 2 * ν₁ < ν₂`，
结合 OGP 的二分性立即排除了 `ν₂ ≤ d(σ, ρ)` 的可能，从而迫使 `d(σ, ρ) ≤ ν₁`（传递性成立）。 -/
theorem ogp_clustering_equivalence {n : ℕ} {φ : CNF n} {ν₁ ν₂ : ℕ}
    (hOGP : HasOGP φ ν₁ ν₂) (hGap : 2 * ν₁ < ν₂) :
    Equivalence (fun (σ τ : { σ : Assignment n // Satisfies φ σ }) =>
      SameCluster ν₁ σ.1 τ.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    unfold SameCluster
    rw [hammingDist_self]
    exact Nat.zero_le ν₁
  · intro σ τ h
    unfold SameCluster at h ⊢
    rw [hammingDist_comm]
    exact h
  · intro σ τ ρ hστ hτρ
    unfold SameCluster at hστ hτρ ⊢
    have hTri : hammingDist σ.1 ρ.1 ≤ hammingDist σ.1 τ.1 + hammingDist τ.1 ρ.1 :=
      hammingDist_triangle σ.1 τ.1 ρ.1
    rcases hOGP.2 σ.1 ρ.1 σ.2 ρ.2 with hClose | hFar
    · exact hClose
    · omega

/-- 由 OGP 与宽间隙诱导的解空间 `Setoid`，其商空间即为互不相交的孤立团簇集合。 -/
def clusterSetoid {n : ℕ} {φ : CNF n} {ν₁ ν₂ : ℕ}
    (hOGP : HasOGP φ ν₁ ν₂) (hGap : 2 * ν₁ < ν₂) :
    Setoid (Solution φ) where
  r σ τ := SameCluster ν₁ σ.1 τ.1
  iseqv := ogp_clustering_equivalence hOGP hGap

/-- **团簇严格分离定理**：不同团簇中的任意两个解之间的汉明距离至少为 `ν₂`。 -/
theorem ogp_distinct_clusters_separated {n : ℕ} {φ : CNF n} {ν₁ ν₂ : ℕ}
    (hOGP : HasOGP φ ν₁ ν₂) {σ τ : Assignment n}
    (hσ : Satisfies φ σ) (hτ : Satisfies φ τ)
    (hDiff : ¬ SameCluster ν₁ σ τ) :
    ν₂ ≤ hammingDist σ τ := by
  rcases hOGP.2 σ τ hσ hτ with hClose | hFar
  · exact absurd hClose hDiff
  · exact hFar

/-- 变量置换保持同团簇关系。 -/
theorem sameCluster_actAssignment {n : ℕ} (π : Equiv.Perm (Fin n)) (ν₁ : ℕ)
    (σ τ : Assignment n) :
    SameCluster ν₁ (actAssignment π σ) (actAssignment π τ) ↔ SameCluster ν₁ σ τ := by
  unfold SameCluster
  rw [hammingDist_actAssignment]

/-- 公式的对称变换在解空间 `Solution φ` 上诱导的映射。 -/
def actSolution {n : ℕ} {φ : CNF n} {π : Equiv.Perm (Fin n)}
    (hSym : actCNF π φ = φ) (σ : Solution φ) : Solution φ :=
  ⟨actAssignment π σ.1, satisfies_of_symmetry hSym σ.2⟩

/-- **对称性保持团簇分解（等距映射定理）**：
若 `π` 是公式 `φ` 的对称变换（`actCNF π φ = φ`），则 `π` 将解空间等距映射到自身，
且严格保持团簇等价关系（将团簇等距映射到团簇）。 -/
theorem symmetry_maps_clusters_isometrically {n : ℕ} {φ : CNF n} {π : Equiv.Perm (Fin n)}
    (hSym : actCNF π φ = φ) (ν₁ : ℕ) (σ τ : Solution φ) :
    hammingDist (actSolution hSym σ).1 (actSolution hSym τ).1 = hammingDist σ.1 τ.1 ∧
    (SameCluster ν₁ (actSolution hSym σ).1 (actSolution hSym τ).1 ↔
      SameCluster ν₁ σ.1 τ.1) :=
  ⟨hammingDist_actAssignment π σ.1 τ.1, sameCluster_actAssignment π ν₁ σ.1 τ.1⟩

end Mathmatica.OverlapGap
