import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# Polynomial Closure and Complexity Upper Bound for 2-SAT Real-Space RG

In real-space renormalization group (decimation) for Boolean satisfiability, eliminating a
variable `v` corresponds to Davis-Putnam resolution: combining positive clauses `(v ∨ P)`
with negative clauses `(¬v ∨ Q)` into effective clauses `(P ∨ Q)` free of `v`.

When clauses and CNF formulas are represented as deduplicated finite sets (`Finset`),
2-SAT exhibits exact renormalization closure and polynomial state-space complexity:
1. **Equisatisfiability** (`decimateVar_equisatisfiable`, `decimateList_equisatisfiable`):
   eliminating any variable or sequence of variables preserves satisfiability.
2. **2-SAT width closure** (`decimateVar_is2SAT`, `decimateList_is2SAT`):
   if every clause has width at most `2`, every decimated formula remains a 2-SAT formula.
3. **Combinatorial state-space bound** (`card_all2Clauses`, `card_all2Clauses_le`):
   the total number of distinct clauses of width at most `2` over `n` variables is exactly
   `1 + 2 * n + (2 * n).choose 2`, which is bounded above by `(2 * n + 1) ^ 2`.
4. **Polynomial RG-flow complexity bound** (`decimateList_card_le`):
   along any variable-elimination sequence `vs`, every intermediate effective formula has
   at most `(2 * n + 1) ^ 2` clauses, keeping the entire 2-SAT decimation flow closed
   within `O(n²)` space and polynomial time.
-/

namespace Mathmatica.TwoSATPoly

/-! ## Deduplicated Finset Model of CNF-SAT -/

/-- A Boolean assignment to `n` variables. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- A literal over `n` variables: a variable index paired with its polarity
(`true` for `x_i`, `false` for `¬x_i`). -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- A deduplicated clause, represented as a finite set of literals. -/
abbrev FClause (n : ℕ) := Finset (Lit n)

/-- A deduplicated CNF formula, represented as a finite set of clauses. -/
abbrev FCNF (n : ℕ) := Finset (FClause n)

/-- The total number of literals over `n` variables is `2 * n`. -/
theorem card_lit (n : ℕ) : Fintype.card (Lit n) = 2 * n := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]

/-- Assignment `σ` satisfies clause `c` if at least one literal in `c` evaluates to `true`. -/
def SatisfiesClause {n : ℕ} (σ : Assignment n) (c : FClause n) : Prop :=
  ∃ l ∈ c, σ l.1 = l.2

/-- Assignment `σ` satisfies CNF formula `φ` if it satisfies every clause in `φ`. -/
def Satisfies {n : ℕ} (φ : FCNF n) (σ : Assignment n) : Prop :=
  ∀ c ∈ φ, SatisfiesClause σ c

/-- A CNF formula `φ` is satisfiable if there exists an assignment satisfying it. -/
def Satisfiable {n : ℕ} (φ : FCNF n) : Prop :=
  ∃ σ : Assignment n, Satisfies φ σ

/-- Update assignment `σ` at variable `v` to Boolean value `b`. -/
def updateAssign {n : ℕ} (σ : Assignment n) (v : Fin n) (b : Bool) : Assignment n :=
  fun i => if i = v then b else σ i

/-! ## Deduplicated Davis-Putnam Real-Space RG Operator -/

/-- Remove all literals mentioning variable `v` from clause `c`. -/
def stripVar {n : ℕ} (v : Fin n) (c : FClause n) : FClause n :=
  c.filter (fun l => l.1 ≠ v)

/-- Clauses in `φ` that do not contain variable `v` in either polarity. -/
def restClauses {n : ℕ} (v : Fin n) (φ : FCNF n) : FCNF n :=
  φ.filter (fun c => (v, true) ∉ c ∧ (v, false) ∉ c)

/-- Stripped remainders of clauses containing `(v, true)` and not `(v, false)`. -/
def posClauses {n : ℕ} (v : Fin n) (φ : FCNF n) : FCNF n :=
  (φ.filter (fun c => (v, true) ∈ c ∧ (v, false) ∉ c)).image (stripVar v)

/-- Stripped remainders of clauses containing `(v, false)` and not `(v, true)`. -/
def negClauses {n : ℕ} (v : Fin n) (φ : FCNF n) : FCNF n :=
  (φ.filter (fun c => (v, true) ∉ c ∧ (v, false) ∈ c)).image (stripVar v)

/-- All pairwise resolvents obtained by merging stripped positive and negative clauses. -/
def resolvents {n : ℕ} (v : Fin n) (φ : FCNF n) : FCNF n :=
  (posClauses v φ).biUnion (fun p => (negClauses v φ).image (fun q => p ∪ q))

/-- Deduplicated Davis-Putnam real-space renormalization operator eliminating variable `v`. -/
def decimateVar {n : ℕ} (v : Fin n) (φ : FCNF n) : FCNF n :=
  restClauses v φ ∪ resolvents v φ

/-- Sequential real-space renormalization eliminating a list of variables `vs`. -/
def decimateList {n : ℕ} : List (Fin n) → FCNF n → FCNF n
  | [], φ => φ
  | v :: vs, φ => decimateList vs (decimateVar v φ)

/-! ## Theorem 1: Equisatisfiability of `decimateVar` and `decimateList` -/

private lemma satisfiesClause_updateAssign_of_no_var {n : ℕ} {c : FClause n} {v : Fin n}
    (hno : ∀ l ∈ c, l.1 ≠ v) {σ : Assignment n} {b : Bool} :
    SatisfiesClause (updateAssign σ v b) c ↔ SatisfiesClause σ c := by
  constructor
  · rintro ⟨l, hl, hsat⟩
    refine ⟨l, hl, ?_⟩
    simpa [updateAssign, hno l hl] using hsat
  · rintro ⟨l, hl, hsat⟩
    refine ⟨l, hl, ?_⟩
    simpa [updateAssign, hno l hl] using hsat

private lemma satisfiesClause_of_stripVar {n : ℕ} {c : FClause n} {v : Fin n}
    {σ : Assignment n} (h : SatisfiesClause σ (stripVar v c)) :
    SatisfiesClause σ c := by
  rcases h with ⟨l, hl, hsat⟩
  exact ⟨l, (Finset.mem_filter.mp hl).1, hsat⟩

private lemma satisfiesClause_stripVar_of_not_mem {n : ℕ} {c : FClause n} {v : Fin n}
    {σ : Assignment n} (hc : SatisfiesClause σ c) (hno : (v, σ v) ∉ c) :
    SatisfiesClause σ (stripVar v c) := by
  rcases hc with ⟨⟨u, b⟩, hl, hsat⟩
  refine ⟨(u, b), Finset.mem_filter.mpr ⟨hl, ?_⟩, hsat⟩
  intro huv
  subst huv
  simp only at hsat
  rw [← hsat] at hl
  exact hno hl

private lemma no_var_of_not_mem {n : ℕ} {c : FClause n} {v : Fin n}
    (ht : (v, true) ∉ c) (hf : (v, false) ∉ c) :
    ∀ l ∈ c, l.1 ≠ v := by
  rintro ⟨u, b⟩ hl huv
  subst huv
  cases b
  · exact hf hl
  · exact ht hl

private lemma no_var_stripVar {n : ℕ} (v : Fin n) (c : FClause n) :
    ∀ l ∈ stripVar v c, l.1 ≠ v := by
  intro l hl
  exact (Finset.mem_filter.mp hl).2

/-- Soundness of `decimateVar`: any satisfying assignment of `φ` satisfies `decimateVar v φ`. -/
theorem decimateVar_sound {n : ℕ} (v : Fin n) {φ : FCNF n} {σ : Assignment n}
    (hSat : Satisfies φ σ) :
    Satisfies (decimateVar v φ) σ := by
  intro c hc
  rw [decimateVar, Finset.mem_union] at hc
  rcases hc with hrest | hres
  · exact hSat c (Finset.mem_filter.mp hrest).1
  · rw [resolvents, Finset.mem_biUnion] at hres
    rcases hres with ⟨p, hp, hqmem⟩
    rw [Finset.mem_image] at hqmem
    rcases hqmem with ⟨q, hq, rfl⟩
    rw [posClauses, Finset.mem_image] at hp
    rcases hp with ⟨c1, hc1, rfl⟩
    rw [Finset.mem_filter] at hc1
    rw [negClauses, Finset.mem_image] at hq
    rcases hq with ⟨c2, hc2, rfl⟩
    rw [Finset.mem_filter] at hc2
    cases hv : σ v
    · have h1 : SatisfiesClause σ (stripVar v c1) := by
        apply satisfiesClause_stripVar_of_not_mem (hSat c1 hc1.1)
        simpa [hv] using hc1.2.2
      rcases h1 with ⟨l, hl, hsat⟩
      exact ⟨l, Finset.mem_union_left _ hl, hsat⟩
    · have h2 : SatisfiesClause σ (stripVar v c2) := by
        apply satisfiesClause_stripVar_of_not_mem (hSat c2 hc2.1)
        simpa [hv] using hc2.2.1
      rcases h2 with ⟨l, hl, hsat⟩
      exact ⟨l, Finset.mem_union_right _ hl, hsat⟩

/-- Completeness (lifting) of `decimateVar`: any satisfying assignment of `decimateVar v φ`
can be lifted to a satisfying assignment of `φ` by choosing a value for `v`. -/
theorem decimateVar_complete {n : ℕ} (v : Fin n) {φ : FCNF n} {σ : Assignment n}
    (hSat : Satisfies (decimateVar v φ) σ) :
    Satisfiable φ := by
  by_cases hPos : ∀ p ∈ posClauses v φ, SatisfiesClause σ p
  · refine ⟨updateAssign σ v false, ?_⟩
    intro c hc
    by_cases hf : (v, false) ∈ c
    · exact ⟨(v, false), hf, by simp [updateAssign]⟩
    · by_cases ht : (v, true) ∈ c
      · have hmem : stripVar v c ∈ posClauses v φ :=
          Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, ht, hf⟩, rfl⟩
        apply satisfiesClause_of_stripVar (v := v)
        rw [satisfiesClause_updateAssign_of_no_var (no_var_stripVar v c)]
        exact hPos _ hmem
      · have hmem : c ∈ restClauses v φ := Finset.mem_filter.mpr ⟨hc, ht, hf⟩
        rw [satisfiesClause_updateAssign_of_no_var (no_var_of_not_mem ht hf)]
        exact hSat c (Finset.mem_union_left _ hmem)
  · push Not at hPos
    rcases hPos with ⟨p, hpMem, hpUnsat⟩
    have hNeg : ∀ q ∈ negClauses v φ, SatisfiesClause σ q := by
      intro q hqMem
      have hresMem : p ∪ q ∈ decimateVar v φ := by
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨p, hpMem, Finset.mem_image.mpr ⟨q, hqMem, rfl⟩⟩
      rcases hSat (p ∪ q) hresMem with ⟨l, hl, hsat⟩
      rcases Finset.mem_union.mp hl with hlp | hlq
      · exact False.elim (hpUnsat ⟨l, hlp, hsat⟩)
      · exact ⟨l, hlq, hsat⟩
    refine ⟨updateAssign σ v true, ?_⟩
    intro c hc
    by_cases ht : (v, true) ∈ c
    · exact ⟨(v, true), ht, by simp [updateAssign]⟩
    · by_cases hf : (v, false) ∈ c
      · have hmem : stripVar v c ∈ negClauses v φ :=
          Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, ht, hf⟩, rfl⟩
        apply satisfiesClause_of_stripVar (v := v)
        rw [satisfiesClause_updateAssign_of_no_var (no_var_stripVar v c)]
        exact hNeg _ hmem
      · have hmem : c ∈ restClauses v φ := Finset.mem_filter.mpr ⟨hc, ht, hf⟩
        rw [satisfiesClause_updateAssign_of_no_var (no_var_of_not_mem ht hf)]
        exact hSat c (Finset.mem_union_left _ hmem)

/-- **Theorem 1 (Equisatisfiability of `decimateVar`)**:
eliminating variable `v` preserves satisfiability exactly. -/
theorem decimateVar_equisatisfiable {n : ℕ} (v : Fin n) (φ : FCNF n) :
    Satisfiable (decimateVar v φ) ↔ Satisfiable φ :=
  ⟨fun ⟨_, hSat⟩ => decimateVar_complete v hSat,
   fun ⟨σ, hSat⟩ => ⟨σ, decimateVar_sound v hSat⟩⟩

/-- Sequential elimination of any list of variables preserves satisfiability. -/
theorem decimateList_equisatisfiable {n : ℕ} (vs : List (Fin n)) (φ : FCNF n) :
    Satisfiable (decimateList vs φ) ↔ Satisfiable φ := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih =>
    simp only [decimateList]
    rw [ih (decimateVar v φ), decimateVar_equisatisfiable v φ]

/-! ## Theorem 2: 2-SAT Width Closure under Real-Space RG -/

/-- A CNF formula is a 2-SAT formula if every clause has cardinality at most `2`. -/
def Is2SAT {n : ℕ} (φ : FCNF n) : Prop :=
  ∀ c ∈ φ, c.card ≤ 2

private lemma card_stripVar_le_pred {n : ℕ} {v : Fin n} {c : FClause n} {b : Bool}
    (hmem : (v, b) ∈ c) :
    (stripVar v c).card ≤ c.card - 1 := by
  have hsub : stripVar v c ⊆ c.erase (v, b) := by
    intro l hl
    rcases Finset.mem_filter.mp hl with ⟨hlc, hne⟩
    refine Finset.mem_erase.mpr ⟨?_, hlc⟩
    intro heq
    exact hne (congrArg Prod.fst heq)
  calc
    (stripVar v c).card ≤ (c.erase (v, b)).card := Finset.card_le_card hsub
    _ = c.card - 1 := Finset.card_erase_of_mem hmem

/-- **Theorem 2 (2-SAT Width Closure)**:
applying `decimateVar` to a 2-SAT formula produces a 2-SAT formula. -/
theorem decimateVar_is2SAT {n : ℕ} (v : Fin n) {φ : FCNF n} (h2 : Is2SAT φ) :
    Is2SAT (decimateVar v φ) := by
  intro c hc
  rw [decimateVar, Finset.mem_union] at hc
  rcases hc with hrest | hres
  · exact h2 c (Finset.mem_filter.mp hrest).1
  · rw [resolvents, Finset.mem_biUnion] at hres
    rcases hres with ⟨p, hp, hqmem⟩
    rw [Finset.mem_image] at hqmem
    rcases hqmem with ⟨q, hq, rfl⟩
    rw [posClauses, Finset.mem_image] at hp
    rcases hp with ⟨c1, hc1, rfl⟩
    rw [Finset.mem_filter] at hc1
    rw [negClauses, Finset.mem_image] at hq
    rcases hq with ⟨c2, hc2, rfl⟩
    rw [Finset.mem_filter] at hc2
    have hp1 : (stripVar v c1).card ≤ 1 := by
      have hle := card_stripVar_le_pred hc1.2.1
      have hc1_le := h2 c1 hc1.1
      omega
    have hq1 : (stripVar v c2).card ≤ 1 := by
      have hle := card_stripVar_le_pred hc2.2.2
      have hc2_le := h2 c2 hc2.1
      omega
    calc
      (stripVar v c1 ∪ stripVar v c2).card
          ≤ (stripVar v c1).card + (stripVar v c2).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add hp1 hq1
      _ = 2 := rfl

/-- Sequential elimination of any list of variables preserves the 2-SAT property. -/
theorem decimateList_is2SAT {n : ℕ} (vs : List (Fin n)) {φ : FCNF n} (h2 : Is2SAT φ) :
    Is2SAT (decimateList vs φ) := by
  induction vs generalizing φ with
  | nil => exact h2
  | cons v vs ih =>
    simp only [decimateList]
    exact ih (decimateVar_is2SAT v h2)

/-! ## Theorem 3: Polynomial Upper Bound on the 2-SAT Clause State Space -/

/-- The finite set of all clauses of width at most `2` over `n` variables, constructed as
the disjoint union of `powersetCard 0`, `powersetCard 1`, and `powersetCard 2`. -/
def all2Clauses (n : ℕ) : Finset (FClause n) :=
  (Finset.univ : Finset (Lit n)).powersetCard 0 ∪
  (Finset.univ : Finset (Lit n)).powersetCard 1 ∪
  (Finset.univ : Finset (Lit n)).powersetCard 2

/-- Membership characterization: a clause lies in `all2Clauses n` iff its width is at most `2`. -/
theorem mem_all2Clauses_iff {n : ℕ} (c : FClause n) :
    c ∈ all2Clauses n ↔ c.card ≤ 2 := by
  simp only [all2Clauses, Finset.mem_union, Finset.mem_powersetCard, Finset.subset_univ,
    true_and]
  omega

/-- Exact combinatorial cardinality of the 2-SAT clause space:
`|(all2Clauses n)| = 1 + 2n + C(2n, 2)`. -/
theorem card_all2Clauses (n : ℕ) :
    (all2Clauses n).card = 1 + 2 * n + (2 * n).choose 2 := by
  set U : Finset (Lit n) := Finset.univ
  have hU : U.card = 2 * n := by
    simpa [U] using card_lit n
  have h01 : Disjoint (U.powersetCard 0) (U.powersetCard 1) := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    have h0 := (Finset.mem_powersetCard.mp hc0).2
    have h1 := (Finset.mem_powersetCard.mp hc1).2
    omega
  have h01_2 : Disjoint (U.powersetCard 0 ∪ U.powersetCard 1) (U.powersetCard 2) := by
    rw [Finset.disjoint_left]
    intro c hc01 hc2
    have h2 := (Finset.mem_powersetCard.mp hc2).2
    rcases Finset.mem_union.mp hc01 with hc0 | hc1
    · have h0 := (Finset.mem_powersetCard.mp hc0).2
      omega
    · have h1 := (Finset.mem_powersetCard.mp hc1).2
      omega
  unfold all2Clauses
  rw [Finset.card_union_of_disjoint h01_2, Finset.card_union_of_disjoint h01,
    Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_powersetCard,
    hU, Nat.choose_zero_right, Nat.choose_one_right]

/-- **Theorem 3 (Polynomial State-Space Bound for 2-SAT)**:
the total number of distinct 2-SAT clauses over `n` variables is at most `(2 * n + 1) ^ 2`. -/
theorem card_all2Clauses_le (n : ℕ) :
    (all2Clauses n).card ≤ (2 * n + 1) ^ 2 := by
  rw [card_all2Clauses]
  have hchoose : (2 * n).choose 2 ≤ (2 * n) ^ 2 := by
    rw [Nat.choose_two_right, sq]
    calc
      2 * n * (2 * n - 1) / 2 ≤ 2 * n * (2 * n - 1) := Nat.div_le_self _ _
      _ ≤ 2 * n * (2 * n) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hexpand : 1 + 2 * n + (2 * n) ^ 2 ≤ (2 * n + 1) ^ 2 := by
    have h : (2 * n + 1) ^ 2 = 1 + 2 * n + (2 * n) ^ 2 + 2 * n := by ring
    omega
  omega

/-! ## Theorem 4: Polynomial Complexity Bound along the 2-SAT RG Flow -/

/-- Any 2-SAT formula is a subset of `all2Clauses n`. -/
theorem is2SAT_subset_all2Clauses {n : ℕ} {φ : FCNF n} (h2 : Is2SAT φ) :
    φ ⊆ all2Clauses n := by
  intro c hc
  exact (mem_all2Clauses_iff c).mpr (h2 c hc)

/-- Exact combinatorial upper bound on the number of clauses in any 2-SAT formula. -/
theorem is2SAT_card_le_exact {n : ℕ} {φ : FCNF n} (h2 : Is2SAT φ) :
    φ.card ≤ 1 + 2 * n + (2 * n).choose 2 := by
  calc
    φ.card ≤ (all2Clauses n).card := Finset.card_le_card (is2SAT_subset_all2Clauses h2)
    _ = 1 + 2 * n + (2 * n).choose 2 := card_all2Clauses n

/-- Polynomial upper bound on the number of clauses in any 2-SAT formula. -/
theorem is2SAT_card_le {n : ℕ} {φ : FCNF n} (h2 : Is2SAT φ) :
    φ.card ≤ (2 * n + 1) ^ 2 := by
  calc
    φ.card ≤ (all2Clauses n).card := Finset.card_le_card (is2SAT_subset_all2Clauses h2)
    _ ≤ (2 * n + 1) ^ 2 := card_all2Clauses_le n

/-- **Theorem 4 (Polynomial RG-Flow Complexity Bound for 2-SAT)**:
if `φ` is a 2-SAT formula, then after eliminating any sequence `vs` of variables via
real-space renormalization, the effective formula has at most `(2 * n + 1) ^ 2` clauses. -/
theorem decimateList_card_le {n : ℕ} (vs : List (Fin n)) {φ : FCNF n} (h2 : Is2SAT φ) :
    (decimateList vs φ).card ≤ (2 * n + 1) ^ 2 :=
  is2SAT_card_le (decimateList_is2SAT vs h2)

/-- Sharper combinatorial bound along the entire 2-SAT real-space RG flow:
every intermediate effective formula has at most `1 + 2n + C(2n, 2)` clauses. -/
theorem decimateList_card_le_exact {n : ℕ} (vs : List (Fin n)) {φ : FCNF n} (h2 : Is2SAT φ) :
    (decimateList vs φ).card ≤ 1 + 2 * n + (2 * n).choose 2 :=
  is2SAT_card_le_exact (decimateList_is2SAT vs h2)

end Mathmatica.TwoSATPoly
